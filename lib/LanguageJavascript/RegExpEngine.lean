/-
The regular expression engine of the three trees.

A regular expression literal is stored by the three trees as a
`RegExpLit` — the pattern between the slashes and the flags after the
closing one (`Language.JavaScript.Types`).  That type says how a literal is
*written*; it says nothing about what it *means*, and this project does not
try to say it on its own: everything about the pattern itself — parsing it,
compiling it, matching with it — is delegated to the
[`lean-regex`](https://github.com/pandaman64/lean-regex) library, whose
matching engines are proved correct against the semantics of regular
expressions.

This module is the bridge between the two:

* `RegExpLit.librarySource` is the pattern in the syntax the library reads
  (JavaScript writes the delimiter escaped, `\/`, which the library does not
  accept as an escape);
* `RegExpLit.ast?`, `RegExpLit.expr?` and `RegExpLit.compile?` parse and
  compile the pattern with the library, honouring the `i` and `s` flags;
* `RegExpCompiled` is a literal *together with* the library's parse tree of
  its pattern and a proof that it really is the parse tree of that pattern,
  so that the compiled `Regex`, and hence `test`, `find`, `replace`, … are
  total on it;
* `RegExpLit.compiled?` is the smart constructor.

### What is supported

The library's syntax is a subset of JavaScript's.  A pattern it cannot read
— a lookaround `(?=…)`, a named group `(?<n>…)`, a back reference `\1`, a
Unicode property `\p{…}` — makes every function here answer `none` rather
than answer wrongly.  Of the flags:

* `i` (`ignoreCase`) is passed to the library as a parse option, which case
  folds the literal characters of the pattern;
* `s` (`dotAll`) is applied to the parse tree, by replacing every `.` with
  the class of all characters — the library's `.` is JavaScript's `.`
  without the flag, every character but a line break;
* `d` (`hasIndices`) and `u`/`v` (`unicode`, `unicodeSets`) change nothing
  here: the library matches over `Char`, and the byte indices of a match are
  reported by every search;
* `g` (`global`) selects, in `RegExpCompiled.replaceJS` and
  `RegExpCompiled.matchJS`, between acting on the first match and acting on
  all of them.  The `lastIndex` of a JavaScript `RegExp` *object* is not
  modelled — that is what makes such an object impure — so `test` and
  `find` do not depend on it;
* `m` (`multiline`) and `y` (`sticky`) change what a *search* means: `^`
  and `$` become line anchors, and a sticky search must start where the
  previous one stopped.  Neither is expressible here, so a literal carrying
  one of them has no `RegExpCompiled` (`RegExpFlags.searchSupported` is
  false) and the matching functions answer `none`.
-/
import Regex
import LanguageJavascript.Types

namespace Language.JavaScript

open Regex.Syntax.Parser (Ast ParseOption ToRegexState parseAst)
open Regex.Data (Class Classes Expr)

namespace RegExpFlags

/-- The parse options the library needs for these flags: `i` case folds the
characters of the pattern. -/
def toParseOption (f : RegExpFlags) : ParseOption := { caseInsensitive := f.ignoreCase }

/-- Whether a *search* with these flags means what the library's search
means.  `m` makes `^` and `$` line anchors and `y` anchors the search at
`lastIndex`; neither is modelled, so a literal carrying one of them is not
compiled. -/
def searchSupported (f : RegExpFlags) : Bool := !f.multiline && !f.sticky

end RegExpFlags

/-! ## The pattern in the library's syntax -/

namespace RegExpLit

/-- Rewrite the escapes JavaScript spells differently from the library.

The only difference is the delimiter: a `/` inside a literal has to be
written `\/`, which the library rejects as an unknown escape, so it is
turned back into a plain `/` — inside a character class too, where it is
just as allowed and just as meaningless.  Every other escape is passed
through untouched, together with the backslash, so that `\\/` (an escaped
backslash followed by a slash) stays what it is.

The pattern is read by byte index and the result is built by pushing
characters onto it, so neither string becomes a list of characters.  `fuel`
bounds the number of characters left to read; the number of bytes left is
always enough, since every step consumes at least one byte. -/
def unescapeDelimiter (pat : String) : Nat → String.Pos.Raw → String → String
  | 0, _, acc => acc
  | fuel + 1, p, acc =>
      if pat.utf8ByteSize ≤ p.byteIdx then acc
      else
        let c := String.Pos.Raw.get pat p
        let q := String.Pos.Raw.next pat p
        if c == '\\' && q.byteIdx < pat.utf8ByteSize then
          let d := String.Pos.Raw.get pat q
          let r := String.Pos.Raw.next pat q
          if d == '/' then unescapeDelimiter pat fuel r (acc.push '/')
          else unescapeDelimiter pat fuel r ((acc.push '\\').push d)
        else unescapeDelimiter pat fuel q (acc.push c)

/-- The pattern of the literal, in the syntax the library reads. -/
def librarySource (r : RegExpLit) : String :=
  unescapeDelimiter r.source.val r.source.val.utf8ByteSize ⟨0⟩ ""

/-- The parse tree of `.`, once the `s` flag is taken into account: the
class of every character. -/
def anyCharAst : Ast :=
  .classes (Classes.atom (Class.range (Char.ofNat 0) (Char.ofNat Char.MAX_UNICODE)))

/-- Apply the `s` flag to a parse tree: with `dotAll`, a `.` matches a line
break too, which the library's `.` does not. -/
def applyDotAll : Ast → Ast
  | .dot => anyCharAst
  | .group a => .group (applyDotAll a)
  | .alternate a b => .alternate (applyDotAll a) (applyDotAll b)
  | .concat a b => .concat (applyDotAll a) (applyDotAll b)
  | .repeat min max greedy a => .repeat min max greedy (applyDotAll a)
  | a => a

/-- The parse tree the library gives the pattern, with the `s` flag applied;
`none` when the pattern uses syntax the library does not read. -/
def ast? (r : RegExpLit) : Option Ast :=
  match parseAst r.librarySource with
  | .ok a => some (if r.flags.dotAll then applyDotAll a else a)
  | .error _ => none

/-- Whether the library reads the pattern of the literal. -/
def patternSupported (r : RegExpLit) : Bool := r.ast?.isSome

end RegExpLit

/-! ## A literal the library understands -/

/-- A regular expression literal whose pattern the library reads, together
with that parse tree and the proof that it is the one the library's parser
returns.  Compiling and matching are therefore *total* on this type: no
`Option`, no `panic!`, no default pattern silently standing in for one that
could not be read.

The flags are restricted to those under which a search means what the
library's search means; see the header of this module. -/
structure RegExpCompiled where
  /-- The literal. -/
  lit : RegExpLit
  /-- Its pattern, as the library parses it, with the `s` flag applied. -/
  ast : Ast
  /-- `ast` is what the library's parser answers on the pattern. -/
  parses : lit.ast? = some ast
  /-- The flags are ones a search can honour. -/
  searchable : lit.flags.searchSupported = true

namespace RegExpCompiled

/-- The literal, if the library reads its pattern and its flags leave the
meaning of a search unchanged. -/
def of? (lit : RegExpLit) : Option RegExpCompiled :=
  if hf : lit.flags.searchSupported = true then
    match h : lit.ast? with
    | some a => some ⟨lit, a, h, hf⟩
    | none => none
  else none

/-- The regular expression of the library, as an `Expr`.  The pattern is
wrapped in a group, as the library's own `parse` does, so that group 0 is
the whole match. -/
def expr (c : RegExpCompiled) : Expr :=
  (Ast.toRegexAux (ToRegexState.mk 0 c.lit.flags.ignoreCase) (.group c.ast)).2

/-- The compiled regular expression: an NFA, and the proof that it is well
formed, built by the library. -/
def regex (c : RegExpCompiled) : Regex := Regex.fromExpr c.expr

/-- Whether the regular expression matches somewhere in `haystack`
(JavaScript's `RegExp.prototype.test`, without `lastIndex`). -/
def test (c : RegExpCompiled) (haystack : String) : Bool := c.regex.test haystack

/-- The first substring of `haystack` the regular expression matches. -/
def extract (c : RegExpCompiled) (haystack : String) : Option String :=
  c.regex.extract haystack

/-- Every substring of `haystack` the regular expression matches, left to
right and without overlap. -/
def extractAll (c : RegExpCompiled) (haystack : String) : Array String :=
  c.regex.extractAll haystack

/-- How many times the regular expression matches in `haystack`. -/
def count (c : RegExpCompiled) (haystack : String) : Nat := c.regex.count haystack

/-- `haystack` split at every match. -/
def split (c : RegExpCompiled) (haystack : String) : Array String :=
  (c.regex.split haystack).map (·.toString)

/-- `haystack` with the first match replaced by `replacement`. -/
def replaceFirst (c : RegExpCompiled) (haystack replacement : String) : String :=
  c.regex.replace haystack replacement

/-- `haystack` with every match replaced by `replacement`. -/
def replaceAll (c : RegExpCompiled) (haystack replacement : String) : String :=
  c.regex.replaceAll haystack replacement

/-- `String.prototype.replace` for this literal: with the `g` flag every
match is replaced, without it only the first one. -/
def replaceJS (c : RegExpCompiled) (haystack replacement : String) : String :=
  if c.lit.flags.global then c.replaceAll haystack replacement
  else c.replaceFirst haystack replacement

/-- `String.prototype.match` for this literal: with the `g` flag the list of
the matched substrings, without it the first match alone (`none` when there
is none). -/
def matchJS (c : RegExpCompiled) (haystack : String) : Option (Array String) :=
  if c.lit.flags.global then
    let all := c.extractAll haystack
    if all.isEmpty then none else some all
  else
    (c.extract haystack).map (fun s => #[s])

/-- The capture groups of the first match: group 0 is the whole match, and a
group which did not take part in the match is `none`. -/
def capture (c : RegExpCompiled) (haystack : String) : Option (Array (Option String)) :=
  (c.regex.capture haystack).map fun groups =>
    (Array.range (groups.buffer.size / 2)).map fun i =>
      (groups.get i).map (·.toString)

end RegExpCompiled

namespace RegExpLit

/-- The literal, compiled by the library; `none` when its pattern uses
syntax the library does not read, or its flags change what a search means
(`m`, `y`). -/
def compiled? (r : RegExpLit) : Option RegExpCompiled := RegExpCompiled.of? r

/-- The regular expression of the library the pattern denotes, ignoring the
flags which only matter to a search. -/
def expr? (r : RegExpLit) : Option Expr :=
  r.ast?.map fun a =>
    (Ast.toRegexAux (ToRegexState.mk 0 r.flags.ignoreCase) (.group a)).2

/-- The pattern, compiled to an NFA by the library. -/
def compile? (r : RegExpLit) : Option Regex := r.expr?.map Regex.fromExpr

/-- Whether the literal matches somewhere in `haystack`; `none` when the
library cannot answer for it. -/
def test? (r : RegExpLit) (haystack : String) : Option Bool :=
  (r.compiled?).map (·.test haystack)

/-- The first match of the literal in `haystack`; the outer `none` means
that the library cannot answer for this literal, the inner one that there is
no match. -/
def extract? (r : RegExpLit) (haystack : String) : Option (Option String) :=
  (r.compiled?).map (·.extract haystack)

/-- Every match of the literal in `haystack`; `none` when the library cannot
answer for it. -/
def extractAll? (r : RegExpLit) (haystack : String) : Option (Array String) :=
  (r.compiled?).map (·.extractAll haystack)

/-- `String.prototype.replace` with this literal; `none` when the library
cannot answer for it. -/
def replaceJS? (r : RegExpLit) (haystack replacement : String) : Option String :=
  (r.compiled?).map (·.replaceJS haystack replacement)

end RegExpLit

end Language.JavaScript
