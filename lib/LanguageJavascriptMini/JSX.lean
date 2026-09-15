import MiniAST.Syntax
import MiniAST.Options

/-!
# The layout of JSX

The parts of the JSX printer that work on documents alone: the way
prettier turns the children of an element into the parts of a `fill`, the
whitespace it has to write as `{" "}`, and the way it assembles an element
from its tags and its children.  The traversal of the tree itself is in
`MiniAST.Printer`, which is where the printer of an expression lives.

The algorithm is prettier's `printJsxElement`: the children are laid out
as a `fill`, the runs of whitespace between them that a line break would
swallow are written as `{" "}`, and an element that holds a tag, more than
one attribute or more than one substitution is always broken.
-/

namespace Language.JavaScript.MiniAST.Printer

open Language.JavaScript.Doc

variable [o : Options]

/-- The number of columns of one indentation step: prettier's
`tabWidth`. -/
private def jsxIndent : Nat := Options.tabWidth

private def tx (s : String) : Doc := .text s

/-! ## The parts of the children of an element -/

/-- One entry of the list prettier builds out of the children of an
element.  The entries alternate contents and separators; the separators
are the four kinds prettier uses, and a content is a document, `empty`
saying that it is the empty one it starts every gap with. -/
inductive JSXPart where
  /-- A content: a word of text, or a printed child. -/
  | content (empty : Bool) (d : Doc)
  /-- The separator between two words of the same run of text. -/
  | line
  /-- The separator that prints as nothing when the line does not break. -/
  | softline
  /-- The separator that always breaks. -/
  | hardline
  /-- A run of whitespace which a line break would swallow, and which is
  written `{" "}` when the line does break. -/
  | jsxWhitespace
deriving Inhabited

namespace JSXPart

/-- Whether the part is the empty content. -/
def isEmptyContent : JSXPart → Bool
  | .content e _ => e
  | _ => false

/-- Whether the part is a line of one of the three kinds, or the empty
content: the parts prettier trims from the ends of the list. -/
def isTrimmable : JSXPart → Bool
  | .content e _ => e
  | .line | .softline | .hardline => true
  | .jsxWhitespace => false

/-- Whether the part is a hard line. -/
def isHardline : JSXPart → Bool
  | .hardline => true
  | _ => false

/-- Whether the part is a soft line. -/
def isSoftline : JSXPart → Bool
  | .softline => true
  | _ => false

/-- Whether the part is a run of whitespace written `{" "}`. -/
def isJsxWhitespace : JSXPart → Bool
  | .jsxWhitespace => true
  | _ => false

end JSXPart

/-- The `{" "}` a run of whitespace is written as where the line breaks. -/
def rawJsxWhitespace : Doc := tx (if Options.singleQuote then "{' '}" else "{\" \"}")

/-- The document of a run of whitespace: a space while the line holds, and
`{" "}` followed by a line break when it does not. -/
def jsxWhitespaceDoc : Doc := .ifBreak (rawJsxWhitespace ++ .softline) (tx " ")

/-- The document a part prints as. -/
def JSXPart.doc : JSXPart → Doc
  | .content _ d => d
  | .line => .line
  -- a line break written where no whitespace stands between two children
  -- is one a parser reads as whitespace, which prettier lays out as a
  -- hard line when it reads the text back
  | .softline => .softlineRemeasure
  | .hardline => .hardline
  | .jsxWhitespace => jsxWhitespaceDoc

/-! ## Cleaning the list up -/

/-- Drop the pairs of parts that would print as two spaces, or as a line
break next to a run of whitespace, the way prettier does: it walks the
list from its end, and at every position either drops the part and the one
after it, or the two parts after it. -/
def jsxCleanup (containsText : Bool) : List JSXPart → List JSXPart
  | [] => []
  | x :: xs =>
    match jsxCleanup containsText xs with
    | [] => [x]
    | [y0] => if x.isEmptyContent && y0.isEmptyContent then [] else [x, y0]
    | y0 :: y1 :: rest =>
      let pairOfEmpties := x.isEmptyContent && y0.isEmptyContent
      let pairOfHardlines := x.isHardline && y0.isEmptyContent && y1.isHardline
      let lineThenWhitespace :=
        (x.isHardline || x.isSoftline) && y0.isEmptyContent && y1.isJsxWhitespace
      let whitespaceThenLine :=
        x.isJsxWhitespace && y0.isEmptyContent && (y1.isHardline || y1.isSoftline)
      let doubleWhitespace := x.isJsxWhitespace && y0.isEmptyContent && y1.isJsxWhitespace
      let mixedLines :=
        (x.isSoftline && y0.isEmptyContent && y1.isHardline)
          || (x.isHardline && y0.isEmptyContent && y1.isSoftline)
      if (pairOfHardlines && containsText) || pairOfEmpties || lineThenWhitespace
          || doubleWhitespace || mixedLines then
        y1 :: rest
      else if whitespaceThenLine then x :: rest
      else x :: y0 :: y1 :: rest

/-- Drop the lines and the empty contents at the end of the list. -/
def jsxTrimEnd (parts : List JSXPart) : List JSXPart :=
  (parts.reverse.dropWhile JSXPart.isTrimmable).reverse

/-- Drop the leading pairs of lines and empty contents. -/
def jsxTrimStart : List JSXPart → List JSXPart
  | a :: b :: rest =>
      if a.isTrimmable && b.isTrimmable then jsxTrimStart rest else a :: b :: rest
  | ps => ps

/-! ## The parts of the `fill` -/

/-- Build the parts of the `fill` the children are laid out as, and say
whether one of them forces the element to break.  It is prettier's last
pass over the list: a run of whitespace that stands alone, or at one of
the ends of the list, or right after a line break, is written `{" "}`
rather than left to the line to decide. -/
private def jsxGroupsAux (total : Nat) : Nat → Option JSXPart → Option JSXPart →
    List Doc → Bool → List JSXPart → List Doc × Bool
  | _, _, _, revC, forced, [] => (revC.reverse, forced)
  | h, prev1, prev2, revC, forced, v :: rest =>
    let merge (d : Doc) : List Doc :=
      match revC with
      | last :: cs => (last ++ d) :: cs
      | [] => [d]
    let pushSep (d : Doc) : List Doc := .nil :: d :: revC
    let handled : Option (List Doc) :=
      if v.isJsxWhitespace then
        if h == 1 && (prev1.map JSXPart.isEmptyContent).getD false then
          if total == 2 then some (merge rawJsxWhitespace)
          else some (pushSep (rawJsxWhitespace ++ .hardline))
        else if h + 1 == total then some (merge rawJsxWhitespace)
        else if (prev1.map JSXPart.isEmptyContent).getD false
            && (prev2.map JSXPart.isHardline).getD false then
          some (merge rawJsxWhitespace)
        else none
      else none
    match handled with
    | some revC' => jsxGroupsAux total (h + 1) (some v) prev1 revC' forced rest
    | none =>
      let d := v.doc
      let revC' := if h % 2 == 0 then merge d else pushSep d
      jsxGroupsAux total (h + 1) (some v) prev1 revC' (forced || Doc.hasForcedBreak d) rest

/-- The parts of the `fill` the children of an element are laid out as,
and whether one of them forces the element to break. -/
def jsxGroups (parts : List JSXPart) : List Doc × Bool :=
  jsxGroupsAux parts.length 0 none none [.nil] false parts

/-! ## Assembling an element -/

/-- The document of an element, from the documents of its tags and the
parts of its children.  `containsText` says that one of the children is
text, which is laid out as a `fill`; `forcedBreak` that the element is one
prettier always breaks. -/
def jsxElementDocOf (opening closing : Doc) (containsText forcedBreak : Bool)
    (parts : List JSXPart) : Doc :=
  let (groups, forcedInParts) := jsxGroups parts
  let inner := if containsText then .fill groups else Doc.groupBreak (Doc.concat groups)
  let multiline :=
    Doc.group (opening ++ .nest jsxIndent (.hardline ++ inner) ++ .hardline ++ closing)
  if forcedBreak || forcedInParts then multiline
  else
    .condGroup (.group (opening ++ Doc.concat (parts.map JSXPart.doc) ++ closing)) multiline

/-- The parentheses prettier writes around a JSX element that stands where
a line break would otherwise leave it beside other text: they are written
only when the element does not fit on the line it starts on.
`alwaysBreaks` says that the element is one prettier always writes on
lines of its own, and `noParens` that the element already stands between
parentheses written for it, so that only the line breaks are wanted. -/
def jsxWrapInParens (alwaysBreaks noParens : Bool) (d : Doc) : Doc :=
  let op : Doc := if noParens then .nil else .ifBreak (tx "(") .nil
  let cl : Doc := if noParens then .nil else .ifBreak (tx ")") .nil
  let body := op ++ .nest jsxIndent (.softline ++ d) ++ .softline ++ cl
  if alwaysBreaks then .groupBreak body else .group body

/-! ## Tags -/

/-- The opening tag of an element, from the documents of its attributes.
`selfClosing` says that the element has no children, `oneStringAttr` that
its only attribute is one whose value is a string without a line break,
which prettier never breaks the tag for, and `breaks` that one of the
attribute values holds a line break, which always breaks it.

Under `bracketSameLine` the `>` of a broken tag stands at the end of the
last attribute line rather than on a line of its own; the `/>` of a self
closing tag keeps its own line either way.  Under
`singleAttributePerLine` a tag of more than one attribute is always
broken. -/
def jsxOpeningDocOf (name : String) (selfClosing oneStringAttr breaks : Bool)
    (attrs : List Doc) : Doc :=
  if selfClosing && attrs.isEmpty then tx ("<" ++ name ++ " />")
  else if oneStringAttr then
    .group (tx ("<" ++ name ++ " ") ++ Doc.concat attrs ++ tx (if selfClosing then " />" else ">"))
  else
    let attrsDoc := Doc.concat (attrs.map (fun a => Doc.line ++ a))
    let tail : Doc :=
      if selfClosing then .line ++ tx "/>"
      else if attrs.isEmpty || Options.bracketSameLine then tx ">"
      else .softline ++ tx ">"
    let body := tx ("<" ++ name) ++ .nest jsxIndent attrsDoc ++ tail
    if breaks || (Options.singleAttributePerLine && 1 < attrs.length) then .groupBreak body
    else .group body

/-! ## Text -/

/-- Whether the character is one JSX reads as whitespace. -/
def isJSXSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

private def jsxWordsAux : List Char → String → List String
  | [], acc => if acc == "" then [] else [acc]
  | c :: cs, acc =>
      if isJSXSpace c then
        if acc == "" then jsxWordsAux cs "" else acc :: jsxWordsAux cs ""
      else jsxWordsAux cs (acc.push c)

/-- The words of a text: its runs of characters that are not whitespace. -/
def jsxWords (s : String) : List String := jsxWordsAux s.toList ""

/-- The first word of a text, or the empty string when it holds none. -/
def jsxFirstWord (s : String) : String := (jsxWords s).head?.getD ""

/-- Whether the text begins with whitespace. -/
def jsxStartsWithSpace (s : String) : Bool :=
  match s.toList with
  | c :: _ => isJSXSpace c
  | [] => false

/-- Whether the text ends with whitespace. -/
def jsxEndsWithSpace (s : String) : Bool :=
  match s.toList.reverse with
  | c :: _ => isJSXSpace c
  | [] => false

/-! ## Building the list of parts -/

/-- Add a content to the part being built: the parts hold the list in
reverse, so that the content being built is its head. -/
def jsxPushWord (rev : List JSXPart) (d : Doc) : List JSXPart :=
  match rev with
  | .content _ d0 :: cs => .content false (d0 ++ d) :: cs
  | cs => .content false d :: cs

/-- Add a separator, and the empty content that follows it.  The list
alternates contents and separators and begins with a content, so a
separator written before any content at all is given the empty content it
stands after. -/
def jsxPushSep (rev : List JSXPart) (s : JSXPart) : List JSXPart :=
  match rev with
  | [] => [.content true .nil, s, .content true .nil]
  | _ => .content true .nil :: s :: rev

/-- Add the words that follow the first one of a run of text, each on the
other side of a line from the one before it. -/
def jsxPushWords (rev : List JSXPart) : List String → List JSXPart
  | [] => rev
  | w :: ws => jsxPushWords (jsxPushWord (jsxPushSep rev .line) (tx (encodeJSXText w))) ws

/-- The separator prettier writes where no whitespace stands between two
children.  `selfClosing` says that one of the two is an element written
`<x />`, next to which a word of more than one character keeps its own
line. -/
def jsxSeparatorNoWhitespace (word : String) (selfClosing : Bool) : JSXPart :=
  if selfClosing then (if word.length == 1 then .softline else .hardline) else .softline

/-! ## The children of an element -/

/-- Whether the child is an element written `<x />`. -/
def jsxChildIsSelfClosing : MiniJSXChild → Bool
  | .node (.element _ _ none) => true
  | _ => false

/-- Whether the child is a nested element or fragment. -/
def jsxChildIsNode : MiniJSXChild → Bool
  | .node _ => true
  | _ => false

/-- Whether the child is a `{ }` substitution.  A `{" "}` is not one: a
parser reads it as the whitespace it stands for, and neither is a
`{...children}`, which a parser reads as a spread child of its own. -/
def jsxChildIsExpr : MiniJSXChild → Bool
  | .expr (.string " ") => false
  | .expr (.spread _) => false
  | .expr _ | .emptyExpr => true
  | _ => false

/-- Whether the child is text that is not empty; a `{" "}` is text. -/
def jsxChildIsText : MiniJSXChild → Bool
  | .text v => v != ""
  | .expr (.string " ") => true
  | _ => false

/-- The text of a child which is one, the empty string otherwise. -/
def jsxChildText : MiniJSXChild → String
  | .text v => v
  | .expr (.string " ") => " "
  | _ => ""

/-- Whether the child is one no source can hold, which is left out. -/
def jsxChildIsEmpty : MiniJSXChild → Bool
  | .text v => v == ""
  | _ => false

/-- Whether the element holds more than one `{ }` substitution, which
makes prettier break it. -/
def jsxHasSeveralExprs (kids : List MiniJSXChild) : Bool :=
  (kids.filter jsxChildIsExpr).length > 1

/-- Whether the expression is a template literal, tagged or not.  An
element whose only child is one holds it between its tags as it is. -/
def jsxIsTemplateExpr : MiniExpr → Bool
  | .template .. => true
  | _ => false

/-! ## Attributes -/

/-- Whether the only attribute of the element is one whose value is a
string without a line break, which prettier never breaks the tag for. -/
def jsxOneStringAttr : List MiniJSXAttribute → Bool
  | [.attr _ (some (.string v))] => !v.contains '\n'
  | _ => false

/-- Whether one of the attribute values holds a line break, which always
breaks the tag. -/
def jsxAttrsBreak (attrs : List MiniJSXAttribute) : Bool :=
  attrs.any fun
    | .attr _ (some (.string v)) => v.contains '\n'
    | _ => false

/-! ## Substitutions -/

/-- Whether the expression written in a `{ }` keeps the braces on its own
lines, rather than standing on a line of its own between them.
`inElement` says that the `{ }` is a child of an element rather than the
value of an attribute: a conditional or a binary expression written as a
child keeps the braces, and one written in an attribute does not. -/
def jsxInlinesContainer (inElement : Bool) : MiniExpr → Bool
  | .array _ | .object _ | .arrow .. | .func .. | .template .. => true
  -- a call keeps the braces on its line; a dynamic `import()`, which is
  -- not a call of the kind prettier means here, and a `new` do not
  | .call .. | .superCall _ => true
  | .chain _ links =>
      match links.toList.getLast? with
      | some (.call ..) => true
      | _ => false
  | .await a =>
      (match a with
        | .jsx _ => true
        | _ => jsxInlinesContainer false a)
  | .ternary .. | .binary .. => inElement
  | _ => false

/-- The `{ }` around an expression written as a child of an element or as
the value of an attribute, given the document of the expression.
`inElement` is as for `jsxInlinesContainer`. -/
def jsxContainerOf (inElement : Bool) (e : MiniExpr) (d : Doc) : Doc :=
  if jsxInlinesContainer inElement e then .group (tx "{" ++ d ++ tx "}")
  else .group (tx "{" ++ .nest jsxIndent (.softline ++ d) ++ .softline ++ tx "}")

/-! ## The parts of the children -/

/-- One child of an element together with the document it prints as.  A
text child prints as the words this file lays out, and carries none. -/
abbrev JSXChildDoc := MiniJSXChild × Doc

/-- Merge the runs of text that stand next to one another, as a parser
reads them: two texts written one after the other are one text, and where
the words of a text fall decides the layout of the children. -/
def jsxMergeChildDocs : List JSXChildDoc → List JSXChildDoc
  | (.text a, _) :: (.text b, _) :: rest =>
      jsxMergeChildDocs ((MiniJSXChild.text (a ++ b), Doc.nil) :: rest)
  | c :: rest => c :: jsxMergeChildDocs rest
  | [] => []
termination_by kids => kids.length

/-- The parts the children of an element are laid out as, from the
children and the documents they print as; `rev` holds the parts already
built, in reverse.  The runs of text that stand next to one another have
to have been merged first. -/
def jsxChildPartsOf (rev : List JSXPart) : List JSXChildDoc → List JSXPart
  | [] => rev.reverse
  | (c, d) :: rest =>
    let nextSelfClosing := match rest with | (n, _) :: _ => jsxChildIsSelfClosing n | [] => false
    -- the separator that follows a child which is not text: a line of its
    -- own, unless text follows it on the same line
    let afterChild (selfClosing : Bool) : JSXPart :=
      match rest with
      | (n, _) :: _ =>
        if jsxChildIsText n then
          jsxSeparatorNoWhitespace (jsxFirstWord (jsxChildText n)) selfClosing
        else .hardline
      | [] => .hardline
    -- the words of a run of text, and the runs of whitespace around them
    let textParts (v : String) : List JSXPart :=
      match jsxWords v with
      -- whitespace on its own is a run of whitespace and nothing else
      | [] => jsxPushSep rev .jsxWhitespace
      | w :: ws =>
        let rev := if jsxStartsWithSpace v then jsxPushSep rev .jsxWhitespace else rev
        let rev := jsxPushWords (jsxPushWord rev (tx (encodeJSXText w))) ws
        let lastWord := (w :: ws).getLast (by simp)
        if jsxEndsWithSpace v then jsxPushSep rev .jsxWhitespace
        else jsxPushSep rev (jsxSeparatorNoWhitespace lastWord nextSelfClosing)
    match c with
    | .text "" => jsxChildPartsOf rev rest
    | .text v => jsxChildPartsOf (textParts v) rest
    -- `{" "}` is the whitespace it stands for
    | .expr (.string " ") => jsxChildPartsOf (textParts " ") rest
    | .expr _ | .emptyExpr =>
        jsxChildPartsOf (jsxPushSep (jsxPushWord rev d) (afterChild nextSelfClosing)) rest
    | .node _ =>
        jsxChildPartsOf (jsxPushSep (jsxPushWord rev d)
          (afterChild (jsxChildIsSelfClosing c || nextSelfClosing))) rest

/-- The document of an element or a fragment, from its tags, its children
and the parts they were laid out as.  `lone` is the document of a lone
template literal child, which the element holds between its tags as it is;
`multipleAttrs` says that the element has more than one attribute, which
always breaks it. -/
def jsxAssemble (opening closing : Doc) (multipleAttrs : Bool) (kids : List MiniJSXChild)
    (rawParts : List JSXPart) (lone : Option Doc) : Doc :=
  match lone with
  | some d => opening ++ d ++ closing
  | none =>
    let containsText := kids.any jsxChildIsText
    let parts := jsxTrimStart (jsxTrimEnd (jsxCleanup containsText rawParts))
    let forced := Doc.hasForcedBreak opening || kids.any jsxChildIsNode || multipleAttrs
      || jsxHasSeveralExprs kids
    jsxElementDocOf opening closing containsText forced parts

end Language.JavaScript.MiniAST.Printer
