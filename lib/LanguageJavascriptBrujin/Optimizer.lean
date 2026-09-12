/-
An optimizer for `BrujinAST`.

The tree it works on is scope safe, so the optimizer is too: every rewrite
takes a tree in a scope to a tree in the *same* scope, and Lean checks that
— an optimization cannot drop a binding a later statement still uses, or
renumber the variables wrongly, because such a tree does not typecheck.

What it does, bottom up:

* **constant folding.**  `1 + 2` becomes `3`, `"a" + "b"` becomes `"ab"`,
  `1 < 2` becomes `true`, `!0` becomes `true`, `typeof "s"` becomes
  `"string"`, `~5` becomes `-6`, `6 & 3` becomes `2`.  Only integers that
  JavaScript represents exactly (`|v| ≤ 2^53 - 1`) are folded, division and
  `%` only when they are exact, and a comparison of two strings only when
  both are ASCII, so that Lean's ordering is JavaScript's;
* **the short circuiting operators.**  `true && e` becomes `e`, `false && e`
  becomes `false`, `0 || e` becomes `e`, and `e1 ? e2 : e3` with a literal
  condition becomes the branch it selects (these do *not* need the other
  operand to be a literal);
* **the comma operator.**  `e1, e2` becomes `e2` when `e1` has no effect;
* **branch pruning.**  `if (true) A else B` becomes the block `A`,
  `while (false) A` disappears, and so does an `if` with a condition
  without effect and no statement in either branch;
* **dead statements.**  An expression statement without effect and an empty
  block are dropped, and everything after a `return`, a `throw`, a `break`
  or a `continue` in the same block is dropped, since it cannot be reached
  (`BrujinAST` has no hoisting, so a declaration that follows one is not
  visible before it either);
* **dead bindings.**  Inside a block, a `const`, a `let`, a `function` or a
  `class` declaration whose value cannot have an effect and which nothing
  in the rest of the block mentions is deleted, and the variables of the
  rest of the block are renumbered (`BrujinStrengthen`).  Whether it is
  mentioned is not a separate analysis: the renumbering is exactly the
  operation that fails when it is.  A *top level* binding is never deleted
  — it may be reached from outside the module — and neither is a parameter
  or a `catch` binder, which are positional.

Whether an expression "has an effect" is decided conservatively by
`Expr.isPure`: a call, a `new`, an assignment, an increment, an `await`, a
`yield`, a `delete` and even a member access (which may run a getter) all
count as having one.

Every rewrite is a rewrite of the *program*, not of a value: the optimizer
does not assume anything about a variable it cannot see the binding of, and
an `unsafeExt` is never touched.
-/
import LanguageJavascriptBrujin.ToMini
import LanguageJavascriptBrujin.Strengthen
import LanguageJavascript.RegExpEngine

namespace Language.JavaScript.BrujinAST

-- The extensions a tree may mention.  Every function here is generic in
-- them: the optimizer never looks inside an extension, and only has to be
-- able to move one to a smaller scope when it deletes a binding.
variable {exprExt targetExt : Nat → Nat → Type}
  [ExtInvariant exprExt] [ExtInvariant targetExt]

open Language.JavaScript.MiniAST

/-! ## Literals

The optimizer only computes with values JavaScript represents exactly: an
integer of at most 2^53 - 1 in absolute value, a string, a boolean and
`null`.  A numeric literal with a fraction or an exponent is left alone. -/

/-- The value of a literal the optimizer can compute with. -/
inductive Lit where
  /-- An integer that JavaScript represents exactly. -/
  | num (value : Int)
  /-- A string. -/
  | str (value : String)
  /-- `true` or `false`. -/
  | bool (value : Bool)
  /-- `null`. -/
  | null
deriving Repr, DecidableEq, Inhabited

/-- The largest integer JavaScript represents exactly. -/
def maxSafeInteger : Int := 9007199254740991

/-- The value of a numeric literal, when it is an integer JavaScript
represents exactly; a literal with a fraction or one too large has none. -/
def intOfNumeral? (n : JSNumber) : Option Int :=
  match n.toNat? with
  | some v => if (v : Int) ≤ maxSafeInteger then some (v : Int) else none
  | none => none

/-- The literal an expression is, if it is one the optimizer computes
with. -/
def litOf? {c m : Nat} : Expr exprExt targetExt c m → Option Lit
  | .number n => (intOfNumeral? n).map .num
  | .string v => some (.str v)
  | .true_ => some (.bool true)
  | .false_ => some (.bool false)
  | .null => some .null
  | .unary .minus e =>
      match e with
      | .number n => (intOfNumeral? n).map fun v => .num (-v)
      | _ => none
  | _ => none

/-- The expression a literal value is written as; a negative number is a
literal with a unary minus, as JavaScript has no negative literal. -/
def exprOfLit {c m : Nat} : Lit → Expr exprExt targetExt c m
  | .num v =>
      if v < 0 then .unary .minus (.number (JSNumber.ofNat (-v).toNat))
      else .number (JSNumber.ofNat v.toNat)
  | .str s => .string s
  | .bool true => .true_
  | .bool false => .false_
  | .null => .null

/-- Whether a value is truthy, as `if` and `&&` understand it. -/
def Lit.truthy : Lit → Bool
  | .num v => v != 0
  | .str s => s != ""
  | .bool b => b
  | .null => false

/-- The string a value is converted to by `+`. -/
def Lit.toJSString : Lit → String
  | .num v => toString v
  | .str s => s
  | .bool true => "true"
  | .bool false => "false"
  | .null => "null"

/-- Whether every character is ASCII, so that Lean's ordering of the string
is JavaScript's. -/
private def isAscii (s : String) : Bool := s.all fun ch : Char => ch.toNat < 128

/-! ## Purity

Whether evaluating an expression can be observed.  The answer is
conservative: everything that could run code — a call, a member access
(a getter), a template with a substitution (`toString`), `in` and
`instanceof` (a proxy) — is taken to have an effect. -/

mutual

/-- Whether an expression can be evaluated without an observable effect,
conservatively. -/
def Expr.isPure {c m : Nat} : Expr exprExt targetExt c m → Bool
  | .mutVar _ | .constVar _ | .unsafeExt _ => true
  | .number _ | .string _ | .regex _ | .null | .true_ | .false_ | .this => true
  -- `new.target` is a read of the current invocation, with no effect
  | .newTarget => true
  -- `super.x` reads a member of the home object, which may be a getter,
  -- and `super(...)` runs the constructor of the parent class
  | .superDot _ | .superIndex _ | .superCall _ => false
  | .array els => ArrayElems.isPure els
  | .object ps => Properties.isPure ps
  | .assign _ _ _ | .update _ _ _ => false
  | .await _ | .yield _ | .yieldFrom _ => false
  | .call _ _ | .new _ _ => false
  | .dot _ _ | .index _ _ | .privateDot _ _ => false
  | .privateName _ => true
  -- a chain reads a member or calls, exactly like what it is written for
  | .chain _ _ _ => false
  | .importMeta => true
  -- a dynamic import loads a module
  | .importCall _ _ => false
  | .classAnon _ _ _ | .classSelf _ _ _ => false
  | .seq a b => a.isPure && b.isPure
  | .binary a op b =>
      match op with
      | .inOp | .instanceOf => false
      | _ => a.isPure && b.isPure
  | .ternary a b d => a.isPure && b.isPure && d.isPure
  | .arrow _ _ _ | .func _ _ _ _ _ | .funcSelf _ _ _ _ _ => true
  | .spread _ => false
  | .template _ _ _ => false
  | .unary op e =>
      match op with
      | .delete | .preIncr | .preDecr => false
      | _ => e.isPure

/-- Whether every element of an array literal is pure. -/
def ArrayElems.isPure {c m : Nat} : ArrayElems exprExt targetExt c m → Bool
  | .nil => true
  | .cons .hole r => ArrayElems.isPure r
  | .cons (.elem e) r => e.isPure && ArrayElems.isPure r

/-- Whether every member of an object literal is pure. -/
def Properties.isPure {c m : Nat} : Properties exprExt targetExt c m → Bool
  | .nil => true
  | .cons (.keyValue k v) r => PropName.isPure k && v.isPure && Properties.isPure r
  -- a spread reads every property of what it copies, so it can run a getter
  | .cons (.spread _) _ => false
  | .cons (.method _ k _ _ _) r => PropName.isPure k && Properties.isPure r

/-- Whether the name of a property is pure. -/
def PropName.isPure {c m : Nat} : PropName exprExt targetExt c m → Bool
  | .ident _ | .private_ _ | .string _ | .number _ => true
  | .computed e => e.isPure

end

/-- Whether a list of expressions is empty; a decorator is run when the
class is defined, so a decorated member is not effect free. -/
def Exprs.isNil {c m : Nat} : Exprs exprExt targetExt c m → Bool
  | .nil => true
  | .cons _ _ => false

/-- Whether an optional expression is pure. -/
def OptExpr.isPure {c m : Nat} : OptExpr exprExt targetExt c m → Bool
  | .none => true
  | .some e => e.isPure

/-- Whether the members of a class body can be defined without an
observable effect, which is what decides whether declaring the class has
one.  The body of a method is not run, so only its key matters; a decorator
*is* run, and so is a static block and the initialiser of a static field,
while the initialiser of an instance field runs when an instance is built
and not when the class is defined. -/
def ClassElems.keysArePure {c m : Nat} : ClassElems exprExt targetExt c m → Bool
  | .nil => true
  | .cons (.method ds _ _ key _ _ _) r =>
      Exprs.isNil ds && PropName.isPure key && ClassElems.keysArePure r
  | .cons (.field ds isStatic key init) r =>
      Exprs.isNil ds && PropName.isPure key && (!isStatic || init.isPure)
        && ClassElems.keysArePure r
  | .cons (.staticBlock _) _ => false

/-! ## Folding an operator -/

/-- 32 bit two's complement, as `&`, `|`, `^` and the shifts use it. -/
private def toUint32 (v : Int) : Nat := (v % 4294967296).toNat

/-- The signed value of a 32 bit word. -/
private def ofUint32 (n : Nat) : Int :=
  if n ≥ 2147483648 then (n : Int) - 4294967296 else (n : Int)

/-- Whether an integer is one JavaScript represents exactly. -/
private def isSafe (v : Int) : Bool := v.natAbs ≤ maxSafeInteger.toNat

/-- The value of `a op b`, when it is one the optimizer computes. -/
def foldBinary (a : Lit) (op : BinOp) (b : Lit) : Option Lit :=
  match op, a, b with
  -- arithmetic
  | .plus, .num x, .num y => if isSafe (x + y) then some (.num (x + y)) else none
  | .minus, .num x, .num y => if isSafe (x - y) then some (.num (x - y)) else none
  | .times, .num x, .num y => if isSafe (x * y) then some (.num (x * y)) else none
  | .divide, .num x, .num y =>
      if y != 0 && Int.tmod x y == 0 then some (.num (Int.tdiv x y)) else none
  | .mod, .num x, .num y => if y != 0 then some (.num (Int.tmod x y)) else none
  -- string concatenation, and a string with a number
  | .plus, .str x, .str y => some (.str (x ++ y))
  | .plus, .str x, .num y => some (.str (x ++ Lit.toJSString (.num y)))
  | .plus, .num x, .str y => some (.str (Lit.toJSString (.num x) ++ y))
  -- comparison
  | .lt, .num x, .num y => some (.bool (x < y))
  | .le, .num x, .num y => some (.bool (x ≤ y))
  | .gt, .num x, .num y => some (.bool (x > y))
  | .ge, .num x, .num y => some (.bool (x ≥ y))
  | .lt, .str x, .str y => if isAscii x && isAscii y then some (.bool (x < y)) else none
  | .le, .str x, .str y => if isAscii x && isAscii y then some (.bool (x ≤ y)) else none
  | .gt, .str x, .str y => if isAscii x && isAscii y then some (.bool (x > y)) else none
  | .ge, .str x, .str y => if isAscii x && isAscii y then some (.bool (x ≥ y)) else none
  -- equality; only values of the same kind, where `==` and `===` agree
  | .strictEq, x, y => some (.bool (sameKindEq x y))
  | .strictNeq, x, y => some (.bool (!sameKindEq x y))
  | .eq, x, y => if sameKind x y then some (.bool (sameKindEq x y)) else none
  | .neq, x, y => if sameKind x y then some (.bool (!sameKindEq x y)) else none
  -- bitwise, on 32 bit words
  | .bitAnd, .num x, .num y => some (.num (ofUint32 (Nat.land (toUint32 x) (toUint32 y))))
  | .bitOr, .num x, .num y => some (.num (ofUint32 (Nat.lor (toUint32 x) (toUint32 y))))
  | .bitXor, .num x, .num y => some (.num (ofUint32 (Nat.xor (toUint32 x) (toUint32 y))))
  | .lsh, .num x, .num y =>
      some (.num (ofUint32 ((toUint32 x <<< (toUint32 y % 32)) % 4294967296)))
  | .rsh, .num x, .num y =>
      let s := toUint32 y % 32
      some (.num (Int.fdiv (ofUint32 (toUint32 x)) ((2 ^ s : Nat) : Int)))
  | .ursh, .num x, .num y => some (.num ((toUint32 x >>> (toUint32 y % 32) : Nat)))
  | _, _, _ => none
where
  /-- Whether two values are of the same kind, so that `==` and `===`
  agree on them. -/
  sameKind : Lit → Lit → Bool
    | .num _, .num _ => true
    | .str _, .str _ => true
    | .bool _, .bool _ => true
    | .null, .null => true
    | _, _ => false
  /-- Whether two values are `===`. -/
  sameKindEq : Lit → Lit → Bool
    | .num x, .num y => x == y
    | .str x, .str y => x == y
    | .bool x, .bool y => x == y
    | .null, .null => true
    | _, _ => false

/-- The value of `op a`, when it is one the optimizer computes. -/
def foldUnary (op : UnaryOp) (a : Lit) : Option Lit :=
  match op, a with
  | .not, v => some (.bool (!v.truthy))
  | .minus, .num v => if isSafe (-v) then some (.num (-v)) else none
  | .plus, .num v => some (.num v)
  | .tilde, .num v => some (.num (ofUint32 (Nat.xor (toUint32 v) 4294967295)))
  | .typeof, .num _ => some (.str "number")
  | .typeof, .str _ => some (.str "string")
  | .typeof, .bool _ => some (.str "boolean")
  | .typeof, .null => some (.str "object")
  | _, _ => none

/-- The result of `typeof e` for the expressions whose type is known
without evaluating them. -/
def typeofOf? {c m : Nat} : Expr exprExt targetExt c m → Option String
  | .arrow _ _ _ | .func _ _ _ _ _ | .funcSelf _ _ _ _ _
  | .classAnon _ _ _ | .classSelf _ _ _ => some "function"
  | e => (litOf? e).bind fun v => (foldUnary .typeof v).bind fun
      | .str s => some s
      | _ => none

/-! ## Folding a call on a regular expression

A regular expression literal is matched by the `lean-regex` library
(`Language.JavaScript.RegExpEngine`), whose engines are proved correct, so a
call whose receiver, pattern and arguments are all literals can be computed
here.

The conditions are deliberately narrow, and a call which does not meet them
is left alone:

* the pattern has to be one the library reads, and its flags ones under
  which a search means what the library's search means — `RegExpLit.test?`
  and friends answer `none` otherwise;
* the pattern, the subject and the replacement have to be ASCII, as they do
  for a comparison of two strings: JavaScript matches over UTF-16 code
  units and the library over `Char`, and the two agree there;
* a replacement may not contain a `$`, which JavaScript reads as a reference
  to a capture group and the library does not;
* `replaceAll` is folded only for a global literal, since JavaScript throws
  a `TypeError` for a non-global one.

A fresh literal has a `lastIndex` of `0` and is thrown away right after the
call, so the `g` flag does not make the value of the call depend on
anything: what `g` selects is whether `replace` replaces one match or all of
them.  As everywhere else in this pass, the value is the one JavaScript
computes as long as the prototypes are the standard ones, which
`optimizeProgramChecked` refuses a program that changes. -/

/-- The value of a call on a regular expression literal, when the optimizer
computes it.  `callee` and `args` are already optimized. -/
def foldRegexCall? {c m : Nat} (callee : Expr exprExt targetExt c m) (args : Exprs exprExt targetExt c m) :
    Option (Expr exprExt targetExt c m) :=
  match callee, args with
  -- `/re/.test("s")`
  | .dot (.regex r) name, .cons (.string s) .nil =>
      if name.val == "test" && isAscii r.source.val && isAscii s then
        match r.test? s with
        | some true => some .true_
        | some false => some .false_
        | none => none
      else none
  -- `"s".replace(/re/, "t")` and `"s".replaceAll(/re/g, "t")`
  | .dot (.string s) name, .cons (.regex r) (.cons (.string repl) .nil) =>
      if isAscii r.source.val && isAscii s && isAscii repl && !repl.contains '$' then
        if name.val == "replace" then (r.replaceJS? s repl).map .string
        else if name.val == "replaceAll" && r.flags.global then
          (r.compiled?).map fun cr => .string (cr.replaceAll s repl)
        else none
      else none
  | _, _ => none

/-! ## The pass

Every function rewrites a node into one of the same type, which is to say
in the same scope: what the optimizer produces is scope correct by
construction. -/

/-- What is to be done with a statement of a block. -/
inductive StmtOpt (exprExt targetExt : Nat → Nat → Type) (c m dc dm : Nat) where
  /-- Keep it, rewritten. -/
  | keep (stmt : Stmt exprExt targetExt c m dc dm)
  /-- Drop it; it binds nothing, so the rest of the block stays in scope. -/
  | drop (hc : dc = 0) (hm : dm = 0)
  /-- Keep it, and drop everything that follows it in the block. -/
  | terminator (stmt : Stmt exprExt targetExt c m dc dm)

/-- A statement is one of the possible answers. -/
instance {c m dc dm : Nat} [Inhabited (Stmt exprExt targetExt c m dc dm)] : Inhabited (StmtOpt exprExt targetExt c m dc dm) :=
  ⟨.keep default⟩

/-- The one statement of a block, when it has exactly one and it binds
nothing — in which case the block is the same thing as the statement. -/
def Block.single? {c m : Nat} : Block exprExt targetExt c m → Option (Stmt exprExt targetExt c m 0 0)
  | .cons (.expr e) .nil => some (.expr e)
  | .cons (.block b) .nil => some (.block b)
  | .cons (.if_ cond t e) .nil => some (.if_ cond t e)
  | .cons (.while_ cond b) .nil => some (.while_ cond b)
  | .cons (.doWhile b cond) .nil => some (.doWhile b cond)
  | .cons (.for_ init cond step body) .nil => some (.for_ init cond step body)
  | .cons (.forIn head obj body) .nil => some (.forIn head obj body)
  | .cons (.forOf head obj body) .nil => some (.forOf head obj body)
  | .cons (.return_ e) .nil => some (.return_ e)
  | .cons (.throw e) .nil => some (.throw e)
  | .cons (.break_ l) .nil => some (.break_ l)
  | .cons (.continue_ l) .nil => some (.continue_ l)
  | .cons (.labelled (dc := 0) (dm := 0) l s) .nil => some (.labelled l s)
  | .cons (.switch disc cases) .nil => some (.switch disc cases)
  | .cons (.try_ b tail) .nil => some (.try_ b tail)
  | _ => none

/-- Whether a statement transfers control, so that what follows it in its
block cannot be reached. -/
def Stmt.isTerminator {c m dc dm : Nat} : Stmt exprExt targetExt c m dc dm → Bool
  | .return_ _ | .throw _ | .break_ _ | .continue_ _ => true
  | _ => false

/-- What a block amounts to as a statement: nothing when it is empty, the
statement itself when it has exactly one that binds nothing, and a block
otherwise. -/
def blockAsStmt {c m : Nat} (b : Block exprExt targetExt c m) : StmtOpt exprExt targetExt c m 0 0 :=
  match b with
  | .nil => .drop rfl rfl
  | b =>
      match b.single? with
      | some s => if s.isTerminator then .terminator s else .keep s
      | none => .keep (.block b)

mutual

/-- Optimize an expression. -/
def optExpr {c m : Nat} (e : Expr exprExt targetExt c m) : Expr exprExt targetExt c m :=
  match e with
  | .mutVar i => .mutVar i
  | .constVar i => .constVar i
  | .unsafeExt e => .unsafeExt e
  | .number n => .number n
  | .string v => .string v
  | .regex r => .regex r
  | .null => .null
  | .true_ => .true_
  | .false_ => .false_
  | .this => .this
  | .superDot n => .superDot n
  | .superIndex i => .superIndex (optExpr i)
  | .superCall args => .superCall (optExprs args)
  | .newTarget => .newTarget
  | .array els => .array (optArrayElems els)
  | .object ps => .object (optProperties ps)
  | .assign t op rhs => .assign (optTarget t) op (optExpr rhs)
  | .update t op isPrefix => .update (optTarget t) op isPrefix
  | .await x => .await (optExpr x)
  | .call f args =>
      let f := optExpr f
      let args := optExprs args
      match foldRegexCall? f args with
      | some v => v
      | none => .call f args
  | .new f args => .new (optExpr f) (optExprs args)
  | .dot o n => .dot (optExpr o) n
  | .index o i => .index (optExpr o) (optExpr i)
  | .privateDot o n => .privateDot (optExpr o) n
  | .privateName n => .privateName n
  | .chain base hd tl => .chain (optExpr base) (optChainLink hd) (optChainLinks tl)
  | .importMeta => .importMeta
  | .importCall spec opts => .importCall (optExpr spec) (optOptExpr opts)
  | .classAnon ds her body =>
      .classAnon (optExprs ds) (optOptExpr her) (optClassElems body)
  | .classSelf ds her body =>
      .classSelf (optExprs ds) (optOptExpr her) (optClassElems body)
  | .seq a b =>
      let a := optExpr a
      let b := optExpr b
      if a.isPure then b else .seq a b
  | .binary a op b =>
      let a := optExpr a
      let b := optExpr b
      match op with
      | .and =>
          match litOf? a with
          | some v => if v.truthy then b else a
          | none => .binary a op b
      | .or =>
          match litOf? a with
          | some v => if v.truthy then a else b
          | none => .binary a op b
      | .coalesce =>
          -- `null ?? b` is `b`; any other literal is not nullish, so it is
          -- the value of the whole expression
          match litOf? a with
          | some .null => b
          | some _ => a
          | none => .binary a op b
      | _ =>
          match litOf? a, litOf? b with
          | some x, some y =>
              match foldBinary x op y with
              | some v => exprOfLit v
              | none => .binary a op b
          | _, _ => .binary a op b
  | .ternary cond t f =>
      let cond := optExpr cond
      let t := optExpr t
      let f := optExpr f
      match litOf? cond with
      | some v => if v.truthy then t else f
      | none => .ternary cond t f
  | .arrow arity hasRest body => .arrow arity hasRest (optArrowBody body)
  | .func isAsync isGen hasRest arity body =>
      .func isAsync isGen hasRest arity (optBlock body)
  | .funcSelf isAsync isGen hasRest arity body =>
      .funcSelf isAsync isGen hasRest arity (optBlock body)
  | .spread x => .spread (optExpr x)
  | .template tag head parts => .template (optOptExpr tag) head (optTemplateParts parts)
  | .unary op x =>
      let x := optExpr x
      match op with
      | .typeof =>
          match typeofOf? x with
          | some s => .string s
          | none => .unary op x
      | _ =>
          match litOf? x with
          | some v =>
              match foldUnary op v with
              | some r => exprOfLit r
              | none => .unary op x
          | none => .unary op x
  | .yield x => .yield (optOptExpr x)
  | .yieldFrom x => .yieldFrom (optExpr x)

/-- Optimize an assignment target. -/
def optTarget {c m : Nat} : Target exprExt targetExt c m → Target exprExt targetExt c m
  | .mut i => .mut i
  | .unsafeExt e => .unsafeExt e
  | .dot o n => .dot (optExpr o) n
  | .privateDot o n => .privateDot (optExpr o) n
  | .superDot n => .superDot n
  | .superIndex i => .superIndex (optExpr i)
  | .index o i => .index (optExpr o) (optExpr i)

/-- Optimize one link of an optional chain. -/
def optChainLink {c m : Nat} : ChainLink exprExt targetExt c m → ChainLink exprExt targetExt c m
  | .dot opt n => .dot opt n
  | .privateDot opt n => .privateDot opt n
  | .index opt i => .index opt (optExpr i)
  | .call opt args => .call opt (optExprs args)

/-- Optimize the links of an optional chain. -/
def optChainLinks {c m : Nat} : ChainLinks exprExt targetExt c m → ChainLinks exprExt targetExt c m
  | .nil => .nil
  | .cons hd tl => .cons (optChainLink hd) (optChainLinks tl)

/-- Optimize a list of expressions. -/
def optExprs {c m : Nat} : Exprs exprExt targetExt c m → Exprs exprExt targetExt c m
  | .nil => .nil
  | .cons e r => .cons (optExpr e) (optExprs r)

/-- Optimize an optional expression. -/
def optOptExpr {c m : Nat} : OptExpr exprExt targetExt c m → OptExpr exprExt targetExt c m
  | .none => .none
  | .some e => .some (optExpr e)

/-- Optimize the elements of an array literal. -/
def optArrayElems {c m : Nat} : ArrayElems exprExt targetExt c m → ArrayElems exprExt targetExt c m
  | .nil => .nil
  | .cons .hole r => .cons .hole (optArrayElems r)
  | .cons (.elem e) r => .cons (.elem (optExpr e)) (optArrayElems r)

/-- Optimize the substitutions of a template literal. -/
def optTemplateParts {c m : Nat} : TemplateParts exprExt targetExt c m → TemplateParts exprExt targetExt c m
  | .nil => .nil
  | .cons (.mk e s) r => .cons (.mk (optExpr e) s) (optTemplateParts r)

/-- Optimize the name of a property. -/
def optPropName {c m : Nat} : PropName exprExt targetExt c m → PropName exprExt targetExt c m
  | .ident n => .ident n
  | .private_ n => .private_ n
  | .string v => .string v
  | .number raw => .number raw
  | .computed e => .computed (optExpr e)

/-- Optimize the members of an object literal. -/
def optProperties {c m : Nat} : Properties exprExt targetExt c m → Properties exprExt targetExt c m
  | .nil => .nil
  | .cons (.keyValue k v) r => .cons (.keyValue (optPropName k) (optExpr v)) (optProperties r)
  | .cons (.spread e) r => .cons (.spread (optExpr e)) (optProperties r)
  | .cons (.method kind k arity hasRest body) r =>
      .cons (.method kind (optPropName k) arity hasRest (optBlock body)) (optProperties r)

/-- Optimize the members of a class body. -/
def optClassElems {c m : Nat} : ClassElems exprExt targetExt c m → ClassElems exprExt targetExt c m
  | .nil => .nil
  | .cons (.method ds isStatic kind k arity hasRest body) r =>
      .cons (.method (optExprs ds) isStatic kind (optPropName k) arity hasRest (optBlock body))
        (optClassElems r)
  | .cons (.field ds isStatic k init) r =>
      .cons (.field (optExprs ds) isStatic (optPropName k) (optOptExpr init)) (optClassElems r)
  | .cons (.staticBlock body) r => .cons (.staticBlock (optBlock body)) (optClassElems r)

/-- Optimize the body of an arrow function. -/
def optArrowBody {c m : Nat} : ArrowBody exprExt targetExt c m → ArrowBody exprExt targetExt c m
  | .expr e => .expr (optExpr e)
  | .block b => .block (optBlock b)

/-- Optimize the first clause of a `for (;;)`. -/
def optForInit {c m dc dm : Nat} : ForInit exprExt targetExt c m dc dm → ForInit exprExt targetExt c m dc dm
  | .none => .none
  | .expr e => .expr (optExpr e)
  | .constDecl init => .constDecl (optExpr init)
  | .letDecl init => .letDecl (optOptExpr init)

/-- Optimize the binder of a `for (... of ...)`. -/
def optForHead {c m dc dm : Nat} : ForHead exprExt targetExt c m dc dm → ForHead exprExt targetExt c m dc dm
  | .target t => .target (optTarget t)
  | .constBind => .constBind
  | .letBind => .letBind

/-- Optimize the cases of a `switch`. -/
def optSwitchCases {c m : Nat} : SwitchCases exprExt targetExt c m → SwitchCases exprExt targetExt c m
  | .nil => .nil
  | .cons (.case t b) r => .cons (.case (optExpr t) (optBlock b)) (optSwitchCases r)
  | .cons (.default b) r => .cons (.default (optBlock b)) (optSwitchCases r)

/-- Optimize an optional block. -/
def optOptBlock {c m : Nat} : OptBlock exprExt targetExt c m → OptBlock exprExt targetExt c m
  | .none => .none
  | .some b => .some (optBlock b)

/-- Optimize what follows the block of a `try`. -/
def optTryTail {c m : Nat} : TryTail exprExt targetExt c m → TryTail exprExt targetExt c m
  | .catch_ body fin => .catch_ (optBlock body) (optOptBlock fin)
  | .finallyOnly b => .finallyOnly (optBlock b)

/-- Optimize a statement, and say whether it can be dropped, or makes the
statements that follow it unreachable. -/
def optStmt {c m dc dm : Nat} (s : Stmt exprExt targetExt c m dc dm) : StmtOpt exprExt targetExt c m dc dm :=
  match s with
  | .expr e =>
      let e := optExpr e
      if e.isPure then .drop rfl rfl else .keep (.expr e)
  | .constDecl init => .keep (.constDecl (optExpr init))
  | .letDecl init => .keep (.letDecl (optOptExpr init))
  -- a `using` binding is never dropped: disposing of what it holds is
  -- what it is written for
  | .usingDecl isAwait init => .keep (.usingDecl isAwait (optExpr init))
  | .block b => blockAsStmt (optBlock b)
  | .if_ cond thenB elseB =>
      let cond := optExpr cond
      let thenB := optBlock thenB
      let elseB := optOptBlock elseB
      match litOf? cond with
      | some v =>
          if v.truthy then blockAsStmt thenB
          else
            match elseB with
            | .none => .drop rfl rfl
            | .some b => blockAsStmt b
      | none =>
          match thenB, elseB with
          | .nil, .none => if cond.isPure then .drop rfl rfl else .keep (.expr cond)
          | _, _ => .keep (.if_ cond thenB elseB)
  | .while_ cond body =>
      let cond := optExpr cond
      match litOf? cond with
      | some v => if v.truthy then .keep (.while_ cond (optBlock body)) else .drop rfl rfl
      | none => .keep (.while_ cond (optBlock body))
  | .doWhile body cond => .keep (.doWhile (optBlock body) (optExpr cond))
  | .for_ init cond step body =>
      .keep (.for_ (optForInit init) (optOptExpr cond) (optOptExpr step) (optBlock body))
  | .forIn head obj body => .keep (.forIn (optForHead head) (optExpr obj) (optBlock body))
  | .forOf head obj body => .keep (.forOf (optForHead head) (optExpr obj) (optBlock body))
  | .funcDecl isAsync isGen hasRest arity body =>
      .keep (.funcDecl isAsync isGen hasRest arity (optBlock body))
  | .classDecl ds her body =>
      .keep (.classDecl (optExprs ds) (optOptExpr her) (optClassElems body))
  | .return_ e => .terminator (.return_ (optOptExpr e))
  | .throw e => .terminator (.throw (optExpr e))
  | .break_ l => .terminator (.break_ l)
  | .continue_ l => .terminator (.continue_ l)
  | .labelled l s' =>
      match optStmt s' with
      | .keep s'' => .keep (.labelled l s'')
      | .terminator s'' => .keep (.labelled l s'')
      | .drop hc hm => .drop hc hm
  | .switch disc cases => .keep (.switch (optExpr disc) (optSwitchCases cases))
  | .try_ b tail => .keep (.try_ (optBlock b) (optTryTail tail))

/-- Optimize a block: every statement, dropping the ones without effect,
the bindings nothing uses, and everything after a statement that transfers
control. -/
def optBlock {c m : Nat} : Block exprExt targetExt c m → Block exprExt targetExt c m
  | .nil => .nil
  | .cons hd tl =>
      match optStmt hd with
      -- the tail is optimized first and the (identical) scopes are matched
      -- up afterwards, so that the recursive call is on the tail itself
      | .drop hc hm =>
          Block.castScope (by omega) (by omega) (optBlock tl)
      | .terminator s => .cons s .nil
      | .keep s =>
          match s, tl with
          | .constDecl init, tl =>
              let rest := optBlock tl
              dropUnusedConst (.constDecl init) init.isPure rest
          | .letDecl init, tl =>
              let rest := optBlock tl
              dropUnusedMut (.letDecl init) init.isPure rest
          | .funcDecl isAsync isGen hasRest arity body, tl =>
              let rest := optBlock tl
              dropUnusedConst (.funcDecl isAsync isGen hasRest arity body) true rest
          | .classDecl ds her body, tl =>
              let rest := optBlock tl
              dropUnusedConst (.classDecl ds her body)
                (match ds, her with
                  | .nil, .none => body.keysArePure
                  | _, _ => false) rest
          | s, tl => .cons s (optBlock tl)

/-- Drop a statement that binds one const variable, when defining it has no
effect and the rest of the block does not use it. -/
def dropUnusedConst {c m : Nat} (s : Stmt exprExt targetExt c m 1 0) (defPure : Bool) (rest : Block exprExt targetExt (c + 1) m) :
    Block exprExt targetExt c m :=
  if defPure then
    match strengthenConstBlock 0 rest with
    | some b => b
    | none => .cons s rest
  else .cons s rest

/-- Drop a statement that binds one mutable variable, when its initializer
has no effect and the rest of the block does not use it. -/
def dropUnusedMut {c m : Nat} (s : Stmt exprExt targetExt c m 0 1) (defPure : Bool) (rest : Block exprExt targetExt c (m + 1)) :
    Block exprExt targetExt c m :=
  if defPure then
    match strengthenMutBlock 0 rest with
    | some b => b
    | none => .cons s rest
  else .cons s rest

end

/-! ## Programs -/

/-- Optimize a top level item that is not a statement; an `import` or an
`export` is left alone, since what a module exports is part of what it
does. -/
def optModuleItem {c m dc dm : Nat} (it : ModuleItem exprExt targetExt c m dc dm) : ModuleItem exprExt targetExt c m dc dm :=
  match it with
  | .stmt s =>
      match optStmt s with
      | .keep s' => .stmt s'
      | .terminator s' => .stmt s'
      | .drop _ _ => .stmt s
  | .importBare mod attrs => .importBare mod attrs
  | .importClause clause => .importClause clause
  | .exportFrom specs mod attrs => .exportFrom specs mod attrs
  | .exportAll alias_ mod attrs => .exportAll alias_ mod attrs
  | .exportDefaultExpr e => .exportDefaultExpr (optExpr e)
  | .exportLocals specs => .exportLocals specs
  | .exportDecl s =>
      match optStmt s with
      | .keep s' => .exportDecl s'
      | .terminator s' => .exportDecl s'
      | .drop _ _ => .exportDecl s

/-- Optimize the top level items.  A statement without effect is dropped
here too, but nothing that *follows* one is: a module is not left by a
`return`, and an `export` is never dropped. -/
def optModuleItems {c m : Nat} : ModuleItems exprExt targetExt c m → ModuleItems exprExt targetExt c m
  | .nil => .nil
  | .cons it r =>
      match it with
      | .stmt s =>
          match optStmt s with
          | .keep s' => .cons (.stmt s') (optModuleItems r)
          | .terminator s' => .cons (.stmt s') (optModuleItems r)
          | .drop hc hm =>
              ModuleItems.castScope (by omega) (by omega) (optModuleItems r)
      | it => .cons (optModuleItem it) (optModuleItems r)

/-- Optimize a program: one bottom up pass.  The optimizer never invents a
global, so the set of globals of the result is the one of the input. -/
def optimizeProgram (p : Program) : Program := ⟨p.globals, optModuleItems p.items⟩

/-- Optimize an expression: one bottom up pass. -/
def optimizeExpr {c m : Nat} (e : Expr exprExt targetExt c m) : Expr exprExt targetExt c m := optExpr e

/-- Optimize a block of statements: one bottom up pass. -/
def optimizeBlock {c m : Nat} (b : Block exprExt targetExt c m) : Block exprExt targetExt c m := optBlock b

/-- Optimize a program repeatedly, until a pass changes nothing or `fuel`
passes have been run.  One pass already folds bottom up, so this only helps
where a rewrite creates a new opportunity above it. -/
def optimizeProgramFix (fuel : Nat) (p : Program) : Program :=
  match fuel with
  | 0 => p
  | fuel + 1 =>
      let q := optimizeProgram p
      if q == p then q else optimizeProgramFix fuel q

end Language.JavaScript.BrujinAST
