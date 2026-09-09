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
an `unsafeGlobal` is never touched.
-/
import LanguageJavascriptBrujin.ToMini
import LanguageJavascriptBrujin.Strengthen

namespace Language.JavaScript.BrujinAST

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

/-- The value of a digit in base 16, if it is one. -/
private def digitValue? (ch : Char) : Option Nat :=
  if ch.isDigit then some (ch.toNat - '0'.toNat)
  else if 'a' ≤ ch && ch ≤ 'f' then some (ch.toNat - 'a'.toNat + 10)
  else none

/-- Read a natural number in the given base; `none` if a character is not a
digit of that base, or if there is no digit at all. -/
private def natOfDigits? (base : Nat) (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldl (init := some 0) fun acc ch => do
    let d ← digitValue? ch
    if d < base then pure ((← acc) * base + d) else none

/-- The value of a numeric literal, when it is an integer JavaScript
represents exactly; a literal with a fraction or an exponent has none. -/
def intOfNumeral? (raw : String) : Option Int :=
  let cs := raw.toLower.toList
  let n? :=
    match cs with
    | '0' :: 'x' :: rest => natOfDigits? 16 rest
    | '0' :: 'b' :: rest => natOfDigits? 2 rest
    | '0' :: 'o' :: rest => natOfDigits? 8 rest
    | _ => natOfDigits? 10 cs
  match n? with
  | some n => if (n : Int) ≤ maxSafeInteger then some (n : Int) else none
  | none => none

/-- The literal an expression is, if it is one the optimizer computes
with. -/
def litOf? {c m : Nat} : Expr c m → Option Lit
  | .number raw => (intOfNumeral? raw.val).map .num
  | .string v => some (.str v)
  | .true_ => some (.bool true)
  | .false_ => some (.bool false)
  | .null => some .null
  | .unary .minus e =>
      match e with
      | .number raw => (intOfNumeral? raw.val).map fun v => .num (-v)
      | _ => none
  | _ => none

/-- The expression a literal value is written as; a negative number is a
literal with a unary minus, as JavaScript has no negative literal. -/
def exprOfLit {c m : Nat} : Lit → Expr c m
  | .num v =>
      if v < 0 then .unary .minus (.number (NEString.ofString! (toString (-v))))
      else .number (NEString.ofString! (toString v))
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
private def isAscii (s : String) : Bool := s.toList.all fun ch => ch.toNat < 128

/-! ## Purity

Whether evaluating an expression can be observed.  The answer is
conservative: everything that could run code — a call, a member access
(a getter), a template with a substitution (`toString`), `in` and
`instanceof` (a proxy) — is taken to have an effect. -/

mutual

/-- Whether an expression can be evaluated without an observable effect,
conservatively. -/
partial def Expr.isPure {c m : Nat} : Expr c m → Bool
  | .mutVar _ | .constVar _ | .unsafeGlobal _ => true
  | .number _ | .string _ | .regex _ | .null | .true_ | .false_ | .this => true
  | .array els => ArrayElems.isPure els
  | .object ps => Properties.isPure ps
  | .assign _ _ _ | .update _ _ _ => false
  | .await _ | .yield _ | .yieldFrom _ => false
  | .call _ _ | .new _ _ => false
  | .dot _ _ | .index _ _ => false
  | .classAnon _ _ | .classSelf _ _ => false
  | .seq a b => a.isPure && b.isPure
  | .binary a op b =>
      match op with
      | .inOp | .instanceOf => false
      | _ => a.isPure && b.isPure
  | .ternary a b d => a.isPure && b.isPure && d.isPure
  | .arrow _ _ | .func _ _ _ _ | .funcSelf _ _ _ _ => true
  | .spread _ => false
  | .template _ _ _ => false
  | .unary op e =>
      match op with
      | .delete | .preIncr | .preDecr => false
      | _ => e.isPure

/-- Whether every element of an array literal is pure. -/
partial def ArrayElems.isPure {c m : Nat} : ArrayElems c m → Bool
  | .nil => true
  | .cons .hole r => ArrayElems.isPure r
  | .cons (.elem e) r => e.isPure && ArrayElems.isPure r

/-- Whether every member of an object literal is pure. -/
partial def Properties.isPure {c m : Nat} : Properties c m → Bool
  | .nil => true
  | .cons (.keyValue k v) r => PropName.isPure k && v.isPure && Properties.isPure r
  | .cons (.method _ k _ _) r => PropName.isPure k && Properties.isPure r

/-- Whether the name of a property is pure. -/
partial def PropName.isPure {c m : Nat} : PropName c m → Bool
  | .ident _ | .string _ | .number _ => true
  | .computed e => e.isPure

end

/-- Whether an optional expression is pure. -/
def OptExpr.isPure {c m : Nat} : OptExpr c m → Bool
  | .none => true
  | .some e => e.isPure

/-- Whether the keys of a class body are pure, which is what decides
whether declaring the class has an effect (its methods are not run). -/
def ClassElems.keysArePure {c m : Nat} : ClassElems c m → Bool
  | .nil => true
  | .cons (.mk _ _ key _ _) r => PropName.isPure key && ClassElems.keysArePure r

/-! ## Folding an operator -/

/-- 32 bit two's complement, as `&`, `|`, `^` and the shifts use it. -/
private def toUint32 (v : Int) : Nat := (v % 4294967296).toNat

/-- The signed value of a 32 bit word. -/
private def ofUint32 (n : Nat) : Int :=
  if n ≥ 2147483648 then (n : Int) - 4294967296 else (n : Int)

/-- Whether an integer is one JavaScript represents exactly. -/
private def isSafe (v : Int) : Bool := v.natAbs ≤ maxSafeInteger.toNat

/-- The value of `a op b`, when it is one the optimizer computes. -/
def foldBinary (a : Lit) (op : MiniBinOp) (b : Lit) : Option Lit :=
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
def foldUnary (op : MiniUnaryOp) (a : Lit) : Option Lit :=
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
def typeofOf? {c m : Nat} : Expr c m → Option String
  | .arrow _ _ | .func _ _ _ _ | .funcSelf _ _ _ _
  | .classAnon _ _ | .classSelf _ _ => some "function"
  | e => (litOf? e).bind fun v => (foldUnary .typeof v).bind fun
      | .str s => some s
      | _ => none

/-! ## The pass

Every function rewrites a node into one of the same type, which is to say
in the same scope: what the optimizer produces is scope correct by
construction. -/

/-- What is to be done with a statement of a block. -/
inductive StmtOpt (c m dc dm : Nat) where
  /-- Keep it, rewritten. -/
  | keep (stmt : Stmt c m dc dm)
  /-- Drop it; it binds nothing, so the rest of the block stays in scope. -/
  | drop (hc : dc = 0) (hm : dm = 0)
  /-- Keep it, and drop everything that follows it in the block. -/
  | terminator (stmt : Stmt c m dc dm)

/-- A statement is one of the possible answers, which is what `optStmt`
needs for Lean to accept it as a `partial` definition. -/
instance {c m dc dm : Nat} [Inhabited (Stmt c m dc dm)] : Inhabited (StmtOpt c m dc dm) :=
  ⟨.keep default⟩

/-- The one statement of a block, when it has exactly one and it binds
nothing — in which case the block is the same thing as the statement. -/
def Block.single? {c m : Nat} : Block c m → Option (Stmt c m 0 0)
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
  | .cons (.labelled l s) .nil => some (.labelled l s)
  | .cons (.switch disc cases) .nil => some (.switch disc cases)
  | .cons (.try_ b tail) .nil => some (.try_ b tail)
  | _ => none

/-- Whether a statement transfers control, so that what follows it in its
block cannot be reached. -/
def Stmt.isTerminator {c m dc dm : Nat} : Stmt c m dc dm → Bool
  | .return_ _ | .throw _ | .break_ _ | .continue_ _ => true
  | _ => false

/-- What a block amounts to as a statement: nothing when it is empty, the
statement itself when it has exactly one that binds nothing, and a block
otherwise. -/
def blockAsStmt {c m : Nat} (b : Block c m) : StmtOpt c m 0 0 :=
  match b with
  | .nil => .drop rfl rfl
  | b =>
      match b.single? with
      | some s => if s.isTerminator then .terminator s else .keep s
      | none => .keep (.block b)

mutual

/-- Optimize an expression. -/
partial def optExpr {c m : Nat} (e : Expr c m) : Expr c m :=
  match e with
  | .mutVar i => .mutVar i
  | .constVar i => .constVar i
  | .unsafeGlobal n => .unsafeGlobal n
  | .number raw => .number raw
  | .string v => .string v
  | .regex raw => .regex raw
  | .null => .null
  | .true_ => .true_
  | .false_ => .false_
  | .this => .this
  | .array els => .array (optArrayElems els)
  | .object ps => .object (optProperties ps)
  | .assign t op rhs => .assign (optTarget t) op (optExpr rhs)
  | .update t op isPrefix => .update (optTarget t) op isPrefix
  | .await x => .await (optExpr x)
  | .call f args => .call (optExpr f) (optExprs args)
  | .new f args => .new (optExpr f) (optExprs args)
  | .dot o n => .dot (optExpr o) n
  | .index o i => .index (optExpr o) (optExpr i)
  | .classAnon her body => .classAnon (optOptExpr her) (optClassElems body)
  | .classSelf her body => .classSelf (optOptExpr her) (optClassElems body)
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
  | .arrow arity body => .arrow arity (optArrowBody body)
  | .func isAsync isGen arity body => .func isAsync isGen arity (optBlock body)
  | .funcSelf isAsync isGen arity body => .funcSelf isAsync isGen arity (optBlock body)
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
partial def optTarget {c m : Nat} : Target c m → Target c m
  | .mut i => .mut i
  | .unsafeGlobal n => .unsafeGlobal n
  | .dot o n => .dot (optExpr o) n
  | .index o i => .index (optExpr o) (optExpr i)

/-- Optimize a list of expressions. -/
partial def optExprs {c m : Nat} : Exprs c m → Exprs c m
  | .nil => .nil
  | .cons e r => .cons (optExpr e) (optExprs r)

/-- Optimize an optional expression. -/
partial def optOptExpr {c m : Nat} : OptExpr c m → OptExpr c m
  | .none => .none
  | .some e => .some (optExpr e)

/-- Optimize the elements of an array literal. -/
partial def optArrayElems {c m : Nat} : ArrayElems c m → ArrayElems c m
  | .nil => .nil
  | .cons .hole r => .cons .hole (optArrayElems r)
  | .cons (.elem e) r => .cons (.elem (optExpr e)) (optArrayElems r)

/-- Optimize the substitutions of a template literal. -/
partial def optTemplateParts {c m : Nat} : TemplateParts c m → TemplateParts c m
  | .nil => .nil
  | .cons (.mk e s) r => .cons (.mk (optExpr e) s) (optTemplateParts r)

/-- Optimize the name of a property. -/
partial def optPropName {c m : Nat} : PropName c m → PropName c m
  | .ident n => .ident n
  | .string v => .string v
  | .number raw => .number raw
  | .computed e => .computed (optExpr e)

/-- Optimize the members of an object literal. -/
partial def optProperties {c m : Nat} : Properties c m → Properties c m
  | .nil => .nil
  | .cons (.keyValue k v) r => .cons (.keyValue (optPropName k) (optExpr v)) (optProperties r)
  | .cons (.method kind k arity body) r =>
      .cons (.method kind (optPropName k) arity (optBlock body)) (optProperties r)

/-- Optimize the members of a class body. -/
partial def optClassElems {c m : Nat} : ClassElems c m → ClassElems c m
  | .nil => .nil
  | .cons (.mk isStatic kind k arity body) r =>
      .cons (.mk isStatic kind (optPropName k) arity (optBlock body)) (optClassElems r)

/-- Optimize the body of an arrow function. -/
partial def optArrowBody {c m : Nat} : ArrowBody c m → ArrowBody c m
  | .expr e => .expr (optExpr e)
  | .block b => .block (optBlock b)

/-- Optimize the first clause of a `for (;;)`. -/
partial def optForInit {c m dc dm : Nat} : ForInit c m dc dm → ForInit c m dc dm
  | .none => .none
  | .expr e => .expr (optExpr e)
  | .constDecl init => .constDecl (optExpr init)
  | .letDecl init => .letDecl (optOptExpr init)

/-- Optimize the binder of a `for (... of ...)`. -/
partial def optForHead {c m dc dm : Nat} : ForHead c m dc dm → ForHead c m dc dm
  | .target t => .target (optTarget t)
  | .constBind => .constBind
  | .letBind => .letBind

/-- Optimize the cases of a `switch`. -/
partial def optSwitchCases {c m : Nat} : SwitchCases c m → SwitchCases c m
  | .nil => .nil
  | .cons (.case t b) r => .cons (.case (optExpr t) (optBlock b)) (optSwitchCases r)
  | .cons (.default b) r => .cons (.default (optBlock b)) (optSwitchCases r)

/-- Optimize an optional block. -/
partial def optOptBlock {c m : Nat} : OptBlock c m → OptBlock c m
  | .none => .none
  | .some b => .some (optBlock b)

/-- Optimize what follows the block of a `try`. -/
partial def optTryTail {c m : Nat} : TryTail c m → TryTail c m
  | .catch_ body fin => .catch_ (optBlock body) (optOptBlock fin)
  | .finallyOnly b => .finallyOnly (optBlock b)

/-- Optimize a statement, and say whether it can be dropped, or makes the
statements that follow it unreachable. -/
partial def optStmt {c m dc dm : Nat} (s : Stmt c m dc dm) : StmtOpt c m dc dm :=
  match s with
  | .expr e =>
      let e := optExpr e
      if e.isPure then .drop rfl rfl else .keep (.expr e)
  | .constDecl init => .keep (.constDecl (optExpr init))
  | .letDecl init => .keep (.letDecl (optOptExpr init))
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
  | .funcDecl isAsync isGen arity body =>
      .keep (.funcDecl isAsync isGen arity (optBlock body))
  | .classDecl her body => .keep (.classDecl (optOptExpr her) (optClassElems body))
  | .return_ e => .terminator (.return_ (optOptExpr e))
  | .throw e => .terminator (.throw (optExpr e))
  | .break_ l => .terminator (.break_ l)
  | .continue_ l => .terminator (.continue_ l)
  | .labelled l s' =>
      match optStmt s' with
      | .keep s'' => .keep (.labelled l s'')
      | .terminator s'' => .keep (.labelled l s'')
      | .drop _ _ => .drop rfl rfl
  | .switch disc cases => .keep (.switch (optExpr disc) (optSwitchCases cases))
  | .try_ b tail => .keep (.try_ (optBlock b) (optTryTail tail))

/-- Optimize a block: every statement, dropping the ones without effect,
the bindings nothing uses, and everything after a statement that transfers
control. -/
partial def optBlock {c m : Nat} : Block c m → Block c m
  | .nil => .nil
  | .cons hd tl =>
      match optStmt hd with
      | .drop hc hm => optBlock (tl.castScope (by omega) (by omega))
      | .terminator s => .cons s .nil
      | .keep s =>
          match s, tl with
          | .constDecl init, tl =>
              let rest := optBlock tl
              dropUnusedConst (.constDecl init) init.isPure rest
          | .letDecl init, tl =>
              let rest := optBlock tl
              dropUnusedMut (.letDecl init) init.isPure rest
          | .funcDecl isAsync isGen arity body, tl =>
              let rest := optBlock tl
              dropUnusedConst (.funcDecl isAsync isGen arity body) true rest
          | .classDecl her body, tl =>
              let rest := optBlock tl
              dropUnusedConst (.classDecl her body)
                (match her with | .none => body.keysArePure | .some _ => false) rest
          | s, tl => .cons s (optBlock tl)

/-- Drop a statement that binds one const variable, when defining it has no
effect and the rest of the block does not use it. -/
partial def dropUnusedConst {c m : Nat} (s : Stmt c m 1 0) (defPure : Bool) (rest : Block (c + 1) m) :
    Block c m :=
  if defPure then
    match strengthenConstBlock 0 rest with
    | some b => b
    | none => .cons s rest
  else .cons s rest

/-- Drop a statement that binds one mutable variable, when its initializer
has no effect and the rest of the block does not use it. -/
partial def dropUnusedMut {c m : Nat} (s : Stmt c m 0 1) (defPure : Bool) (rest : Block c (m + 1)) :
    Block c m :=
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
def optModuleItem {c m dc dm : Nat} (it : ModuleItem c m dc dm) : ModuleItem c m dc dm :=
  match it with
  | .stmt s =>
      match optStmt s with
      | .keep s' => .stmt s'
      | .terminator s' => .stmt s'
      | .drop _ _ => .stmt s
  | .importBare mod => .importBare mod
  | .importClause clause => .importClause clause
  | .exportFrom specs mod => .exportFrom specs mod
  | .exportLocals specs => .exportLocals specs
  | .exportDecl s =>
      match optStmt s with
      | .keep s' => .exportDecl s'
      | .terminator s' => .exportDecl s'
      | .drop _ _ => .exportDecl s

/-- Optimize the top level items.  A statement without effect is dropped
here too, but nothing that *follows* one is: a module is not left by a
`return`, and an `export` is never dropped. -/
partial def optModuleItems {c m : Nat} : ModuleItems c m → ModuleItems c m
  | .nil => .nil
  | .cons it r =>
      match it with
      | .stmt s =>
          match optStmt s with
          | .keep s' => .cons (.stmt s') (optModuleItems r)
          | .terminator s' => .cons (.stmt s') (optModuleItems r)
          | .drop hc hm => optModuleItems (r.castScope (by omega) (by omega))
      | it => .cons (optModuleItem it) (optModuleItems r)

/-- Optimize a program: one bottom up pass. -/
def optimizeProgram (p : Program) : Program := ⟨optModuleItems p.items⟩

/-- Optimize an expression: one bottom up pass. -/
def optimizeExpr {c m : Nat} (e : Expr c m) : Expr c m := optExpr e

/-- Optimize a block of statements: one bottom up pass. -/
def optimizeBlock {c m : Nat} (b : Block c m) : Block c m := optBlock b

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
