/-
Conversion of the deterministic `MiniAST` into the scope safe `BrujinAST`.
-/
import LanguageJavascriptBrujin.AST
import LanguageJavascriptMini.OfFull

namespace Language.JavaScript.BrujinAST

open Language.JavaScript.MiniAST

structure Binding where
  name : NEString
  isConst : Bool
  level : Nat
deriving Repr, Inhabited

abbrev Env := List Binding

namespace Env

def lookup (env : Env) (n : NEString) : Option Binding :=
  env.find? fun b => b.name.val == n.val

def pushConsts (env : Env) (c : Nat) (names : List NEString) : Env :=
  (names.zipIdx.map fun (n, j) => ⟨n, true, c + j⟩).reverse ++ env

def pushMuts (env : Env) (m : Nat) (names : List NEString) : Env :=
  (names.zipIdx.map fun (n, j) => ⟨n, false, m + j⟩).reverse ++ env

end Env

/-- Resolvers for free variable names and assignment targets encountered during conversion. -/
structure Resolvers (exprExt targetExt : Nat → Nat → Type) where
  /-- Resolve a free name in expression position into an extension node. -/
  resolveFree : (c m : Nat) → NEString → Except String (exprExt c m)
  /-- Resolve a free name in assignment target position into a target extension node. -/
  resolveFreeTarget : (c m : Nat) → NEString → Except String (targetExt c m) :=
    fun _ _ n => .error s!"assignment to unknown global: {n.val}"

/-- The conversion monad, carrying the free identifier resolvers. -/
abbrev ConvM (exprExt targetExt : Nat → Nat → Type) (α : Type) :=
  ReaderT (Resolvers exprExt targetExt) (Except String) α

/-- The result of a conversion. -/
abbrev ResM := Except String

variable {exprExt targetExt : Nat → Nat → Type}

def fail (msg : String) : ConvM exprExt targetExt α := throw ("BrujinAST: " ++ msg)

/-- A name the tree does not bind: the escape hatch, resolved via `resolveFree`. -/
def freeName (c m : Nat) (n : NEString) : ConvM exprExt targetExt (Expr exprExt targetExt c m) := do
  let ctx ← read
  match ctx.resolveFree c m n with
  | .ok ext => pure (.unsafeExt ext)
  | .error e => fail e

/-- The same, for the left hand side of an assignment: resolved via `resolveFreeTarget`. -/
def freeTarget (c m : Nat) (n : NEString) : ConvM exprExt targetExt (Target exprExt targetExt c m) := do
  let ctx ← read
  match ctx.resolveFreeTarget c m n with
  | .ok ext => pure (.unsafeExt ext)
  | .error e => fail e

def resolveVar (env : Env) (c m : Nat) (n : NEString) : ConvM exprExt targetExt (Expr exprExt targetExt c m) :=
  match idxIdent? n with
  | some (true, i) =>
      if h : i < c then pure (.constVar ⟨i, h⟩)
      else fail s!"the de Bruijn index c#{i} is out of range: {c} const bindings are in scope"
  | some (false, i) =>
      if h : i < m then pure (.mutVar ⟨i, h⟩)
      else fail s!"the de Bruijn index l#{i} is out of range: {m} mutable bindings are in scope"
  | none =>
    match env.lookup n with
    | none => freeName c m n
    | some b =>
        if b.isConst then
          match constIndex? c b.level with
          | some i => pure (.constVar i)
          | none => freeName c m n
        else
          match mutIndex? m b.level with
          | some i => pure (.mutVar i)
          | none => freeName c m n

def resolveTarget (env : Env) (c m : Nat) (n : NEString) : ConvM exprExt targetExt (Target exprExt targetExt c m) :=
  match idxIdent? n with
  | some (true, i) => fail s!"assignment to the const variable c#{i}"
  | some (false, i) =>
      if h : i < m then pure (.mut ⟨i, h⟩)
      else fail s!"the de Bruijn index l#{i} is out of range: {m} mutable bindings are in scope"
  | none =>
    match env.lookup n with
    | none => freeTarget c m n
    | some b =>
        if b.isConst then
          fail s!"assignment to the const variable {n.val}"
        else
          match mutIndex? m b.level with
          | some i => pure (.mut i)
          | none => freeTarget c m n

def resolveExportLocal (env : Env) (c m : Nat) (n exported : NEString) :
    ConvM exprExt targetExt (ExportLocal exprExt targetExt c m) :=
  match idxIdent? n with
  | some (true, i) =>
      if h : i < c then pure (.const ⟨i, h⟩ exported)
      else fail s!"the de Bruijn index c#{i} is out of range: {c} const bindings are in scope"
  | some (false, i) =>
      if h : i < m then pure (.mut ⟨i, h⟩ exported)
      else fail s!"the de Bruijn index l#{i} is out of range: {m} mutable bindings are in scope"
  | none =>
    match env.lookup n with
    | none => fail s!"export of the unbound name {n.val}"
    | some b =>
        if b.isConst then
          match constIndex? c b.level with
          | some i => pure (.const i exported)
          | none => fail s!"export of the out of scope name {n.val}"
        else
          match mutIndex? m b.level with
          | some i => pure (.mut i exported)
          | none => fail s!"export of the out of scope name {n.val}"

/-- The name a binding pattern binds.  `BrujinAST` has a binder for a plain
name only, so a destructuring pattern and a default value are refused. -/
def binderName : MiniPattern → ConvM exprExt targetExt NEString
  | .ident n => pure n
  | .array _ | .object _ _ => fail "a destructuring pattern in a binder"
  | .withDefault _ _ => fail "a default value in a binder"
  | .target _ => fail "a binder that is not a name"

/-- The name a parameter binds.  `BrujinAST` has a binder for a plain name
only, so a default value and a destructuring pattern are refused; a rest
parameter binds a name like any other, and the tree records that it is one.
-/
def paramBinderName : MiniParam → ConvM exprExt targetExt NEString
  | .plain p | .rest p =>
    match p with
    | .ident n => pure n
    | .array _ | .object _ _ => fail "a destructuring pattern in a parameter"
    | .withDefault _ _ => fail "a default value in a parameter"
    | .target _ => fail "a parameter that is not a name"

/-- The parameters of a function: the names they bind, in source order,
together with how the tree records them — `arity` ordinary parameters
followed by a rest parameter if `hasRest`. -/
structure ParamsRes where
  /-- The name each parameter binds, the rest parameter included. -/
  names : List NEString
  /-- The number of ordinary parameters. -/
  arity : Nat
  /-- Whether a rest parameter follows them. -/
  hasRest : Bool
  /-- One name is bound per parameter. -/
  len : names.length = arity + hasRest.toNat

/-- Whether a parameter is a rest parameter. -/
def isRestParam : MiniParam → Bool
  | .rest _ => true
  | _ => false

/-- Read the parameters of a function.  A rest parameter is accepted where
JavaScript allows one, which is nowhere but last. -/
def paramsOf (params : List MiniParam) : ConvM exprExt targetExt ParamsRes := do
  if params.dropLast.any isRestParam then
    fail "a rest parameter which is not the last one"
  else
    let v : Vector MiniParam params.length := ⟨params.toArray, by simp⟩
    let names ← v.mapM paramBinderName
    match hp : params.getLast? with
    | some (.rest _) =>
        have h0 : 0 < params.length := by
          cases params with
          | nil => simp at hp
          | cons _ t => simp
        pure ⟨names.toList, params.length - 1, true, by simp; omega⟩
    | _ => pure ⟨names.toList, params.length, false, by simp⟩

structure StmtRes (exprExt targetExt : Nat → Nat → Type) (c m : Nat) where
  dc : Nat
  dm : Nat
  stmt : Stmt exprExt targetExt c m dc dm
  binds : List Binding

structure ItemRes (exprExt targetExt : Nat → Nat → Type) (c m : Nat) where
  dc : Nat
  dm : Nat
  item : ModuleItem exprExt targetExt c m dc dm
  binds : List Binding

/-! ## Putting a declarator in front of what follows it

A `var`/`let`/`const` statement with several declarators becomes one
`BrujinAST` statement per declarator, since each of them binds.  This used
to be done by rewriting the *list* of statements before converting it,
which is what cost this module its structural recursion: the rewritten list
is not a component of anything, so the conversion of a block could not be
seen to recurse on the block.

It is now done in place, by `ofDeclThenBlock` (and `ofDeclThenItems` for the
top level), which converts one declarator and
then calls the continuation it is given for whatever follows it — the part
of the program that sees the new binding.  What the declarator and the
continuation produce is put together by the two functions below, which is
all that differs between the three places a declaration can occur: inside a
block, at the top level, and after an `export`. -/

/-- What a declarator declares: a `var`, a `let` or a `const`, or a
`using`/`await using`.  A `using` binding cannot be assigned to, so — like
a `const` — it is a const binding. -/
inductive DeclKind where
  /-- `var`, `let` or `const`. -/
  | var_ (kind : VarKind)
  /-- `using` (`isAwait = false`) or `await using`. -/
  | using_ (isAwait : Bool)
deriving Repr, Inhabited

/-- A `const` declarator in front of the rest of a block. -/
def blockConsConst (c m : Nat) (init : Expr exprExt targetExt c m) (tl : Block exprExt targetExt (c + 1) m) : Block exprExt targetExt c m :=
  .cons (.constDecl init) tl

/-- A `using` declarator in front of the rest of a block. -/
def blockConsUsing (c m : Nat) (isAwait : Bool) (init : Expr exprExt targetExt c m)
    (tl : Block exprExt targetExt (c + 1) m) : Block exprExt targetExt c m :=
  .cons (.usingDecl isAwait init) tl

/-- A `let`/`var` declarator in front of the rest of a block. -/
def blockConsLet (c m : Nat) (init : OptExpr exprExt targetExt c m) (tl : Block exprExt targetExt c (m + 1)) : Block exprExt targetExt c m :=
  .cons (.letDecl init) tl

/-- A `const` declarator in front of the rest of the top level; `exported`
says whether it is written after an `export`. -/
def itemsConsConst (exported : Bool) (c m : Nat) (init : Expr exprExt targetExt c m)
    (tl : ModuleItems exprExt targetExt (c + 1) m) : ModuleItems exprExt targetExt c m :=
  if exported then .cons (.exportDecl (.constDecl init)) tl
  else .cons (.stmt (.constDecl init)) tl

/-- A `using` declarator in front of the rest of the top level. -/
def itemsConsUsing (exported : Bool) (isAwait : Bool) (c m : Nat) (init : Expr exprExt targetExt c m)
    (tl : ModuleItems exprExt targetExt (c + 1) m) : ModuleItems exprExt targetExt c m :=
  if exported then .cons (.exportDecl (.usingDecl isAwait init)) tl
  else .cons (.stmt (.usingDecl isAwait init)) tl

/-- A `let`/`var` declarator in front of the rest of the top level. -/
def itemsConsLet (exported : Bool) (c m : Nat) (init : OptExpr exprExt targetExt c m)
    (tl : ModuleItems exprExt targetExt c (m + 1)) : ModuleItems exprExt targetExt c m :=
  if exported then .cons (.exportDecl (.letDecl init)) tl
  else .cons (.stmt (.letDecl init)) tl

/-! ## The conversion

Every function below recurses on a component of its argument, so the block
is *structurally* recursive: it has equations, it reduces in the kernel and
it can be reasoned about, rather than being `partial` and opaque.

Three things had to be arranged for that.  Every `mapM` of a conversion is
spelled out as a function of the same block, walking the list it is given.
A declaration of several variables is converted in place (`ofDeclThenBlock`
above) rather than by rewriting the statement list first.  And the body of
an `if`, a loop or a `for`, which is a *statement* where a block is wanted,
is converted by `ofBody`, which takes the conversion of that statement as
its last argument: the caller has it as a component of the node it is
looking at, so passing it keeps every recursive call on a component. -/

mutual

/-- Convert an expression. -/
def ofExpr (env : Env) (c m : Nat) (e : MiniExpr) : ConvM exprExt targetExt (Expr exprExt targetExt c m) := do
  match e with
  | .ident n => resolveVar env c m n
  | .number n => pure (.number n)
  | .string v => pure (.string v)
  | .regex r => pure (.regex r)
  | .null => pure .null
  | .true_ => pure .true_
  | .false_ => pure .false_
  | .this => pure .this
  | .superDot n => pure (.superDot n)
  | .superIndex i => pure (.superIndex (← ofExpr env c m i))
  | .superCall args => pure (.superCall (← ofExprs env c m args))
  | .newTarget => pure .newTarget
  | .array els => pure (.array (← ofArrayElems env c m els))
  | .object ps => pure (.object (← ofProperties env c m ps))
  | .assign lhs op rhs =>
      pure (.assign (← ofTarget env c m lhs) op (← ofExpr env c m rhs))
  | .assignPattern lhs rhs =>
      pure (.assign (← ofPatternTarget env c m lhs) .assign (← ofExpr env c m rhs))
  | .postfix x op => pure (.update (← ofTarget env c m x) op false)
  | .unary op x =>
      match op with
      | .preIncr => pure (.update (← ofTarget env c m x) .incr true)
      | .preDecr => pure (.update (← ofTarget env c m x) .decr true)
      | _ => pure (.unary op (← ofExpr env c m x))
  | .await x => pure (.await (← ofExpr env c m x))
  | .call f args => pure (.call (← ofExpr env c m f) (← ofExprs env c m args))
  | .new f args => pure (.new (← ofExpr env c m f) (← ofExprs env c m args))
  | .dot o n => pure (.dot (← ofExpr env c m o) n)
  | .index o i => pure (.index (← ofExpr env c m o) (← ofExpr env c m i))
  | .privateDot o n => pure (.privateDot (← ofExpr env c m o) n)
  | .privateName n => pure (.privateName n)
  | .chain base links =>
      pure (.chain (← ofExpr env c m base) (← ofChainLink env c m links.hd)
        (← ofChainLinks env c m links.tl))
  | .importMeta => pure .importMeta
  | .importCall spec opts =>
      pure (.importCall (← ofExpr env c m spec) (← ofOptExpr env c m opts))
  | .classExpr decorators name heritage body =>
      -- the decorators are evaluated outside the class, so they do not see
      -- the name the class binds in its own body
      let ds ← ofExprs env c m decorators
      let her ← ofOptExpr env c m heritage
      match name with
      | none => pure (.classAnon ds her (← ofClassElems env c m body))
      | some n =>
          pure (.classSelf ds her (← ofClassElems (env.pushConsts c [n]) (c + 1) m body))
  | .seq a b => pure (.seq (← ofExpr env c m a) (← ofExpr env c m b))
  | .binary a op b => pure (.binary (← ofExpr env c m a) op (← ofExpr env c m b))
  | .ternary a b d =>
      pure (.ternary (← ofExpr env c m a) (← ofExpr env c m b) (← ofExpr env c m d))
  | .arrow params body =>
      let ps ← paramsOf params
      let inner := env.pushMuts m ps.names
      match body with
      | .expr x =>
          pure (.arrow ps.arity ps.hasRest (.expr (← ofExpr inner c (m + ps.arity + ps.hasRest.toNat) x)))
      | .block b =>
          pure (.arrow ps.arity ps.hasRest (.block (← ofStmts inner c (m + ps.arity + ps.hasRest.toNat) b)))
  | .func isAsync isGen name params body =>
      let ps ← paramsOf params
      match name with
      | none =>
          let inner := env.pushMuts m ps.names
          pure (.func isAsync isGen ps.hasRest ps.arity
            (← ofStmts inner c (m + ps.arity + ps.hasRest.toNat) body))
      | some n =>
          let inner := (env.pushConsts c [n]).pushMuts m ps.names
          pure (.funcSelf isAsync isGen ps.hasRest ps.arity
            (← ofStmts inner (c + 1) (m + ps.arity + ps.hasRest.toNat) body))
  | .spread x => pure (.spread (← ofExpr env c m x))
  | .template tag head parts =>
      pure (.template (← ofOptExpr env c m tag) head (← ofTemplateParts env c m parts))
  | .yield x => pure (.yield (← ofOptExpr env c m x))
  | .yieldFrom x => pure (.yieldFrom (← ofExpr env c m x))
termination_by structural e

/-- Convert an expression which may be absent. -/
def ofOptExpr (env : Env) (c m : Nat) : Option MiniExpr → ConvM exprExt targetExt (OptExpr exprExt targetExt c m)
  | none => pure .none
  | some e => do pure (.some (← ofExpr env c m e))
termination_by structural x => x

/-- Convert a list of expressions. -/
def ofExprs (env : Env) (c m : Nat) : List MiniExpr → ConvM exprExt targetExt (Exprs exprExt targetExt c m)
  | [] => pure .nil
  | e :: rest => do pure (.cons (← ofExpr env c m e) (← ofExprs env c m rest))
termination_by structural x => x

/-- Convert the left hand side of an assignment. -/
def ofTarget (env : Env) (c m : Nat) (e : MiniExpr) : ConvM exprExt targetExt (Target exprExt targetExt c m) := do
  match e with
  | .ident n => resolveTarget env c m n
  | .dot o n => pure (.dot (← ofExpr env c m o) n)
  | .index o i => pure (.index (← ofExpr env c m o) (← ofExpr env c m i))
  | .superDot n => pure (.superDot n)
  | .superIndex i => pure (.superIndex (← ofExpr env c m i))
  | _ => fail "an assignment target that is not a variable or a member"
termination_by structural e

/-- Convert the left hand side of an assignment written as a pattern.  A
destructuring pattern and a default value are refused, so what is left is a
name or a member access. -/
def ofPatternTarget (env : Env) (c m : Nat) (p : MiniPattern) : ConvM exprExt targetExt (Target exprExt targetExt c m) := do
  match p with
  | .ident n => resolveTarget env c m n
  | .target e => ofTarget env c m e
  | .array _ | .object _ _ => fail "a destructuring pattern in an assignment"
  | .withDefault _ _ => fail "a default value in an assignment target"
termination_by structural p

/-- Convert one link of an optional chain. -/
def ofChainLink (env : Env) (c m : Nat) : MiniChainLink → ConvM exprExt targetExt (ChainLink exprExt targetExt c m)
  | .dot opt n => pure (.dot opt n)
  | .privateDot opt n => pure (.privateDot opt n)
  | .index opt i => do pure (.index opt (← ofExpr env c m i))
  | .call opt args => do pure (.call opt (← ofExprs env c m args))
termination_by structural x => x

/-- Convert the links of an optional chain. -/
def ofChainLinks (env : Env) (c m : Nat) : List MiniChainLink → ConvM exprExt targetExt (ChainLinks exprExt targetExt c m)
  | [] => pure .nil
  | l :: rest => do
      pure (.cons (← ofChainLink env c m l) (← ofChainLinks env c m rest))
termination_by structural x => x

/-- Convert an element of an array literal. -/
def ofArrayElem (env : Env) (c m : Nat) : MiniArrayElement → ConvM exprExt targetExt (ArrayElem exprExt targetExt c m)
  | .hole => pure .hole
  | .elem e => do pure (.elem (← ofExpr env c m e))
termination_by structural x => x

/-- Convert the elements of an array literal. -/
def ofArrayElems (env : Env) (c m : Nat) : List MiniArrayElement → ConvM exprExt targetExt (ArrayElems exprExt targetExt c m)
  | [] => pure .nil
  | el :: rest => do
      pure (.cons (← ofArrayElem env c m el) (← ofArrayElems env c m rest))
termination_by structural x => x

/-- Convert the substitutions of a template literal. -/
def ofTemplateParts (env : Env) (c m : Nat) :
    List MiniTemplatePart → ConvM exprExt targetExt (TemplateParts exprExt targetExt c m)
  | [] => pure .nil
  | ⟨e, suffix⟩ :: rest => do
      pure (.cons (.mk (← ofExpr env c m e) suffix) (← ofTemplateParts env c m rest))
termination_by structural x => x

/-- Convert the name of a property. -/
def ofPropName (env : Env) (c m : Nat) : MiniPropertyName → ConvM exprExt targetExt (PropName exprExt targetExt c m)
  | .ident n => pure (.ident n)
  | .private_ n => pure (.private_ n)
  | .string v => pure (.string v)
  | .number n => pure (.number n)
  | .computed e => do pure (.computed (← ofExpr env c m e))
termination_by structural x => x

/-- Convert a member of an object literal. -/
def ofProperty (env : Env) (c m : Nat) : MiniProperty → ConvM exprExt targetExt (Property exprExt targetExt c m)
  | .keyValue k v => do pure (.keyValue (← ofPropName env c m k) (← ofExpr env c m v))
  | .shorthand n => do pure (.keyValue (.ident n) (← resolveVar env c m n))
  | .spread e => do pure (.spread (← ofExpr env c m e))
  | .method kind k params body => do
      let ps ← paramsOf params
      pure (.method kind (← ofPropName env c m k) ps.arity ps.hasRest
        (← ofStmts (env.pushMuts m ps.names) c (m + ps.arity + ps.hasRest.toNat) body))
termination_by structural x => x

/-- Convert the members of an object literal. -/
def ofProperties (env : Env) (c m : Nat) : List MiniProperty → ConvM exprExt targetExt (Properties exprExt targetExt c m)
  | [] => pure .nil
  | p :: rest => do pure (.cons (← ofProperty env c m p) (← ofProperties env c m rest))
termination_by structural x => x

/-- Convert a member of a class body. -/
def ofClassElem (env : Env) (c m : Nat) : MiniClassElement → ConvM exprExt targetExt (ClassElem exprExt targetExt c m)
  | .method decorators isStatic kind key params body => do
      let ps ← paramsOf params
      pure (.method (← ofExprs env c m decorators) isStatic kind (← ofPropName env c m key)
        ps.arity ps.hasRest
        (← ofStmts (env.pushMuts m ps.names) c (m + ps.arity + ps.hasRest.toNat) body))
  | .field decorators isStatic key init => do
      pure (.field (← ofExprs env c m decorators) isStatic (← ofPropName env c m key)
        (← ofOptExpr env c m init))
  | .staticBlock body => do pure (.staticBlock (← ofStmts env c m body))
termination_by structural x => x

/-- Convert a class body. -/
def ofClassElems (env : Env) (c m : Nat) :
    List MiniClassElement → ConvM exprExt targetExt (ClassElems exprExt targetExt c m)
  | [] => pure .nil
  | el :: rest => do
      pure (.cons (← ofClassElem env c m el) (← ofClassElems env c m rest))
termination_by structural x => x

/-- Convert one `case`/`default` of a `switch`. -/
def ofSwitchCase (env : Env) (c m : Nat) : MiniSwitchCase → ConvM exprExt targetExt (SwitchCase exprExt targetExt c m)
  | .case t b => do pure (.case (← ofExpr env c m t) (← ofStmts env c m b))
  | .default b => do pure (.default (← ofStmts env c m b))
termination_by structural x => x

/-- Convert the cases of a `switch`. -/
def ofSwitchCases (env : Env) (c m : Nat) :
    List MiniSwitchCase → ConvM exprExt targetExt (SwitchCases exprExt targetExt c m)
  | [] => pure .nil
  | k :: rest => do
      pure (.cons (← ofSwitchCase env c m k) (← ofSwitchCases env c m rest))
termination_by structural x => x

/-- Convert one declarator of a `var`/`let`/`const` inside a block, then
whatever follows it, in the scope the declarator extends. -/
def ofDeclThenBlock (kind : DeclKind) (d : MiniDeclarator) (env : Env) (c m : Nat)
    (kont : (env : Env) → (c' m' : Nat) → ConvM exprExt targetExt (Block exprExt targetExt c' m')) : ConvM exprExt targetExt (Block exprExt targetExt c m) :=
  match d with
  | ⟨lhs, init⟩ =>
      match kind with
      | .using_ isAwait =>
          match init with
          | none => do
              let _ ← binderName lhs
              fail "a `using` declaration without an initialiser"
          | some i => do
              let n ← binderName lhs
              let i' ← ofExpr env c m i
              let tl ← kont (⟨n, true, c⟩ :: env) (c + 1) m
              pure (blockConsUsing c m isAwait i' tl)
      | .var_ .const =>
          match init with
          | none => do
              let _ ← binderName lhs
              fail "a const declaration without an initialiser"
          | some i => do
              let n ← binderName lhs
              let i' ← ofExpr env c m i
              let tl ← kont (⟨n, true, c⟩ :: env) (c + 1) m
              pure (blockConsConst c m i' tl)
      | _ => do
          let n ← binderName lhs
          let i' ← ofOptExpr env c m init
          let tl ← kont (⟨n, false, m⟩ :: env) c (m + 1)
          pure (blockConsLet c m i' tl)
termination_by structural d

/-- Convert the remaining declarators of a `var`/`let`/`const` inside a
block, then whatever follows them. -/
def ofDeclsThenBlock (kind : DeclKind) (ds : List MiniDeclarator) (env : Env) (c m : Nat)
    (kont : (env : Env) → (c' m' : Nat) → ConvM exprExt targetExt (Block exprExt targetExt c' m')) : ConvM exprExt targetExt (Block exprExt targetExt c m) := do
  match ds with
  | [] => kont env c m
  | d :: ds =>
      ofDeclThenBlock kind d env c m fun env c m =>
        ofDeclsThenBlock kind ds env c m kont
termination_by structural ds

/-- Convert one declarator of a top level `var`/`let`/`const`, then
whatever follows it. -/
def ofDeclThenItems (exported : Bool) (kind : DeclKind) (d : MiniDeclarator)
    (env : Env) (c m : Nat)
    (kont : (env : Env) → (c' m' : Nat) → ConvM exprExt targetExt (ModuleItems exprExt targetExt c' m')) :
    ConvM exprExt targetExt (ModuleItems exprExt targetExt c m) := do
  match d with
  | ⟨lhs, init⟩ =>
      let n ← binderName lhs
      match kind with
      | .using_ isAwait =>
          match init with
          | none => fail "a `using` declaration without an initialiser"
          | some i =>
              let i' ← ofExpr env c m i
              let tl ← kont (⟨n, true, c⟩ :: env) (c + 1) m
              pure (itemsConsUsing exported isAwait c m i' tl)
      | .var_ .const =>
          match init with
          | none => fail "a const declaration without an initialiser"
          | some i =>
              let i' ← ofExpr env c m i
              let tl ← kont (⟨n, true, c⟩ :: env) (c + 1) m
              pure (itemsConsConst exported c m i' tl)
      | _ =>
          let i' ← ofOptExpr env c m init
          let tl ← kont (⟨n, false, m⟩ :: env) c (m + 1)
          pure (itemsConsLet exported c m i' tl)

/-- Convert the remaining declarators of a top level `var`/`let`/`const`,
then whatever follows them. -/
def ofDeclsThenItems (exported : Bool) (kind : DeclKind) (ds : List MiniDeclarator)
    (env : Env) (c m : Nat)
    (kont : (env : Env) → (c' m' : Nat) → ConvM exprExt targetExt (ModuleItems exprExt targetExt c' m')) :
    ConvM exprExt targetExt (ModuleItems exprExt targetExt c m) := do
  match ds with
  | [] => kont env c m
  | d :: ds =>
      ofDeclThenItems exported kind d env c m fun env c m =>
        ofDeclsThenItems exported kind ds env c m kont
termination_by structural ds

/-- Convert the statements of a block.  An empty statement disappears and a
declaration of several variables becomes one statement per declarator, as
in the deterministic tree's own reading of a block. -/
def ofStmts (env : Env) (c m : Nat) : List MiniStatement → ConvM exprExt targetExt (Block exprExt targetExt c m)
  | [] => pure .nil
  | .empty :: rest => ofStmts env c m rest
  | .decl kind ⟨d, ds⟩ :: rest =>
      ofDeclThenBlock (.var_ kind) d env c m fun env c m =>
        ofDeclsThenBlock (.var_ kind) ds env c m fun env c m =>
          ofStmts env c m rest
  | .using_ isAwait ⟨d, ds⟩ :: rest =>
      ofDeclThenBlock (.using_ isAwait) d env c m fun env c m =>
        ofDeclsThenBlock (.using_ isAwait) ds env c m fun env c m =>
          ofStmts env c m rest
  | s :: rest => do
      let r ← ofStmt env c m s
      let tl ← ofStmts (r.binds.reverse ++ env) (c + r.dc) (m + r.dm) rest
      pure (.cons r.stmt tl)
termination_by structural x => x

/-- The body of an `if`, a loop or a `for`, as a block.  `self` is the
conversion of `s` as a statement, which only the last case needs; the
caller passes it because `s` is a component of the node it is converting,
so that this stays a recursion on components. -/
def ofBody (env : Env) (c m : Nat) (s : MiniStatement)
    (self : ConvM exprExt targetExt (StmtRes exprExt targetExt c m)) : ConvM exprExt targetExt (Block exprExt targetExt c m) :=
  match s with
  | .block b => ofStmts env c m b
  | .empty => pure .nil
  | .decl kind ⟨d, ds⟩ =>
      ofDeclThenBlock (.var_ kind) d env c m fun env c m =>
        ofDeclsThenBlock (.var_ kind) ds env c m fun _ _ _ => pure .nil
  | .using_ isAwait ⟨d, ds⟩ =>
      ofDeclThenBlock (.using_ isAwait) d env c m fun env c m =>
        ofDeclsThenBlock (.using_ isAwait) ds env c m fun _ _ _ => pure .nil
  | _ => do
      let r ← self
      pure (.cons r.stmt .nil)
termination_by structural s

/-- Convert a statement, together with what it binds. -/
def ofStmt (env : Env) (c m : Nat) (s : MiniStatement) : ConvM exprExt targetExt (StmtRes exprExt targetExt c m) := do
  match s with
  | .expr e => return ⟨0, 0, .expr (← ofExpr env c m e), []⟩
  | .empty => return ⟨0, 0, .block .nil, []⟩
  | .decl kind ⟨⟨lhs, init⟩, ds⟩ =>
      match ds with
      | _ :: _ => fail "a declaration of several variables (it should have been split)"
      | [] =>
        let n ← binderName lhs
        match kind with
        | .const =>
            match init with
            | none => fail "a const declaration without an initialiser"
            | some i => return ⟨1, 0, .constDecl (← ofExpr env c m i), [⟨n, true, c⟩]⟩
        | _ => return ⟨0, 1, .letDecl (← ofOptExpr env c m init), [⟨n, false, m⟩]⟩
  | .using_ isAwait ⟨⟨lhs, init⟩, ds⟩ =>
      match ds with
      | _ :: _ => fail "a `using` declaration of several variables (it should have been split)"
      | [] =>
        let n ← binderName lhs
        match init with
        | none => fail "a `using` declaration without an initialiser"
        | some i => return ⟨1, 0, .usingDecl isAwait (← ofExpr env c m i), [⟨n, true, c⟩]⟩
  | .block b => return ⟨0, 0, .block (← ofStmts env c m b), []⟩
  | .if_ cond t e =>
      let cond' ← ofExpr env c m cond
      let tb ← ofBody env c m t (ofStmt env c m t)
      let eb : OptBlock exprExt targetExt c m ←
        match e with
        | none => pure .none
        | some s => do pure (.some (← ofBody env c m s (ofStmt env c m s)))
      return ⟨0, 0, .if_ cond' tb eb, []⟩
  | .while_ cond b =>
      return ⟨0, 0, .while_ (← ofExpr env c m cond) (← ofBody env c m b (ofStmt env c m b)), []⟩
  | .doWhile b cond =>
      return ⟨0, 0, .doWhile (← ofBody env c m b (ofStmt env c m b)) (← ofExpr env c m cond), []⟩
  | .for_ init cond step body =>
      match init with
      | .none =>
          return ⟨0, 0, .for_ .none (← ofOptExpr env c m cond) (← ofOptExpr env c m step)
            (← ofBody env c m body (ofStmt env c m body)), []⟩
      | .expr e =>
          let e' ← ofExpr env c m e
          return ⟨0, 0, .for_ (.expr e') (← ofOptExpr env c m cond) (← ofOptExpr env c m step)
            (← ofBody env c m body (ofStmt env c m body)), []⟩
      | .decl kind ⟨⟨lhs, dinit⟩, ds⟩ =>
          match ds with
          | _ :: _ => fail "a `for` clause that declares several variables"
          | [] =>
            let n ← binderName lhs
            match kind with
            | .const =>
                match dinit with
                | none => fail "a const declaration without an initialiser"
                | some i =>
                    let i' ← ofExpr env c m i
                    let inner := env.pushConsts c [n]
                    return ⟨0, 0, .for_ (.constDecl i') (← ofOptExpr inner (c + 1) m cond)
                      (← ofOptExpr inner (c + 1) m step)
                      (← ofBody inner (c + 1) m body (ofStmt inner (c + 1) m body)), []⟩
            | _ =>
                let i' ← ofOptExpr env c m dinit
                let inner := env.pushMuts m [n]
                return ⟨0, 0, .for_ (.letDecl i') (← ofOptExpr inner c (m + 1) cond)
                  (← ofOptExpr inner c (m + 1) step)
                  (← ofBody inner c (m + 1) body (ofStmt inner c (m + 1) body)), []⟩
  | .forIn head obj body =>
      let obj' ← ofExpr env c m obj
      match head with
      | .pattern lhs =>
          let t ← ofPatternTarget env c m lhs
          let b ← ofBody env c m body (ofStmt env c m body)
          return ⟨0, 0, .forIn (.target t) obj' b, []⟩
      | .decl kind lhs =>
          let n ← binderName lhs
          match kind with
          | .const =>
              let inner := env.pushConsts c [n]
              let b ← ofBody inner (c + 1) m body (ofStmt inner (c + 1) m body)
              return ⟨0, 0, .forIn .constBind obj' b, []⟩
          | _ =>
              let inner := env.pushMuts m [n]
              let b ← ofBody inner c (m + 1) body (ofStmt inner c (m + 1) body)
              return ⟨0, 0, .forIn .letBind obj' b, []⟩
  | .forOf head obj body =>
      let obj' ← ofExpr env c m obj
      match head with
      | .pattern lhs =>
          let t ← ofPatternTarget env c m lhs
          let b ← ofBody env c m body (ofStmt env c m body)
          return ⟨0, 0, .forOf (.target t) obj' b, []⟩
      | .decl kind lhs =>
          let n ← binderName lhs
          match kind with
          | .const =>
              let inner := env.pushConsts c [n]
              let b ← ofBody inner (c + 1) m body (ofStmt inner (c + 1) m body)
              return ⟨0, 0, .forOf .constBind obj' b, []⟩
          | _ =>
              let inner := env.pushMuts m [n]
              let b ← ofBody inner c (m + 1) body (ofStmt inner c (m + 1) body)
              return ⟨0, 0, .forOf .letBind obj' b, []⟩
  | .funcDecl isAsync isGen name params body =>
      let ps ← paramsOf params
      let inner := (env.pushConsts c [name]).pushMuts m ps.names
      let b ← ofStmts inner (c + 1) (m + ps.arity + ps.hasRest.toNat) body
      return ⟨1, 0, .funcDecl isAsync isGen ps.hasRest ps.arity b, [⟨name, true, c⟩]⟩
  | .classDecl decorators name heritage body =>
      let ds ← ofExprs env c m decorators
      let her ← ofOptExpr env c m heritage
      let els ← ofClassElems (env.pushConsts c [name]) (c + 1) m body
      return ⟨1, 0, .classDecl ds her els, [⟨name, true, c⟩]⟩
  | .return_ e => return ⟨0, 0, .return_ (← ofOptExpr env c m e), []⟩
  | .throw e => return ⟨0, 0, .throw (← ofExpr env c m e), []⟩
  | .break_ l => return ⟨0, 0, .break_ l, []⟩
  | .continue_ l => return ⟨0, 0, .continue_ l, []⟩
  | .labelled l s' =>
      -- a label may carry a declaration, a labelled function declaration
      -- being the usual case, so what the statement binds is what the
      -- labelled statement binds
      let ⟨dc, dm, st, binds⟩ ← ofStmt env c m s'
      return ⟨dc, dm, .labelled l st, binds⟩
  | .switch d cases =>
      return ⟨0, 0, .switch (← ofExpr env c m d) (← ofSwitchCases env c m cases), []⟩
  | .try_ body tail =>
      let b ← ofStmts env c m body
      match tail with
      | .finallyOnly fb => return ⟨0, 0, .try_ b (.finallyOnly (← ofStmts env c m fb)), []⟩
      | .catches ⟨cat, cs⟩ fin =>
          match cs with
          | _ :: _ => fail "a `try` with several catch clauses"
          | [] =>
            match cat with
            | ⟨param, guard, cbody⟩ =>
              match guard with
              | some _ => fail "a catch clause with a guard"
              | none =>
                  let n ← binderName param
                  let cb ← ofStmts (env.pushMuts m [n]) c (m + 1) cbody
                  let f : OptBlock exprExt targetExt c m ←
                    match fin with
                    | .none => pure .none
                    | .some fb => do pure (.some (← ofStmts env c m fb))
                  return ⟨0, 0, .try_ b (.catch_ cb f), []⟩
  | .with_ _ _ => fail "a `with` statement (its scope is dynamic)"
termination_by structural s

/-- Convert a top level item, together with what it binds. -/
def ofModuleItem (env : Env) (c m : Nat) : MiniModuleItem → ConvM exprExt targetExt (ItemRes exprExt targetExt c m)
  | .stmt s => do
      let r ← ofStmt env c m s
      return ⟨r.dc, r.dm, .stmt r.stmt, r.binds⟩
  | .importDecl (.bare mod attrs) => pure ⟨0, 0, .importBare mod attrs, []⟩
  | .importDecl (.clause cl) => do
      let specs := cl.named.getD []
      let names := specs.map (·.name)
      let locals :=
        cl.default_.toList ++ cl.namespace_.toList ++ specs.map fun s => s.alias_.getD s.name
      match ImportClause.mk? cl.mod cl.default_.isSome cl.namespace_.isSome names cl.attrs with
      | none => fail "an import that binds nothing"
      | some clause =>
          return ⟨clause.count, 0, .importClause clause,
            locals.zipIdx.map fun (n, j) => ⟨n, true, c + j⟩⟩
  | .exportDecl (.fromClause specs mod attrs) => pure ⟨0, 0, .exportFrom specs mod attrs, []⟩
  | .exportDecl (.all alias_ mod attrs) => pure ⟨0, 0, .exportAll alias_ mod attrs, []⟩
  | .exportDecl (.defaultExpr e) => do
      return ⟨0, 0, .exportDefaultExpr (← ofExpr env c m e), []⟩
  | .exportDecl (.locals specs) => do
      let entries ← specs.mapM fun sp =>
        resolveExportLocal env c m sp.name (sp.alias_.getD sp.name)
      return ⟨0, 0, .exportLocals (ExportLocals.ofList entries), []⟩
  | .exportDecl (.decl s) => do
      let r ← ofStmt env c m s
      return ⟨r.dc, r.dm, .exportDecl r.stmt, r.binds⟩

/-- Convert the top level items.  As in a block, an empty statement
disappears and a declaration of several variables — exported or not —
becomes one item per declarator. -/
def ofItems (env : Env) (c m : Nat) : List MiniModuleItem → ConvM exprExt targetExt (ModuleItems exprExt targetExt c m)
  | [] => pure .nil
  | .stmt .empty :: rest => ofItems env c m rest
  | .stmt (.decl kind ⟨d, ds⟩) :: rest =>
      ofDeclThenItems false (.var_ kind) d env c m fun env c m =>
        ofDeclsThenItems false (.var_ kind) ds env c m fun env c m =>
          ofItems env c m rest
  | .stmt (.using_ isAwait ⟨d, ds⟩) :: rest =>
      ofDeclThenItems false (.using_ isAwait) d env c m fun env c m =>
        ofDeclsThenItems false (.using_ isAwait) ds env c m fun env c m =>
          ofItems env c m rest
  | .exportDecl (.decl .empty) :: rest => ofItems env c m rest
  | .exportDecl (.decl (.decl kind ⟨d, ds⟩)) :: rest =>
      ofDeclThenItems true (.var_ kind) d env c m fun env c m =>
        ofDeclsThenItems true (.var_ kind) ds env c m fun env c m =>
          ofItems env c m rest
  | .exportDecl (.decl (.using_ isAwait ⟨d, ds⟩)) :: rest =>
      ofDeclThenItems true (.using_ isAwait) d env c m fun env c m =>
        ofDeclsThenItems true (.using_ isAwait) ds env c m fun env c m =>
          ofItems env c m rest
  | it :: rest => do
      let r ← ofModuleItem env c m it
      let tl ← ofItems (r.binds.reverse ++ env) (c + r.dc) (m + r.dm) rest
      pure (.cons r.item tl)
termination_by structural x => x

end

/-- Convert a `MiniProgram` with the given resolvers for free names and free targets. -/
def ofMiniProgramWith (resolvers : Resolvers exprExt targetExt) (p : MiniProgram) :
    ResM (ModuleItems exprExt targetExt 0 0) :=
  (ofItems [] 0 0 p.items).run resolvers

/-- Convert an expression with the given resolvers for free names and free targets. -/
def ofExprWith (resolvers : Resolvers exprExt targetExt) (env : Env) (c m : Nat) (e : MiniExpr) :
    ResM (Expr exprExt targetExt c m) :=
  (ofExpr env c m e).run resolvers

/-- Convert a `MiniProgram`, specifying resolving callbacks directly. -/
def ofProgramWith
    (resolveFree : (c m : Nat) → NEString → Except String (exprExt c m))
    (resolveFreeTarget : (c m : Nat) → NEString → Except String (targetExt c m) :=
      fun _ _ n => .error s!"assignment to unknown global: {n.val}")
    (p : MiniProgram) :
    ResM (ModuleItems exprExt targetExt 0 0) :=
  ofMiniProgramWith ⟨resolveFree, resolveFreeTarget⟩ p

/-- Convert an expression, specifying resolving callbacks directly. -/
def ofExprWithFns
    (resolveFree : (c m : Nat) → NEString → Except String (exprExt c m))
    (resolveFreeTarget : (c m : Nat) → NEString → Except String (targetExt c m) :=
      fun _ _ n => .error s!"assignment to unknown global: {n.val}")
    (env : Env) (c m : Nat) (e : MiniExpr) :
    ResM (Expr exprExt targetExt c m) :=
  ofExprWith ⟨resolveFree, resolveFreeTarget⟩ env c m e

/-- Convert a closed `MiniProgram` (no free names or targets allowed). -/
def ofMiniProgramClosed (p : MiniProgram) : ResM (ModuleItems NoExt NoExt 0 0) :=
  ofMiniProgramWith ⟨fun _ _ n => .error s!"unknown global: {n.val}",
                     fun _ _ n => .error s!"assignment to unknown global: {n.val}"⟩ p

/-- Convert a closed expression (no free names or targets allowed). -/
def ofExprClosed (env : Env) (c m : Nat) (e : MiniExpr) : ResM (Expr NoExt NoExt c m) :=
  ofExprWith ⟨fun _ _ n => .error s!"unknown global: {n.val}",
              fun _ _ n => .error s!"assignment to unknown global: {n.val}"⟩ env c m e

/-- Parse a JavaScript program with custom resolvers. -/
def parseWith (resolvers : Resolvers exprExt targetExt) (input : String) :
    ResM (ModuleItems exprExt targetExt 0 0) := do
  ofMiniProgramWith resolvers (← MiniAST.parse input)

def isIdentChar (ch : Char) : Bool := ch.isAlphanum || ch == '_' || ch == '$'

inductive ScanMode where
  | code
  | subst (depth : Nat)
  | string (delim : Char)
  | template
  | lineComment
  | blockComment
deriving Repr, DecidableEq, Inhabited

/-- The number written in decimal at the byte index `p`, the index just
after it, and whether there was a digit at all.

The scan is well founded on the number of bytes of the input still to be
read; it takes no step counter. -/
private def digitsAt (input : String) (p : String.Pos.Raw) (value : Nat)
    (any : Bool) : Nat × String.Pos.Raw × Bool :=
  if _h : input.utf8ByteSize ≤ p.byteIdx then (value, p, any)
  else if (String.Pos.Raw.get input p).isDigit then
    digitsAt input (String.Pos.Raw.next input p)
      (10 * value + ((String.Pos.Raw.get input p).toNat - '0'.toNat)) true
  else (value, p, any)
termination_by input.utf8ByteSize - p.byteIdx
decreasing_by
  have := String.Pos.Raw.byteIdx_lt_byteIdx_next input p
  omega

/-- Reading the digits never moves backwards. -/
private theorem digitsAt_le (input : String) (p : String.Pos.Raw) (value : Nat) (any : Bool) :
    p.byteIdx ≤ (digitsAt input p value any).2.1.byteIdx := by
  rw [digitsAt]
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_trans (Nat.le_of_lt (String.Pos.Raw.byteIdx_lt_byteIdx_next input p))
        (digitsAt_le input (String.Pos.Raw.next input p) _ _)
    · exact Nat.le_refl _
termination_by input.utf8ByteSize - p.byteIdx
decreasing_by
  rename_i hend _
  have := String.Pos.Raw.byteIdx_lt_byteIdx_next input p
  omega

/-- Rewrite the index references of `input` from the byte index `p` on,
`stack` describing what is being scanned and `prev` being the character
before `p`.

The input is read in place, by byte index, and the result is built by
pushing onto `acc`: neither the input nor the tail it is skipping ever
becomes a list of characters.

The scan is well founded on the number of bytes of the input still to be
read: it stops at the end of the input, and every step reads at least one
byte.  It takes no step counter, so it does not have to be told how long
its input is. -/
def rewriteAux (input : String) (stack : List ScanMode) (prev : Char)
    (p : String.Pos.Raw) (acc : String) : String :=
  let size := input.utf8ByteSize
  if _hend : size ≤ p.byteIdx then acc
  else
    let ch := String.Pos.Raw.get input p
    let q := String.Pos.Raw.next input p
    let q2 := String.Pos.Raw.next input q
    let nextIs (c : Char) : Bool := q.byteIdx < size && String.Pos.Raw.get input q == c
    match stack with
    | [] => acc ++ String.Pos.Raw.extract input p ⟨size⟩
    | .string d :: st =>
        if ch == '\\' then
          if size ≤ q.byteIdx then acc.push ch
          else
            let e := String.Pos.Raw.get input q
            rewriteAux input stack e q2 ((acc.push ch).push e)
        else if ch == d then rewriteAux input st ch q (acc.push ch)
        else rewriteAux input stack ch q (acc.push ch)
    | .template :: st =>
        if ch == '\\' then
          if size ≤ q.byteIdx then acc.push ch
          else
            let e := String.Pos.Raw.get input q
            rewriteAux input stack e q2 ((acc.push ch).push e)
        else if ch == '`' then rewriteAux input st ch q (acc.push ch)
        else if ch == '$' && nextIs '{' then
          rewriteAux input (.subst 0 :: stack) ' ' q2 ((acc.push ch).push '{')
        else rewriteAux input stack ch q (acc.push ch)
    | .lineComment :: st =>
        if ch == '\n' then rewriteAux input st ch q (acc.push ch)
        else rewriteAux input stack ch q (acc.push ch)
    | .blockComment :: st =>
        if prev == '*' && ch == '/' then rewriteAux input st ch q (acc.push ch)
        else rewriteAux input stack ch q (acc.push ch)
    | m :: st =>
        if (ch == 'c' || ch == 'l') && !isIdentChar prev then
          if nextIs '#' then
            let d := digitsAt input q2 0 false
            if !d.2.2 then rewriteAux input stack ch q (acc.push ch)
            else
              let name := if ch == 'c' then (idxConstIdent d.1).val else (idxMutIdent d.1).val
              rewriteAux input stack '0' d.2.1 (acc ++ name)
          else rewriteAux input stack ch q (acc.push ch)
        else if ch == '"' || ch == '\'' then
          rewriteAux input (.string ch :: stack) ch q (acc.push ch)
        else if ch == '`' then rewriteAux input (.template :: stack) ch q (acc.push ch)
        else if ch == '/' && nextIs '/' then
          rewriteAux input (.lineComment :: stack) ' ' q2 ((acc.push ch).push '/')
        else if ch == '/' && nextIs '*' then
          rewriteAux input (.blockComment :: stack) ' ' q2 ((acc.push ch).push '*')
        else
          match m with
          | .subst d =>
              if ch == '{' then rewriteAux input (.subst (d + 1) :: st) ch q (acc.push ch)
              else if ch == '}' then
                if d == 0 then rewriteAux input st ch q (acc.push ch)
                else rewriteAux input (.subst (d - 1) :: st) ch q (acc.push ch)
              else rewriteAux input stack ch q (acc.push ch)
          | _ => rewriteAux input stack ch q (acc.push ch)
termination_by input.utf8ByteSize - p.byteIdx
decreasing_by
  all_goals
    have h1 := String.Pos.Raw.byteIdx_lt_byteIdx_next input p
    have h2 := String.Pos.Raw.byteIdx_lt_byteIdx_next input (String.Pos.Raw.next input p)
    have h3 := digitsAt_le input (String.Pos.Raw.next input (String.Pos.Raw.next input p)) 0 false
    omega

def rewriteIndexRefs (input : String) : String :=
  rewriteAux input [.code] ' ' ⟨0⟩ ""

/-- Default resolvers keeping free identifiers as their `NEString` name. -/
def defaultResolvers : Resolvers FreeExt FreeExt where
  resolveFree _ _ n := pure n
  resolveFreeTarget _ _ n := pure n

/-- Parse a JavaScript program, keeping free names as `NEString`. -/
def parse (input : String) : ResM (ModuleItems FreeExt FreeExt 0 0) :=
  parseWith defaultResolvers input

def parseIndexedWith (resolvers : Resolvers exprExt targetExt) (input : String) :
    ResM (ModuleItems exprExt targetExt 0 0) :=
  parseWith resolvers (rewriteIndexRefs input)

def parseExprIndexedWith (resolvers : Resolvers exprExt targetExt) (c m : Nat) (input : String) :
    ResM (Expr exprExt targetExt c m) := do
  let e ← MiniAST.parseExpr (rewriteIndexRefs input)
  ofExprWith resolvers [] c m e

def parseIndexed (input : String) : ResM (ModuleItems FreeExt FreeExt 0 0) :=
  parseIndexedWith defaultResolvers input

def parseIndexed! (input : String) : ModuleItems FreeExt FreeExt 0 0 :=
  (parseIndexed input).toOption.getD .nil

def parseExprIndexed (c m : Nat) (input : String) : ResM (Expr FreeExt FreeExt c m) :=
  parseExprIndexedWith defaultResolvers c m input

def parseExprIndexed! (c m : Nat) (input : String) : Expr FreeExt FreeExt c m :=
  (parseExprIndexed c m input).toOption.getD .null

end Language.JavaScript.BrujinAST
