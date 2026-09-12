/-
Removing a binding from the scope of a `BrujinAST` tree.

This is what an optimizer needs in order to delete a binding: a tree that
lives in a scope with one more const (respectively mutable) variable can be
moved into the smaller scope exactly when it does not mention that
variable, and the variables above it have to be renumbered.  Both halves
are what the following functions do, and the *type* records the result:

    strengthenConstExpr (k : Nat) : Expr exprExt targetExt (c + 1) m → Option (Expr exprExt targetExt c m)

gives `none` precisely when the variable of index `k` is mentioned, and
otherwise a tree in the smaller scope, with every index above `k` lowered
by one.  There is nothing to prove about the renumbering afterwards: a
wrong index would not typecheck.

`k` is the index of the variable to remove *at the root of the tree*.
Under a binder it grows: the body of a function of arity `a` sees `a` more
mutable variables, so the mutable variable that was `k` outside is `k + a`
inside; the same happens with the const scope inside a named function or
class, and inside the rest of a block, after a statement that binds `dc`
const and `dm` mutable variables.

**Why the `…At` functions carry an equation.**  Under such a binder the
scope of the subtree is `c + 1 + dc`, while the recursion wants a tree in a
scope of the shape `_ + 1`, namely `(c + dc) + 1`.  The two are equal but
not definitionally so.  Transporting the subtree along that equation (with
`Block.castScope`) hides it behind a `▸`, which is no longer a structural
subterm, and the whole file then had to be `partial`: opaque to the kernel,
with no equations to reason with.

The functions therefore take the scope of the tree as it is, together with
an equation saying what it is *equal to*:

    strengthenConstBlockAt (b : Block exprExt targetExt c' m) (hc : c' = c + 1) (k : Nat) :
      Option (Block exprExt targetExt c m)

The equation travels instead of the tree, every recursive call is on a
genuine subterm, and the definitions are structurally recursive: they
reduce in the kernel and have equation lemmas.  The functions named without
`At` are the same thing with `c' = c + 1` — they pass `rfl`.
-/
import LanguageJavascriptBrujin.AST

namespace Language.JavaScript.BrujinAST

-- The extensions a tree may mention.  Every function here is generic in
-- them; removing a binding from the scope moves an extension to the
-- smaller scope, which is what `ExtInvariant` provides.
variable {exprExt targetExt : Nat → Nat → Type}
  [ExtInvariant exprExt] [ExtInvariant targetExt]

/-! ## Moving between equal scopes

A scope such as `c + 1 + dc` and the scope `c + dc + 1` the recursion wants
are equal but not definitionally so; `Expr.castScope` and its siblings (in
`BrujinAST`) move a tree between them.  Only the body of an arrow function
is missing there.  The functions below no longer need them — they carry the
equation instead — but they are part of the tree's interface. -/

/-- Move the body of an arrow function to an equal scope. -/
def ArrowBody.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m') (b : ArrowBody exprExt targetExt c m) :
    ArrowBody exprExt targetExt c' m' := hc ▸ hm ▸ b

/-! ## Removing a const variable -/

mutual

/-- Remove the const variable of index `k` from the scope of an
expression; `none` if it is mentioned. -/
def strengthenConstExprAt {c' m : Nat} (e : Expr exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1) (k : Nat) :
    Option (Expr exprExt targetExt c m) :=
  match e with
  | .mutVar i => some (.mutVar i)
  | .constVar i =>
      if i.val = k then none
      else if h : k < i.val then some (.constVar ⟨i.val - 1, by omega⟩)
      else if h' : i.val < c then some (.constVar ⟨i.val, h'⟩)
      else none
  | .unsafeExt e => some (.unsafeExt (ExtInvariant.castScope e))
  | .number raw => some (.number raw)
  | .string v => some (.string v)
  | .regex raw => some (.regex raw)
  | .null => some .null
  | .true_ => some .true_
  | .false_ => some .false_
  | .this => some .this
  | .superDot n => some (.superDot n)
  | .superIndex i => do pure (.superIndex (← strengthenConstExprAt i hc k))
  | .superCall args => do pure (.superCall (← strengthenConstExprsAt args hc k))
  | .newTarget => some .newTarget
  | .array els => (strengthenConstArrayElemsAt els hc k).map .array
  | .object ps => (strengthenConstPropertiesAt ps hc k).map .object
  | .assign t op rhs => do
      pure (.assign (← strengthenConstTargetAt t hc k) op (← strengthenConstExprAt rhs hc k))
  | .update t op isPrefix => do pure (.update (← strengthenConstTargetAt t hc k) op isPrefix)
  | .await x => do pure (.await (← strengthenConstExprAt x hc k))
  | .call f args => do
      pure (.call (← strengthenConstExprAt f hc k) (← strengthenConstExprsAt args hc k))
  | .new f args => do
      pure (.new (← strengthenConstExprAt f hc k) (← strengthenConstExprsAt args hc k))
  | .dot o n => do pure (.dot (← strengthenConstExprAt o hc k) n)
  | .index o i => do
      pure (.index (← strengthenConstExprAt o hc k) (← strengthenConstExprAt i hc k))
  | .privateDot o n => do pure (.privateDot (← strengthenConstExprAt o hc k) n)
  | .privateName n => some (.privateName n)
  | .chain base hd tl => do
      pure (.chain (← strengthenConstExprAt base hc k) (← strengthenConstChainLinkAt hd hc k)
        (← strengthenConstChainLinksAt tl hc k))
  | .importMeta => some .importMeta
  | .importCall spec opts => do
      pure (.importCall (← strengthenConstExprAt spec hc k)
        (← strengthenConstOptExprAt opts hc k))
  | .classAnon ds her body => do
      pure (.classAnon (← strengthenConstExprsAt ds hc k) (← strengthenConstOptExprAt her hc k)
        (← strengthenConstClassElemsAt body hc k))
  | .classSelf ds her body => do
      pure (.classSelf (← strengthenConstExprsAt ds hc k) (← strengthenConstOptExprAt her hc k)
        (← strengthenConstClassElemsAt (c := c + 1) body (by omega) (k + 1)))
  | .seq a b => do pure (.seq (← strengthenConstExprAt a hc k) (← strengthenConstExprAt b hc k))
  | .binary a op b => do
      pure (.binary (← strengthenConstExprAt a hc k) op (← strengthenConstExprAt b hc k))
  | .ternary a b d => do
      pure (.ternary (← strengthenConstExprAt a hc k) (← strengthenConstExprAt b hc k)
        (← strengthenConstExprAt d hc k))
  | .arrow arity hasRest body => do
      pure (.arrow arity hasRest (← strengthenConstArrowBodyAt body hc k))
  | .func isAsync isGen hasRest arity body => do
      pure (.func isAsync isGen hasRest arity (← strengthenConstBlockAt body hc k))
  | .funcSelf isAsync isGen hasRest arity body => do
      pure (.funcSelf isAsync isGen hasRest arity
        (← strengthenConstBlockAt (c := c + 1) body (by omega) (k + 1)))
  | .spread x => do pure (.spread (← strengthenConstExprAt x hc k))
  | .template tag head parts => do
      pure (.template (← strengthenConstOptExprAt tag hc k) head
        (← strengthenConstTemplatePartsAt parts hc k))
  | .unary op x => do pure (.unary op (← strengthenConstExprAt x hc k))
  | .yield x => do pure (.yield (← strengthenConstOptExprAt x hc k))
  | .yieldFrom x => do pure (.yieldFrom (← strengthenConstExprAt x hc k))

/-- Remove the const variable of index `k` from an assignment target. -/
def strengthenConstTargetAt {c' m : Nat} (t : Target exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (Target exprExt targetExt c m) :=
  match t with
  | .mut i => some (.mut i)
  | .unsafeExt e => some (.unsafeExt (ExtInvariant.castScope e))
  | .dot o n => do pure (.dot (← strengthenConstExprAt o hc k) n)
  | .privateDot o n => do pure (.privateDot (← strengthenConstExprAt o hc k) n)
  | .superDot n => some (.superDot n)
  | .superIndex i => do pure (.superIndex (← strengthenConstExprAt i hc k))
  | .index o i => do
      pure (.index (← strengthenConstExprAt o hc k) (← strengthenConstExprAt i hc k))

/-- Remove the const variable of index `k` from one link of a chain. -/
def strengthenConstChainLinkAt {c' m : Nat} (l : ChainLink exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (ChainLink exprExt targetExt c m) :=
  match l with
  | .dot opt n => some (.dot opt n)
  | .privateDot opt n => some (.privateDot opt n)
  | .index opt i => do pure (.index opt (← strengthenConstExprAt i hc k))
  | .call opt args => do pure (.call opt (← strengthenConstExprsAt args hc k))

/-- Remove the const variable of index `k` from the links of a chain. -/
def strengthenConstChainLinksAt {c' m : Nat} (ls : ChainLinks exprExt targetExt c' m) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (ChainLinks exprExt targetExt c m) :=
  match ls with
  | .nil => some .nil
  | .cons hd tl => do
      pure (.cons (← strengthenConstChainLinkAt hd hc k) (← strengthenConstChainLinksAt tl hc k))

/-- Remove the const variable of index `k` from a list of expressions. -/
def strengthenConstExprsAt {c' m : Nat} (es : Exprs exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (Exprs exprExt targetExt c m) :=
  match es with
  | .nil => some .nil
  | .cons e r => do
      pure (.cons (← strengthenConstExprAt e hc k) (← strengthenConstExprsAt r hc k))

/-- Remove the const variable of index `k` from an optional expression. -/
def strengthenConstOptExprAt {c' m : Nat} (e : OptExpr exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (OptExpr exprExt targetExt c m) :=
  match e with
  | .none => some .none
  | .some e => do pure (.some (← strengthenConstExprAt e hc k))

/-- Remove the const variable of index `k` from the elements of an array. -/
def strengthenConstArrayElemsAt {c' m : Nat} (els : ArrayElems exprExt targetExt c' m) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (ArrayElems exprExt targetExt c m) :=
  match els with
  | .nil => some .nil
  | .cons .hole r => do pure (.cons .hole (← strengthenConstArrayElemsAt r hc k))
  | .cons (.elem e) r => do
      pure (.cons (.elem (← strengthenConstExprAt e hc k))
        (← strengthenConstArrayElemsAt r hc k))

/-- Remove the const variable of index `k` from a template literal. -/
def strengthenConstTemplatePartsAt {c' m : Nat} (ps : TemplateParts exprExt targetExt c' m) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (TemplateParts exprExt targetExt c m) :=
  match ps with
  | .nil => some .nil
  | .cons (.mk e s) r => do
      pure (.cons (.mk (← strengthenConstExprAt e hc k) s)
        (← strengthenConstTemplatePartsAt r hc k))

/-- Remove the const variable of index `k` from the name of a property. -/
def strengthenConstPropNameAt {c' m : Nat} (n : PropName exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (PropName exprExt targetExt c m) :=
  match n with
  | .ident n => some (.ident n)
  | .private_ n => some (.private_ n)
  | .string v => some (.string v)
  | .number raw => some (.number raw)
  | .computed e => do pure (.computed (← strengthenConstExprAt e hc k))

/-- Remove the const variable of index `k` from an object literal. -/
def strengthenConstPropertiesAt {c' m : Nat} (ps : Properties exprExt targetExt c' m) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (Properties exprExt targetExt c m) :=
  match ps with
  | .nil => some .nil
  | .cons (.keyValue key v) r => do
      pure (.cons (.keyValue (← strengthenConstPropNameAt key hc k)
        (← strengthenConstExprAt v hc k)) (← strengthenConstPropertiesAt r hc k))
  | .cons (.spread e) r => do
      pure (.cons (.spread (← strengthenConstExprAt e hc k))
        (← strengthenConstPropertiesAt r hc k))
  | .cons (.method kind key arity hasRest body) r => do
      pure (.cons (.method kind (← strengthenConstPropNameAt key hc k) arity hasRest
        (← strengthenConstBlockAt body hc k)) (← strengthenConstPropertiesAt r hc k))

/-- Remove the const variable of index `k` from a class body. -/
def strengthenConstClassElemsAt {c' m : Nat} (es : ClassElems exprExt targetExt c' m) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (ClassElems exprExt targetExt c m) :=
  match es with
  | .nil => some .nil
  | .cons (.method ds isStatic kind key arity hasRest body) r => do
      pure (.cons (.method (← strengthenConstExprsAt ds hc k) isStatic kind
        (← strengthenConstPropNameAt key hc k) arity hasRest
        (← strengthenConstBlockAt body hc k)) (← strengthenConstClassElemsAt r hc k))
  | .cons (.field ds isStatic key init) r => do
      pure (.cons (.field (← strengthenConstExprsAt ds hc k) isStatic
        (← strengthenConstPropNameAt key hc k) (← strengthenConstOptExprAt init hc k))
        (← strengthenConstClassElemsAt r hc k))
  | .cons (.staticBlock body) r => do
      pure (.cons (.staticBlock (← strengthenConstBlockAt body hc k))
        (← strengthenConstClassElemsAt r hc k))

/-- Remove the const variable of index `k` from the body of an arrow. -/
def strengthenConstArrowBodyAt {c' m : Nat} (b : ArrowBody exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (ArrowBody exprExt targetExt c m) :=
  match b with
  | .expr e => do pure (.expr (← strengthenConstExprAt e hc k))
  | .block b => do pure (.block (← strengthenConstBlockAt b hc k))

/-- Remove the const variable of index `k` from the first clause of a
`for (;;)`. -/
def strengthenConstForInitAt {c' m dc dm : Nat} (i : ForInit exprExt targetExt c' m dc dm) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (ForInit exprExt targetExt c m dc dm) :=
  match i with
  | .none => some .none
  | .expr e => do pure (.expr (← strengthenConstExprAt e hc k))
  | .constDecl init => do pure (.constDecl (← strengthenConstExprAt init hc k))
  | .letDecl init => do pure (.letDecl (← strengthenConstOptExprAt init hc k))

/-- Remove the const variable of index `k` from the binder of a
`for (... of ...)`. -/
def strengthenConstForHeadAt {c' m dc dm : Nat} (h : ForHead exprExt targetExt c' m dc dm) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (ForHead exprExt targetExt c m dc dm) :=
  match h with
  | .target t => do pure (.target (← strengthenConstTargetAt t hc k))
  | .constBind => some .constBind
  | .letBind => some .letBind

/-- Remove the const variable of index `k` from the cases of a `switch`. -/
def strengthenConstSwitchCasesAt {c' m : Nat} (cs : SwitchCases exprExt targetExt c' m) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (SwitchCases exprExt targetExt c m) :=
  match cs with
  | .nil => some .nil
  | .cons (.case t b) r => do
      pure (.cons (.case (← strengthenConstExprAt t hc k) (← strengthenConstBlockAt b hc k))
        (← strengthenConstSwitchCasesAt r hc k))
  | .cons (.default b) r => do
      pure (.cons (.default (← strengthenConstBlockAt b hc k))
        (← strengthenConstSwitchCasesAt r hc k))

/-- Remove the const variable of index `k` from an optional block. -/
def strengthenConstOptBlockAt {c' m : Nat} (b : OptBlock exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (OptBlock exprExt targetExt c m) :=
  match b with
  | .none => some .none
  | .some b => do pure (.some (← strengthenConstBlockAt b hc k))

/-- Remove the const variable of index `k` from what follows a `try`. -/
def strengthenConstTryTailAt {c' m : Nat} (t : TryTail exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (TryTail exprExt targetExt c m) :=
  match t with
  | .catch_ body fin => do
      pure (.catch_ (← strengthenConstBlockAt body hc k)
        (← strengthenConstOptBlockAt fin hc k))
  | .finallyOnly b => do pure (.finallyOnly (← strengthenConstBlockAt b hc k))

/-- Remove the const variable of index `k` from a statement. -/
def strengthenConstStmtAt {c' m dc dm : Nat} (s : Stmt exprExt targetExt c' m dc dm) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (Stmt exprExt targetExt c m dc dm) :=
  match s with
  | .expr e => do pure (.expr (← strengthenConstExprAt e hc k))
  | .constDecl init => do pure (.constDecl (← strengthenConstExprAt init hc k))
  | .letDecl init => do pure (.letDecl (← strengthenConstOptExprAt init hc k))
  | .usingDecl isAwait init => do
      pure (.usingDecl isAwait (← strengthenConstExprAt init hc k))
  | .block b => do pure (.block (← strengthenConstBlockAt b hc k))
  | .if_ cond t e => do
      pure (.if_ (← strengthenConstExprAt cond hc k) (← strengthenConstBlockAt t hc k)
        (← strengthenConstOptBlockAt e hc k))
  | .while_ cond b => do
      pure (.while_ (← strengthenConstExprAt cond hc k) (← strengthenConstBlockAt b hc k))
  | .doWhile b cond => do
      pure (.doWhile (← strengthenConstBlockAt b hc k) (← strengthenConstExprAt cond hc k))
  | .for_ (dc := dc') init cond step body => do
      let init ← strengthenConstForInitAt init hc k
      let cond ← strengthenConstOptExprAt (c := c + dc') cond (by omega) (k + dc')
      let step ← strengthenConstOptExprAt (c := c + dc') step (by omega) (k + dc')
      let body ← strengthenConstBlockAt (c := c + dc') body (by omega) (k + dc')
      pure (.for_ init cond step body)
  | .forIn (dc := dc') head obj body => do
      let head ← strengthenConstForHeadAt head hc k
      let obj ← strengthenConstExprAt obj hc k
      let body ← strengthenConstBlockAt (c := c + dc') body (by omega) (k + dc')
      pure (.forIn head obj body)
  | .forOf (dc := dc') head obj body => do
      let head ← strengthenConstForHeadAt head hc k
      let obj ← strengthenConstExprAt obj hc k
      let body ← strengthenConstBlockAt (c := c + dc') body (by omega) (k + dc')
      pure (.forOf head obj body)
  | .funcDecl isAsync isGen hasRest arity body => do
      pure (.funcDecl isAsync isGen hasRest arity
        (← strengthenConstBlockAt (c := c + 1) body (by omega) (k + 1)))
  | .classDecl ds her body => do
      pure (.classDecl (← strengthenConstExprsAt ds hc k) (← strengthenConstOptExprAt her hc k)
        (← strengthenConstClassElemsAt (c := c + 1) body (by omega) (k + 1)))
  | .return_ e => do pure (.return_ (← strengthenConstOptExprAt e hc k))
  | .throw e => do pure (.throw (← strengthenConstExprAt e hc k))
  | .break_ l => some (.break_ l)
  | .continue_ l => some (.continue_ l)
  | .labelled l s => do pure (.labelled l (← strengthenConstStmtAt s hc k))
  | .switch disc cases => do
      pure (.switch (← strengthenConstExprAt disc hc k)
        (← strengthenConstSwitchCasesAt cases hc k))
  | .try_ b tail => do
      pure (.try_ (← strengthenConstBlockAt b hc k) (← strengthenConstTryTailAt tail hc k))

/-- Remove the const variable of index `k` from a block. -/
def strengthenConstBlockAt {c' m : Nat} (b : Block exprExt targetExt c' m) {c : Nat} (hc : c' = c + 1)
    (k : Nat) : Option (Block exprExt targetExt c m) :=
  match b with
  | .nil => some .nil
  | .cons (dc := dc) hd tl => do
      let hd ← strengthenConstStmtAt hd hc k
      let tl ← strengthenConstBlockAt (c := c + dc) tl (by omega) (k + dc)
      pure (.cons hd tl)

end

/-! ## Removing a mutable variable -/

mutual

/-- Remove the mutable variable of index `k` from the scope of an
expression; `none` if it is mentioned. -/
def strengthenMutExprAt {c m' : Nat} (e : Expr exprExt targetExt c m') {m : Nat} (hm : m' = m + 1) (k : Nat) :
    Option (Expr exprExt targetExt c m) :=
  match e with
  | .constVar i => some (.constVar i)
  | .mutVar i =>
      if i.val = k then none
      else if h : k < i.val then some (.mutVar ⟨i.val - 1, by omega⟩)
      else if h' : i.val < m then some (.mutVar ⟨i.val, h'⟩)
      else none
  | .unsafeExt e => some (.unsafeExt (ExtInvariant.castScope e))
  | .number raw => some (.number raw)
  | .string v => some (.string v)
  | .regex raw => some (.regex raw)
  | .null => some .null
  | .true_ => some .true_
  | .false_ => some .false_
  | .this => some .this
  | .superDot n => some (.superDot n)
  | .superIndex i => do pure (.superIndex (← strengthenMutExprAt i hm k))
  | .superCall args => do pure (.superCall (← strengthenMutExprsAt args hm k))
  | .newTarget => some .newTarget
  | .array els => (strengthenMutArrayElemsAt els hm k).map .array
  | .object ps => (strengthenMutPropertiesAt ps hm k).map .object
  | .assign t op rhs => do
      pure (.assign (← strengthenMutTargetAt t hm k) op (← strengthenMutExprAt rhs hm k))
  | .update t op isPrefix => do pure (.update (← strengthenMutTargetAt t hm k) op isPrefix)
  | .await x => do pure (.await (← strengthenMutExprAt x hm k))
  | .call f args => do
      pure (.call (← strengthenMutExprAt f hm k) (← strengthenMutExprsAt args hm k))
  | .new f args => do
      pure (.new (← strengthenMutExprAt f hm k) (← strengthenMutExprsAt args hm k))
  | .dot o n => do pure (.dot (← strengthenMutExprAt o hm k) n)
  | .index o i => do pure (.index (← strengthenMutExprAt o hm k) (← strengthenMutExprAt i hm k))
  | .privateDot o n => do pure (.privateDot (← strengthenMutExprAt o hm k) n)
  | .privateName n => some (.privateName n)
  | .chain base hd tl => do
      pure (.chain (← strengthenMutExprAt base hm k) (← strengthenMutChainLinkAt hd hm k)
        (← strengthenMutChainLinksAt tl hm k))
  | .importMeta => some .importMeta
  | .importCall spec opts => do
      pure (.importCall (← strengthenMutExprAt spec hm k) (← strengthenMutOptExprAt opts hm k))
  | .classAnon ds her body => do
      pure (.classAnon (← strengthenMutExprsAt ds hm k) (← strengthenMutOptExprAt her hm k)
        (← strengthenMutClassElemsAt body hm k))
  | .classSelf ds her body => do
      pure (.classSelf (← strengthenMutExprsAt ds hm k) (← strengthenMutOptExprAt her hm k)
        (← strengthenMutClassElemsAt body hm k))
  | .seq a b => do pure (.seq (← strengthenMutExprAt a hm k) (← strengthenMutExprAt b hm k))
  | .binary a op b => do
      pure (.binary (← strengthenMutExprAt a hm k) op (← strengthenMutExprAt b hm k))
  | .ternary a b d => do
      pure (.ternary (← strengthenMutExprAt a hm k) (← strengthenMutExprAt b hm k)
        (← strengthenMutExprAt d hm k))
  | .arrow arity hasRest body => do
      pure (.arrow arity hasRest
        (← strengthenMutArrowBodyAt (m := m + arity + hasRest.toNat) body (by omega)
          (k + arity + hasRest.toNat)))
  | .func isAsync isGen hasRest arity body => do
      pure (.func isAsync isGen hasRest arity
        (← strengthenMutBlockAt (m := m + arity + hasRest.toNat) body (by omega)
          (k + arity + hasRest.toNat)))
  | .funcSelf isAsync isGen hasRest arity body => do
      pure (.funcSelf isAsync isGen hasRest arity
        (← strengthenMutBlockAt (m := m + arity + hasRest.toNat) body (by omega)
          (k + arity + hasRest.toNat)))
  | .spread x => do pure (.spread (← strengthenMutExprAt x hm k))
  | .template tag head parts => do
      pure (.template (← strengthenMutOptExprAt tag hm k) head
        (← strengthenMutTemplatePartsAt parts hm k))
  | .unary op x => do pure (.unary op (← strengthenMutExprAt x hm k))
  | .yield x => do pure (.yield (← strengthenMutOptExprAt x hm k))
  | .yieldFrom x => do pure (.yieldFrom (← strengthenMutExprAt x hm k))

/-- Remove the mutable variable of index `k` from an assignment target. -/
def strengthenMutTargetAt {c m' : Nat} (t : Target exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (Target exprExt targetExt c m) :=
  match t with
  | .mut i =>
      if i.val = k then none
      else if h : k < i.val then some (.mut ⟨i.val - 1, by omega⟩)
      else if h' : i.val < m then some (.mut ⟨i.val, h'⟩)
      else none
  | .unsafeExt e => some (.unsafeExt (ExtInvariant.castScope e))
  | .dot o n => do pure (.dot (← strengthenMutExprAt o hm k) n)
  | .privateDot o n => do pure (.privateDot (← strengthenMutExprAt o hm k) n)
  | .superDot n => some (.superDot n)
  | .superIndex i => do pure (.superIndex (← strengthenMutExprAt i hm k))
  | .index o i => do pure (.index (← strengthenMutExprAt o hm k) (← strengthenMutExprAt i hm k))

/-- Remove the mutable variable of index `k` from one link of a chain. -/
def strengthenMutChainLinkAt {c m' : Nat} (l : ChainLink exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (ChainLink exprExt targetExt c m) :=
  match l with
  | .dot opt n => some (.dot opt n)
  | .privateDot opt n => some (.privateDot opt n)
  | .index opt i => do pure (.index opt (← strengthenMutExprAt i hm k))
  | .call opt args => do pure (.call opt (← strengthenMutExprsAt args hm k))

/-- Remove the mutable variable of index `k` from the links of a chain. -/
def strengthenMutChainLinksAt {c m' : Nat} (ls : ChainLinks exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (ChainLinks exprExt targetExt c m) :=
  match ls with
  | .nil => some .nil
  | .cons hd tl => do
      pure (.cons (← strengthenMutChainLinkAt hd hm k) (← strengthenMutChainLinksAt tl hm k))

/-- Remove the mutable variable of index `k` from a list of expressions. -/
def strengthenMutExprsAt {c m' : Nat} (es : Exprs exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (Exprs exprExt targetExt c m) :=
  match es with
  | .nil => some .nil
  | .cons e r => do pure (.cons (← strengthenMutExprAt e hm k) (← strengthenMutExprsAt r hm k))

/-- Remove the mutable variable of index `k` from an optional expression. -/
def strengthenMutOptExprAt {c m' : Nat} (e : OptExpr exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (OptExpr exprExt targetExt c m) :=
  match e with
  | .none => some .none
  | .some e => do pure (.some (← strengthenMutExprAt e hm k))

/-- Remove the mutable variable of index `k` from the elements of an
array. -/
def strengthenMutArrayElemsAt {c m' : Nat} (els : ArrayElems exprExt targetExt c m') {m : Nat}
    (hm : m' = m + 1) (k : Nat) : Option (ArrayElems exprExt targetExt c m) :=
  match els with
  | .nil => some .nil
  | .cons .hole r => do pure (.cons .hole (← strengthenMutArrayElemsAt r hm k))
  | .cons (.elem e) r => do
      pure (.cons (.elem (← strengthenMutExprAt e hm k)) (← strengthenMutArrayElemsAt r hm k))

/-- Remove the mutable variable of index `k` from a template literal. -/
def strengthenMutTemplatePartsAt {c m' : Nat} (ps : TemplateParts exprExt targetExt c m') {m : Nat}
    (hm : m' = m + 1) (k : Nat) : Option (TemplateParts exprExt targetExt c m) :=
  match ps with
  | .nil => some .nil
  | .cons (.mk e s) r => do
      pure (.cons (.mk (← strengthenMutExprAt e hm k) s)
        (← strengthenMutTemplatePartsAt r hm k))

/-- Remove the mutable variable of index `k` from the name of a
property. -/
def strengthenMutPropNameAt {c m' : Nat} (n : PropName exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (PropName exprExt targetExt c m) :=
  match n with
  | .ident n => some (.ident n)
  | .private_ n => some (.private_ n)
  | .string v => some (.string v)
  | .number raw => some (.number raw)
  | .computed e => do pure (.computed (← strengthenMutExprAt e hm k))

/-- Remove the mutable variable of index `k` from an object literal. -/
def strengthenMutPropertiesAt {c m' : Nat} (ps : Properties exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (Properties exprExt targetExt c m) :=
  match ps with
  | .nil => some .nil
  | .cons (.keyValue key v) r => do
      pure (.cons (.keyValue (← strengthenMutPropNameAt key hm k)
        (← strengthenMutExprAt v hm k)) (← strengthenMutPropertiesAt r hm k))
  | .cons (.spread e) r => do
      pure (.cons (.spread (← strengthenMutExprAt e hm k))
        (← strengthenMutPropertiesAt r hm k))
  | .cons (.method kind key arity hasRest body) r => do
      pure (.cons (.method kind (← strengthenMutPropNameAt key hm k) arity hasRest
          (← strengthenMutBlockAt (m := m + arity + hasRest.toNat) body (by omega)
            (k + arity + hasRest.toNat)))
        (← strengthenMutPropertiesAt r hm k))

/-- Remove the mutable variable of index `k` from a class body. -/
def strengthenMutClassElemsAt {c m' : Nat} (es : ClassElems exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (ClassElems exprExt targetExt c m) :=
  match es with
  | .nil => some .nil
  | .cons (.method ds isStatic kind key arity hasRest body) r => do
      pure (.cons (.method (← strengthenMutExprsAt ds hm k) isStatic kind
          (← strengthenMutPropNameAt key hm k) arity hasRest
          (← strengthenMutBlockAt (m := m + arity + hasRest.toNat) body (by omega)
            (k + arity + hasRest.toNat)))
        (← strengthenMutClassElemsAt r hm k))
  | .cons (.field ds isStatic key init) r => do
      pure (.cons (.field (← strengthenMutExprsAt ds hm k) isStatic
          (← strengthenMutPropNameAt key hm k) (← strengthenMutOptExprAt init hm k))
        (← strengthenMutClassElemsAt r hm k))
  | .cons (.staticBlock body) r => do
      pure (.cons (.staticBlock (← strengthenMutBlockAt body hm k))
        (← strengthenMutClassElemsAt r hm k))

/-- Remove the mutable variable of index `k` from the body of an arrow. -/
def strengthenMutArrowBodyAt {c m' : Nat} (b : ArrowBody exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (ArrowBody exprExt targetExt c m) :=
  match b with
  | .expr e => do pure (.expr (← strengthenMutExprAt e hm k))
  | .block b => do pure (.block (← strengthenMutBlockAt b hm k))

/-- Remove the mutable variable of index `k` from the first clause of a
`for (;;)`. -/
def strengthenMutForInitAt {c m' dc dm : Nat} (i : ForInit exprExt targetExt c m' dc dm) {m : Nat}
    (hm : m' = m + 1) (k : Nat) : Option (ForInit exprExt targetExt c m dc dm) :=
  match i with
  | .none => some .none
  | .expr e => do pure (.expr (← strengthenMutExprAt e hm k))
  | .constDecl init => do pure (.constDecl (← strengthenMutExprAt init hm k))
  | .letDecl init => do pure (.letDecl (← strengthenMutOptExprAt init hm k))

/-- Remove the mutable variable of index `k` from the binder of a
`for (... of ...)`. -/
def strengthenMutForHeadAt {c m' dc dm : Nat} (h : ForHead exprExt targetExt c m' dc dm) {m : Nat}
    (hm : m' = m + 1) (k : Nat) : Option (ForHead exprExt targetExt c m dc dm) :=
  match h with
  | .target t => do pure (.target (← strengthenMutTargetAt t hm k))
  | .constBind => some .constBind
  | .letBind => some .letBind

/-- Remove the mutable variable of index `k` from the cases of a
`switch`. -/
def strengthenMutSwitchCasesAt {c m' : Nat} (cs : SwitchCases exprExt targetExt c m') {m : Nat}
    (hm : m' = m + 1) (k : Nat) : Option (SwitchCases exprExt targetExt c m) :=
  match cs with
  | .nil => some .nil
  | .cons (.case t b) r => do
      pure (.cons (.case (← strengthenMutExprAt t hm k) (← strengthenMutBlockAt b hm k))
        (← strengthenMutSwitchCasesAt r hm k))
  | .cons (.default b) r => do
      pure (.cons (.default (← strengthenMutBlockAt b hm k))
        (← strengthenMutSwitchCasesAt r hm k))

/-- Remove the mutable variable of index `k` from an optional block. -/
def strengthenMutOptBlockAt {c m' : Nat} (b : OptBlock exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (OptBlock exprExt targetExt c m) :=
  match b with
  | .none => some .none
  | .some b => do pure (.some (← strengthenMutBlockAt b hm k))

/-- Remove the mutable variable of index `k` from what follows a `try`. -/
def strengthenMutTryTailAt {c m' : Nat} (t : TryTail exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (TryTail exprExt targetExt c m) :=
  match t with
  | .catch_ body fin => do
      pure (.catch_ (← strengthenMutBlockAt (m := m + 1) body (by omega) (k + 1))
        (← strengthenMutOptBlockAt fin hm k))
  | .finallyOnly b => do pure (.finallyOnly (← strengthenMutBlockAt b hm k))

/-- Remove the mutable variable of index `k` from a statement. -/
def strengthenMutStmtAt {c m' dc dm : Nat} (s : Stmt exprExt targetExt c m' dc dm) {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (Stmt exprExt targetExt c m dc dm) :=
  match s with
  | .expr e => do pure (.expr (← strengthenMutExprAt e hm k))
  | .constDecl init => do pure (.constDecl (← strengthenMutExprAt init hm k))
  | .letDecl init => do pure (.letDecl (← strengthenMutOptExprAt init hm k))
  | .usingDecl isAwait init => do
      pure (.usingDecl isAwait (← strengthenMutExprAt init hm k))
  | .block b => do pure (.block (← strengthenMutBlockAt b hm k))
  | .if_ cond t e => do
      pure (.if_ (← strengthenMutExprAt cond hm k) (← strengthenMutBlockAt t hm k)
        (← strengthenMutOptBlockAt e hm k))
  | .while_ cond b => do
      pure (.while_ (← strengthenMutExprAt cond hm k) (← strengthenMutBlockAt b hm k))
  | .doWhile b cond => do
      pure (.doWhile (← strengthenMutBlockAt b hm k) (← strengthenMutExprAt cond hm k))
  | .for_ (dm := dm') init cond step body => do
      let init ← strengthenMutForInitAt init hm k
      let cond ← strengthenMutOptExprAt (m := m + dm') cond (by omega) (k + dm')
      let step ← strengthenMutOptExprAt (m := m + dm') step (by omega) (k + dm')
      let body ← strengthenMutBlockAt (m := m + dm') body (by omega) (k + dm')
      pure (.for_ init cond step body)
  | .forIn (dm := dm') head obj body => do
      let head ← strengthenMutForHeadAt head hm k
      let obj ← strengthenMutExprAt obj hm k
      let body ← strengthenMutBlockAt (m := m + dm') body (by omega) (k + dm')
      pure (.forIn head obj body)
  | .forOf (dm := dm') head obj body => do
      let head ← strengthenMutForHeadAt head hm k
      let obj ← strengthenMutExprAt obj hm k
      let body ← strengthenMutBlockAt (m := m + dm') body (by omega) (k + dm')
      pure (.forOf head obj body)
  | .funcDecl isAsync isGen hasRest arity body => do
      pure (.funcDecl isAsync isGen hasRest arity
        (← strengthenMutBlockAt (m := m + arity + hasRest.toNat) body (by omega)
          (k + arity + hasRest.toNat)))
  | .classDecl ds her body => do
      pure (.classDecl (← strengthenMutExprsAt ds hm k) (← strengthenMutOptExprAt her hm k)
        (← strengthenMutClassElemsAt body hm k))
  | .return_ e => do pure (.return_ (← strengthenMutOptExprAt e hm k))
  | .throw e => do pure (.throw (← strengthenMutExprAt e hm k))
  | .break_ l => some (.break_ l)
  | .continue_ l => some (.continue_ l)
  | .labelled l s => do pure (.labelled l (← strengthenMutStmtAt s hm k))
  | .switch disc cases => do
      pure (.switch (← strengthenMutExprAt disc hm k)
        (← strengthenMutSwitchCasesAt cases hm k))
  | .try_ b tail => do
      pure (.try_ (← strengthenMutBlockAt b hm k) (← strengthenMutTryTailAt tail hm k))

/-- Remove the mutable variable of index `k` from a block. -/
def strengthenMutBlockAt {c m' : Nat} (b : Block exprExt targetExt c m') {m : Nat} (hm : m' = m + 1)
    (k : Nat) : Option (Block exprExt targetExt c m) :=
  match b with
  | .nil => some .nil
  | .cons (dm := dm) hd tl => do
      let hd ← strengthenMutStmtAt hd hm k
      let tl ← strengthenMutBlockAt (m := m + dm) tl (by omega) (k + dm)
      pure (.cons hd tl)

end

/-! ## The scopes the caller writes

The tree usually already lives in a scope of the shape `c + 1`; these are
the `…At` functions with `rfl` for the equation. -/

/-- Remove the const variable of index `k` from an expression. -/
def strengthenConstExpr {c m : Nat} (k : Nat) (e : Expr exprExt targetExt (c + 1) m) : Option (Expr exprExt targetExt c m) :=
  strengthenConstExprAt e rfl k

/-- Remove the const variable of index `k` from a statement. -/
def strengthenConstStmt {c m dc dm : Nat} (k : Nat) (s : Stmt exprExt targetExt (c + 1) m dc dm) :
    Option (Stmt exprExt targetExt c m dc dm) :=
  strengthenConstStmtAt s rfl k

/-- Remove the const variable of index `k` from a block. -/
def strengthenConstBlock {c m : Nat} (k : Nat) (b : Block exprExt targetExt (c + 1) m) : Option (Block exprExt targetExt c m) :=
  strengthenConstBlockAt b rfl k

/-- Remove the mutable variable of index `k` from an expression. -/
def strengthenMutExpr {c m : Nat} (k : Nat) (e : Expr exprExt targetExt c (m + 1)) : Option (Expr exprExt targetExt c m) :=
  strengthenMutExprAt e rfl k

/-- Remove the mutable variable of index `k` from a statement. -/
def strengthenMutStmt {c m dc dm : Nat} (k : Nat) (s : Stmt exprExt targetExt c (m + 1) dc dm) :
    Option (Stmt exprExt targetExt c m dc dm) :=
  strengthenMutStmtAt s rfl k

/-- Remove the mutable variable of index `k` from a block. -/
def strengthenMutBlock {c m : Nat} (k : Nat) (b : Block exprExt targetExt c (m + 1)) : Option (Block exprExt targetExt c m) :=
  strengthenMutBlockAt b rfl k

/-! ## The top level

An `export { x }` mentions a variable, so a binding that is exported is
never removable — which is exactly what these give. -/

/-- Remove the const variable of index `k` from an `export { ... }`
clause. -/
def strengthenConstExportLocalsAt {c' m : Nat} (l : ExportLocals exprExt targetExt c' m) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (ExportLocals exprExt targetExt c m) :=
  match l with
  | .nil => some .nil
  | .cons (.const i exported) r => do
      let hd ←
        if i.val = k then none
        else if h : k < i.val then some (ExportLocal.const ⟨i.val - 1, by omega⟩ exported)
        else if h' : i.val < c then some (ExportLocal.const ⟨i.val, h'⟩ exported)
        else none
      pure (.cons hd (← strengthenConstExportLocalsAt r hc k))
  | .cons (.mut i exported) r => do
      pure (.cons (.mut i exported) (← strengthenConstExportLocalsAt r hc k))

/-- Remove the mutable variable of index `k` from an `export { ... }`
clause. -/
def strengthenMutExportLocalsAt {c m' : Nat} (l : ExportLocals exprExt targetExt c m') {m : Nat}
    (hm : m' = m + 1) (k : Nat) : Option (ExportLocals exprExt targetExt c m) :=
  match l with
  | .nil => some .nil
  | .cons (.mut i exported) r => do
      let hd ←
        if i.val = k then none
        else if h : k < i.val then some (ExportLocal.mut ⟨i.val - 1, by omega⟩ exported)
        else if h' : i.val < m then some (ExportLocal.mut ⟨i.val, h'⟩ exported)
        else none
      pure (.cons hd (← strengthenMutExportLocalsAt r hm k))
  | .cons (.const i exported) r => do
      pure (.cons (.const i exported) (← strengthenMutExportLocalsAt r hm k))

/-- Remove the const variable of index `k` from a top level item. -/
def strengthenConstModuleItemAt {c' m dc dm : Nat} (it : ModuleItem exprExt targetExt c' m dc dm) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (ModuleItem exprExt targetExt c m dc dm) :=
  match it with
  | .stmt s => do pure (.stmt (← strengthenConstStmtAt s hc k))
  | .importBare mod attrs => some (.importBare mod attrs)
  | .importClause clause => some (.importClause clause)
  | .exportFrom specs mod attrs => some (.exportFrom specs mod attrs)
  | .exportAll alias_ mod attrs => some (.exportAll alias_ mod attrs)
  | .exportDefaultExpr e => do pure (.exportDefaultExpr (← strengthenConstExprAt e hc k))
  | .exportLocals specs => do
      pure (.exportLocals (← strengthenConstExportLocalsAt specs hc k))
  | .exportDecl s => do pure (.exportDecl (← strengthenConstStmtAt s hc k))

/-- Remove the mutable variable of index `k` from a top level item. -/
def strengthenMutModuleItemAt {c m' dc dm : Nat} (it : ModuleItem exprExt targetExt c m' dc dm) {m : Nat}
    (hm : m' = m + 1) (k : Nat) : Option (ModuleItem exprExt targetExt c m dc dm) :=
  match it with
  | .stmt s => do pure (.stmt (← strengthenMutStmtAt s hm k))
  | .importBare mod attrs => some (.importBare mod attrs)
  | .importClause clause => some (.importClause clause)
  | .exportFrom specs mod attrs => some (.exportFrom specs mod attrs)
  | .exportAll alias_ mod attrs => some (.exportAll alias_ mod attrs)
  | .exportDefaultExpr e => do pure (.exportDefaultExpr (← strengthenMutExprAt e hm k))
  | .exportLocals specs => do pure (.exportLocals (← strengthenMutExportLocalsAt specs hm k))
  | .exportDecl s => do pure (.exportDecl (← strengthenMutStmtAt s hm k))

/-- Remove the const variable of index `k` from the top level items. -/
def strengthenConstModuleItemsAt {c' m : Nat} (l : ModuleItems exprExt targetExt c' m) {c : Nat}
    (hc : c' = c + 1) (k : Nat) : Option (ModuleItems exprExt targetExt c m) :=
  match l with
  | .nil => some .nil
  | .cons (dc := dc) hd tl => do
      let hd ← strengthenConstModuleItemAt hd hc k
      let tl ← strengthenConstModuleItemsAt (c := c + dc) tl (by omega) (k + dc)
      pure (.cons hd tl)

/-- Remove the mutable variable of index `k` from the top level items. -/
def strengthenMutModuleItemsAt {c m' : Nat} (l : ModuleItems exprExt targetExt c m') {m : Nat}
    (hm : m' = m + 1) (k : Nat) : Option (ModuleItems exprExt targetExt c m) :=
  match l with
  | .nil => some .nil
  | .cons (dm := dm) hd tl => do
      let hd ← strengthenMutModuleItemAt hd hm k
      let tl ← strengthenMutModuleItemsAt (m := m + dm) tl (by omega) (k + dm)
      pure (.cons hd tl)

/-- Remove the const variable of index `k` from an `export { ... }`
clause. -/
def strengthenConstExportLocals {c m : Nat} (k : Nat) (l : ExportLocals exprExt targetExt (c + 1) m) :
    Option (ExportLocals exprExt targetExt c m) :=
  strengthenConstExportLocalsAt l rfl k

/-- Remove the mutable variable of index `k` from an `export { ... }`
clause. -/
def strengthenMutExportLocals {c m : Nat} (k : Nat) (l : ExportLocals exprExt targetExt c (m + 1)) :
    Option (ExportLocals exprExt targetExt c m) :=
  strengthenMutExportLocalsAt l rfl k

/-- Remove the const variable of index `k` from a top level item. -/
def strengthenConstModuleItem {c m dc dm : Nat} (k : Nat) (it : ModuleItem exprExt targetExt (c + 1) m dc dm) :
    Option (ModuleItem exprExt targetExt c m dc dm) :=
  strengthenConstModuleItemAt it rfl k

/-- Remove the mutable variable of index `k` from a top level item. -/
def strengthenMutModuleItem {c m dc dm : Nat} (k : Nat) (it : ModuleItem exprExt targetExt c (m + 1) dc dm) :
    Option (ModuleItem exprExt targetExt c m dc dm) :=
  strengthenMutModuleItemAt it rfl k

/-- Remove the const variable of index `k` from the top level items. -/
def strengthenConstModuleItems {c m : Nat} (k : Nat) (l : ModuleItems exprExt targetExt (c + 1) m) :
    Option (ModuleItems exprExt targetExt c m) :=
  strengthenConstModuleItemsAt l rfl k

/-- Remove the mutable variable of index `k` from the top level items. -/
def strengthenMutModuleItems {c m : Nat} (k : Nat) (l : ModuleItems exprExt targetExt c (m + 1)) :
    Option (ModuleItems exprExt targetExt c m) :=
  strengthenMutModuleItemsAt l rfl k

end Language.JavaScript.BrujinAST
