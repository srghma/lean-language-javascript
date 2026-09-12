/-
Weakening the set of unsafe globals of a `BrujinAST` tree.

The set of globals a `Global.*` tree is instantiated at is an *upper bound* on the
unknown globals the tree may mention, so a tree built against `g` is also a
legal tree against any larger `g'`.  That is not true by definition —
`Expr.unsafeGlobal` stores a proof `name ∈ g` — so it has to be witnessed by
a function, and this is it: `Expr.weaken (h : g ⊆ g') e` rebuilds `e`,
transporting each membership proof along `h`.

Combining two trees that were built against different sets is what this is
for: weaken both to `g₁ ∪ g₂` and they become the same type.
-/
import LanguageJavascriptBrujin.AST

namespace Language.JavaScript.BrujinAST

mutual

/-- Reindex an expression along an inclusion of global sets: every
`unsafeGlobal name (mem : name ∈ g)` becomes `unsafeGlobal name (h mem)`.
The tree is otherwise unchanged. -/
def Expr.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.Expr c m g → Global.Expr c m g'
  | .mutVar i => .mutVar i
  | .constVar i => .constVar i
  | .unsafeExt ⟨name, _h⟩ => .unsafeExt ⟨name, h _h⟩
  | .number value => .number value
  | .string value => .string value
  | .regex re => .regex re
  | .null => .null
  | .true_ => .true_
  | .false_ => .false_
  | .this => .this
  | .superDot name => .superDot name
  | .superIndex idx => .superIndex (Expr.weaken h idx)
  | .superCall args => .superCall (Exprs.weaken h args)
  | .newTarget => .newTarget
  | .array elements => .array (ArrayElems.weaken h elements)
  | .object properties => .object (Properties.weaken h properties)
  | .assign target op rhs => .assign (Target.weaken h target) op (Expr.weaken h rhs)
  | .update target op isPrefix => .update (Target.weaken h target) op isPrefix
  | .await expr => .await (Expr.weaken h expr)
  | .call callee args => .call (Expr.weaken h callee) (Exprs.weaken h args)
  | .new callee args => .new (Expr.weaken h callee) (Exprs.weaken h args)
  | .dot obj name => .dot (Expr.weaken h obj) name
  | .index obj idx => .index (Expr.weaken h obj) (Expr.weaken h idx)
  | .privateDot obj name => .privateDot (Expr.weaken h obj) name
  | .privateName name => .privateName name
  | .chain base hd tl =>
      .chain (Expr.weaken h base) (ChainLink.weaken h hd) (ChainLinks.weaken h tl)
  | .importMeta => .importMeta
  | .importCall specifier options =>
      .importCall (Expr.weaken h specifier) (OptExpr.weaken h options)
  | .classAnon decorators heritage body =>
      .classAnon (Exprs.weaken h decorators) (OptExpr.weaken h heritage) (ClassElems.weaken h body)
  | .classSelf decorators heritage body =>
      .classSelf (Exprs.weaken h decorators) (OptExpr.weaken h heritage) (ClassElems.weaken h body)
  | .seq lhs rhs => .seq (Expr.weaken h lhs) (Expr.weaken h rhs)
  | .binary lhs op rhs => .binary (Expr.weaken h lhs) op (Expr.weaken h rhs)
  | .ternary cond thenE elseE => .ternary (Expr.weaken h cond) (Expr.weaken h thenE) (Expr.weaken h elseE)
  | .arrow arity hasRest body => .arrow arity hasRest (ArrowBody.weaken h body)
  | .func isAsync isGenerator hasRest arity body =>
      .func isAsync isGenerator hasRest arity (Block.weaken h body)
  | .funcSelf isAsync isGenerator hasRest arity body =>
      .funcSelf isAsync isGenerator hasRest arity (Block.weaken h body)
  | .spread expr => .spread (Expr.weaken h expr)
  | .template tag head parts => .template (OptExpr.weaken h tag) head (TemplateParts.weaken h parts)
  | .unary op expr => .unary op (Expr.weaken h expr)
  | .yield expr => .yield (OptExpr.weaken h expr)
  | .yieldFrom expr => .yieldFrom (Expr.weaken h expr)

def Target.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.Target c m g → Global.Target c m g'
  | .mut i => .mut i
  | .unsafeExt ⟨name, _h⟩ => .unsafeExt ⟨name, h _h⟩
  | .dot obj name => .dot (Expr.weaken h obj) name
  | .privateDot obj name => .privateDot (Expr.weaken h obj) name
  | .superDot name => .superDot name
  | .superIndex idx => .superIndex (Expr.weaken h idx)
  | .index obj idx => .index (Expr.weaken h obj) (Expr.weaken h idx)

def ChainLink.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ChainLink c m g → Global.ChainLink c m g'
  | .dot optional name => .dot optional name
  | .privateDot optional name => .privateDot optional name
  | .index optional idx => .index optional (Expr.weaken h idx)
  | .call optional args => .call optional (Exprs.weaken h args)

def ChainLinks.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ChainLinks c m g → Global.ChainLinks c m g'
  | .nil => .nil
  | .cons hd tl => .cons (ChainLink.weaken h hd) (ChainLinks.weaken h tl)

def Exprs.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.Exprs c m g → Global.Exprs c m g'
  | .nil => .nil
  | .cons hd tl => .cons (Expr.weaken h hd) (Exprs.weaken h tl)

def OptExpr.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.OptExpr c m g → Global.OptExpr c m g'
  | .none => .none
  | .some expr => .some (Expr.weaken h expr)

def ArrayElem.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ArrayElem c m g → Global.ArrayElem c m g'
  | .elem expr => .elem (Expr.weaken h expr)
  | .hole => .hole

def ArrayElems.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ArrayElems c m g → Global.ArrayElems c m g'
  | .nil => .nil
  | .cons hd tl => .cons (ArrayElem.weaken h hd) (ArrayElems.weaken h tl)

def TemplatePart.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.TemplatePart c m g → Global.TemplatePart c m g'
  | .mk expr suffix => .mk (Expr.weaken h expr) suffix

def TemplateParts.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.TemplateParts c m g → Global.TemplateParts c m g'
  | .nil => .nil
  | .cons hd tl => .cons (TemplatePart.weaken h hd) (TemplateParts.weaken h tl)

def PropName.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.PropName c m g → Global.PropName c m g'
  | .ident name => .ident name
  | .private_ name => .private_ name
  | .string value => .string value
  | .number value => .number value
  | .computed expr => .computed (Expr.weaken h expr)

def Property.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.Property c m g → Global.Property c m g'
  | .keyValue key value => .keyValue (PropName.weaken h key) (Expr.weaken h value)
  | .spread expr => .spread (Expr.weaken h expr)
  | .method kind key arity hasRest body =>
      .method kind (PropName.weaken h key) arity hasRest (Block.weaken h body)

def Properties.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.Properties c m g → Global.Properties c m g'
  | .nil => .nil
  | .cons hd tl => .cons (Property.weaken h hd) (Properties.weaken h tl)

def ClassElem.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ClassElem c m g → Global.ClassElem c m g'
  | .method decorators isStatic kind key arity hasRest body =>
      .method (Exprs.weaken h decorators) isStatic kind (PropName.weaken h key) arity hasRest
        (Block.weaken h body)
  | .field decorators isStatic key init =>
      .field (Exprs.weaken h decorators) isStatic (PropName.weaken h key) (OptExpr.weaken h init)
  | .staticBlock body => .staticBlock (Block.weaken h body)

def ClassElems.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ClassElems c m g → Global.ClassElems c m g'
  | .nil => .nil
  | .cons hd tl => .cons (ClassElem.weaken h hd) (ClassElems.weaken h tl)

def ArrowBody.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ArrowBody c m g → Global.ArrowBody c m g'
  | .expr expr => .expr (Expr.weaken h expr)
  | .block body => .block (Block.weaken h body)

def ForInit.weaken {c m dc dm : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ForInit c m g dc dm → Global.ForInit c m g' dc dm
  | .none => .none
  | .expr expr => .expr (Expr.weaken h expr)
  | .constDecl init => .constDecl (Expr.weaken h init)
  | .letDecl init => .letDecl (OptExpr.weaken h init)

def ForHead.weaken {c m dc dm : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ForHead c m g dc dm → Global.ForHead c m g' dc dm
  | .target target => .target (Target.weaken h target)
  | .constBind => .constBind
  | .letBind => .letBind

def SwitchCase.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.SwitchCase c m g → Global.SwitchCase c m g'
  | .case test body => .case (Expr.weaken h test) (Block.weaken h body)
  | .default body => .default (Block.weaken h body)

def SwitchCases.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.SwitchCases c m g → Global.SwitchCases c m g'
  | .nil => .nil
  | .cons hd tl => .cons (SwitchCase.weaken h hd) (SwitchCases.weaken h tl)

def OptBlock.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.OptBlock c m g → Global.OptBlock c m g'
  | .none => .none
  | .some body => .some (Block.weaken h body)

def TryTail.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.TryTail c m g → Global.TryTail c m g'
  | .catch_ body fin => .catch_ (Block.weaken h body) (OptBlock.weaken h fin)
  | .finallyOnly body => .finallyOnly (Block.weaken h body)

def Stmt.weaken {c m dc dm : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.Stmt c m g dc dm → Global.Stmt c m g' dc dm
  | .expr expr => .expr (Expr.weaken h expr)
  | .constDecl init => .constDecl (Expr.weaken h init)
  | .letDecl init => .letDecl (OptExpr.weaken h init)
  | .usingDecl isAwait init => .usingDecl isAwait (Expr.weaken h init)
  | .block body => .block (Block.weaken h body)
  | .if_ cond thenB elseB => .if_ (Expr.weaken h cond) (Block.weaken h thenB) (OptBlock.weaken h elseB)
  | .while_ cond body => .while_ (Expr.weaken h cond) (Block.weaken h body)
  | .doWhile body cond => .doWhile (Block.weaken h body) (Expr.weaken h cond)
  | .for_ init cond step body => .for_ (ForInit.weaken h init) (OptExpr.weaken h cond) (OptExpr.weaken h step) (Block.weaken h body)
  | .forIn head obj body => .forIn (ForHead.weaken h head) (Expr.weaken h obj) (Block.weaken h body)
  | .forOf head obj body => .forOf (ForHead.weaken h head) (Expr.weaken h obj) (Block.weaken h body)
  | .funcDecl isAsync isGenerator hasRest arity body =>
      .funcDecl isAsync isGenerator hasRest arity (Block.weaken h body)
  | .classDecl decorators heritage body =>
      .classDecl (Exprs.weaken h decorators) (OptExpr.weaken h heritage) (ClassElems.weaken h body)
  | .return_ expr => .return_ (OptExpr.weaken h expr)
  | .throw expr => .throw (Expr.weaken h expr)
  | .break_ label => .break_ label
  | .continue_ label => .continue_ label
  | .labelled label stmt => .labelled label (Stmt.weaken h stmt)
  | .switch disc cases => .switch (Expr.weaken h disc) (SwitchCases.weaken h cases)
  | .try_ body tail => .try_ (Block.weaken h body) (TryTail.weaken h tail)

def Block.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.Block c m g → Global.Block c m g'
  | .nil => .nil
  | .cons hd tl => .cons (Stmt.weaken h hd) (Block.weaken h tl)

/-- An export specifier names a local binding, never a global, so it can be
reindexed to *any* set of globals; no `g ⊆ g'` is needed. -/
def ExportLocal.weaken {c m : Nat} {g g' : Finset NEString} :
    Global.ExportLocal c m g → Global.ExportLocal c m g'
  | .const i exported => .const i exported
  | .mut i exported => .mut i exported

def ExportLocals.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ExportLocals c m g → Global.ExportLocals c m g'
  | .nil => .nil
  | .cons hd tl => .cons (ExportLocal.weaken hd) (ExportLocals.weaken h tl)

def ModuleItem.weaken {c m dc dm : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ModuleItem c m g dc dm → Global.ModuleItem c m g' dc dm
  | .stmt stmt => .stmt (Stmt.weaken h stmt)
  | .importBare mod attrs => .importBare mod attrs
  | .importClause clause => .importClause clause
  | .exportFrom specs mod attrs => .exportFrom specs mod attrs
  | .exportAll alias_ mod attrs => .exportAll alias_ mod attrs
  | .exportDefaultExpr expr => .exportDefaultExpr (Expr.weaken h expr)
  | .exportLocals specs => .exportLocals (ExportLocals.weaken h specs)
  | .exportDecl stmt => .exportDecl (Stmt.weaken h stmt)

def ModuleItems.weaken {c m : Nat} {g g' : Finset NEString}
    (h : g ⊆ g') : Global.ModuleItems c m g → Global.ModuleItems c m g'
  | .nil => .nil
  | .cons hd tl => .cons (ModuleItem.weaken h hd) (ModuleItems.weaken h tl)

end

/-- Weaken a whole block of module items along `g ⊆ g'`. -/
def Program.weakenTo (p : Program) {g' : Finset NEString} (h : p.globals ⊆ g') :
    Program :=
  ⟨g', ModuleItems.weaken h p.items⟩

/-- Weaken a scoped expression along `g ⊆ g'`. -/
def ScopedExpr.weakenTo {c m : Nat} (e : ScopedExpr c m) {g' : Finset NEString}
    (h : e.globals ⊆ g') : ScopedExpr c m :=
  ⟨g', Expr.weaken h e.expr⟩

/-- Put two scoped expressions in a common set of globals: the union. -/
def ScopedExpr.union {c m : Nat} (a b : ScopedExpr c m) :
    Global.Expr c m (a.globals ∪ b.globals) × Global.Expr c m (a.globals ∪ b.globals) :=
  (Expr.weaken Finset.subset_union_left a.expr,
   Expr.weaken Finset.subset_union_right b.expr)

end Language.JavaScript.BrujinAST
