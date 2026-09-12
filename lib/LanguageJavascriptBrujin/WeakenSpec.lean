/-
Weakening the set of unsafe globals does not change the program.

The set of globals a `Global.*` tree is instantiated at is an *upper bound* on the unknown
globals it may mention, and `Expr.weaken (h : g ⊆ g')` moves a tree to a
larger bound (`LanguageJavascriptBrujin.Weaken`).  It is meant to transport
the membership proof `name ∈ g` carried by `unsafeGlobal` and to change
nothing else — but that is a claim about a function which rebuilds the
whole tree, so it is worth proving rather than assuming.

This module proves it, by taking the tree back to the deterministic
`MiniAST`, which no longer mentions `g` at all:

* `toMiniExpr_weaken` : `toMiniExpr (Expr.weaken h e) = toMiniExpr e`,

and the same for every other type of the family, up to

* `toMiniProgram_weakenTo` : `toMiniProgram (p.weakenTo h) = toMiniProgram p`.

So weakening is invisible: the program a tree denotes — and therefore
everything printed from it — is exactly the program it denoted before.
-/
import LanguageJavascriptBrujin.ToMini
import LanguageJavascriptBrujin.Weaken

namespace Language.JavaScript.BrujinAST

open Language.JavaScript.MiniAST

section Naming

variable [naming : NamingScheme] {g g' : Finset NEString} (h : g ⊆ g')

mutual

/-- Weakening does not change the expression a tree denotes. -/
theorem toMiniExpr_weaken {c m : Nat} (e : Global.Expr c m g) :
    toMiniExpr (Expr.weaken h e) = toMiniExpr e :=
  match e with
  | .mutVar _ => rfl
  | .constVar _ => rfl
  | .unsafeExt _ => rfl
  | .number _ => rfl
  | .string _ => rfl
  | .regex _ => rfl
  | .null => rfl
  | .true_ => rfl
  | .false_ => rfl
  | .this => rfl
  | .superDot _ => rfl
  | .superIndex i => by
      show MiniExpr.superIndex _ = MiniExpr.superIndex _
      rw [toMiniExpr_weaken i]
  | .superCall args => by
      show MiniExpr.superCall _ = MiniExpr.superCall _
      rw [toMiniExprs_weaken args]
  | .newTarget => rfl
  | .array els => by
      show MiniExpr.array _ = MiniExpr.array _
      rw [toMiniArrayElems_weaken els]
  | .object ps => by
      show MiniExpr.object _ = MiniExpr.object _
      rw [toMiniProperties_weaken ps]
  | .assign t _ rhs => by
      show MiniExpr.assign _ _ _ = MiniExpr.assign _ _ _
      rw [toMiniTarget_weaken t, toMiniExpr_weaken rhs]
  | .update t _ isPrefix => by
      cases isPrefix
      · show MiniExpr.postfix _ _ = MiniExpr.postfix _ _
        rw [toMiniTarget_weaken t]
      · show MiniExpr.unary _ _ = MiniExpr.unary _ _
        rw [toMiniTarget_weaken t]
  | .await x => by
      show MiniExpr.await _ = MiniExpr.await _
      rw [toMiniExpr_weaken x]
  | .call f args => by
      show MiniExpr.call _ _ = MiniExpr.call _ _
      rw [toMiniExpr_weaken f, toMiniExprs_weaken args]
  | .new f args => by
      show MiniExpr.new _ _ = MiniExpr.new _ _
      rw [toMiniExpr_weaken f, toMiniExprs_weaken args]
  | .dot o n => by
      show MiniExpr.dot _ n = MiniExpr.dot _ n
      rw [toMiniExpr_weaken o]
  | .index o i => by
      show MiniExpr.index _ _ = MiniExpr.index _ _
      rw [toMiniExpr_weaken o, toMiniExpr_weaken i]
  | .privateDot o n => by
      show MiniExpr.privateDot _ n = MiniExpr.privateDot _ n
      rw [toMiniExpr_weaken o]
  | .privateName _ => rfl
  | .chain base hd tl => by
      show MiniExpr.chain _ _ = MiniExpr.chain _ _
      rw [toMiniExpr_weaken base, toMiniChainLink_weaken hd, toMiniChainLinks_weaken tl]
  | .importMeta => rfl
  | .importCall spec opts => by
      show MiniExpr.importCall _ _ = MiniExpr.importCall _ _
      rw [toMiniExpr_weaken spec, toMiniOptExpr_weaken opts]
  | .classAnon ds her body => by
      show MiniExpr.classExpr _ _ _ _ = MiniExpr.classExpr _ _ _ _
      rw [toMiniExprs_weaken ds, toMiniOptExpr_weaken her, toMiniClassElems_weaken body]
  | .classSelf ds her body => by
      show MiniExpr.classExpr _ _ _ _ = MiniExpr.classExpr _ _ _ _
      rw [toMiniExprs_weaken ds, toMiniOptExpr_weaken her, toMiniClassElems_weaken body]
  | .seq a b => by
      show MiniExpr.seq _ _ = MiniExpr.seq _ _
      rw [toMiniExpr_weaken a, toMiniExpr_weaken b]
  | .binary a _ b => by
      show MiniExpr.binary _ _ _ = MiniExpr.binary _ _ _
      rw [toMiniExpr_weaken a, toMiniExpr_weaken b]
  | .ternary a b d => by
      show MiniExpr.ternary _ _ _ = MiniExpr.ternary _ _ _
      rw [toMiniExpr_weaken a, toMiniExpr_weaken b, toMiniExpr_weaken d]
  | .arrow _ _ body => by
      show MiniExpr.arrow _ _ = MiniExpr.arrow _ _
      rw [toMiniArrowBody_weaken body]
  | .func _ _ _ _ body => by
      show MiniExpr.func _ _ _ _ _ = MiniExpr.func _ _ _ _ _
      rw [toMiniBlock_weaken body]
  | .funcSelf _ _ _ _ body => by
      show MiniExpr.func _ _ _ _ _ = MiniExpr.func _ _ _ _ _
      rw [toMiniBlock_weaken body]
  | .spread x => by
      show MiniExpr.spread _ = MiniExpr.spread _
      rw [toMiniExpr_weaken x]
  | .template tag head parts => by
      show MiniExpr.template _ head _ = MiniExpr.template _ head _
      rw [toMiniOptExpr_weaken tag, toMiniTemplateParts_weaken parts]
  | .unary op x => by
      show MiniExpr.unary op _ = MiniExpr.unary op _
      rw [toMiniExpr_weaken x]
  | .yield x => by
      show MiniExpr.yield _ = MiniExpr.yield _
      rw [toMiniOptExpr_weaken x]
  | .yieldFrom x => by
      show MiniExpr.yieldFrom _ = MiniExpr.yieldFrom _
      rw [toMiniExpr_weaken x]
termination_by structural e

theorem toMiniTarget_weaken {c m : Nat} (t : Global.Target c m g) :
    toMiniTarget (Target.weaken h t) = toMiniTarget t :=
  match t with
  | .mut _ => rfl
  | .unsafeExt _ => rfl
  | .dot o _ => by simp [Target.weaken, toMiniTarget, toMiniExpr_weaken o]
  | .privateDot o _ => by simp [Target.weaken, toMiniTarget, toMiniExpr_weaken o]
  | .superDot _ => rfl
  | .superIndex i => by simp [Target.weaken, toMiniTarget, toMiniExpr_weaken i]
  | .index o i => by
      simp [Target.weaken, toMiniTarget, toMiniExpr_weaken o, toMiniExpr_weaken i]
termination_by structural t

theorem toMiniChainLink_weaken {c m : Nat} (l : Global.ChainLink c m g) :
    toMiniChainLink (ChainLink.weaken h l) = toMiniChainLink l :=
  match l with
  | .dot _ _ => rfl
  | .privateDot _ _ => rfl
  | .index _ i => by simp [ChainLink.weaken, toMiniChainLink, toMiniExpr_weaken i]
  | .call _ args => by simp [ChainLink.weaken, toMiniChainLink, toMiniExprs_weaken args]
termination_by structural l

theorem toMiniChainLinks_weaken {c m : Nat} (l : Global.ChainLinks c m g) :
    toMiniChainLinks (ChainLinks.weaken h l) = toMiniChainLinks l :=
  match l with
  | .nil => rfl
  | .cons hd tl => by
      simp [ChainLinks.weaken, toMiniChainLinks, toMiniChainLink_weaken hd,
        toMiniChainLinks_weaken tl]
termination_by structural l

theorem toMiniExprs_weaken {c m : Nat} (l : Global.Exprs c m g) :
    toMiniExprs (Exprs.weaken h l) = toMiniExprs l :=
  match l with
  | .nil => rfl
  | .cons e r => by
      simp [Exprs.weaken, toMiniExprs, toMiniExpr_weaken e, toMiniExprs_weaken r]
termination_by structural l

theorem toMiniOptExpr_weaken {c m : Nat} (o : Global.OptExpr c m g) :
    toMiniOptExpr (OptExpr.weaken h o) = toMiniOptExpr o :=
  match o with
  | .none => rfl
  | .some e => by simp [OptExpr.weaken, toMiniOptExpr, toMiniExpr_weaken e]
termination_by structural o

theorem toMiniArrayElem_weaken {c m : Nat} (e : Global.ArrayElem c m g) :
    toMiniArrayElem (ArrayElem.weaken h e) = toMiniArrayElem e :=
  match e with
  | .elem e => by simp [ArrayElem.weaken, toMiniArrayElem, toMiniExpr_weaken e]
  | .hole => rfl
termination_by structural e

theorem toMiniArrayElems_weaken {c m : Nat} (l : Global.ArrayElems c m g) :
    toMiniArrayElems (ArrayElems.weaken h l) = toMiniArrayElems l :=
  match l with
  | .nil => rfl
  | .cons e r => by
      simp [ArrayElems.weaken, toMiniArrayElems, toMiniArrayElem_weaken e,
        toMiniArrayElems_weaken r]
termination_by structural l

theorem toMiniTemplatePart_weaken {c m : Nat} (p : Global.TemplatePart c m g) :
    toMiniTemplatePart (TemplatePart.weaken h p) = toMiniTemplatePart p :=
  match p with
  | .mk e _ => by simp [TemplatePart.weaken, toMiniTemplatePart, toMiniExpr_weaken e]
termination_by structural p

theorem toMiniTemplateParts_weaken {c m : Nat} (l : Global.TemplateParts c m g) :
    toMiniTemplateParts (TemplateParts.weaken h l) = toMiniTemplateParts l :=
  match l with
  | .nil => rfl
  | .cons p r => by
      simp [TemplateParts.weaken, toMiniTemplateParts, toMiniTemplatePart_weaken p,
        toMiniTemplateParts_weaken r]
termination_by structural l

theorem toMiniPropName_weaken {c m : Nat} (n : Global.PropName c m g) :
    toMiniPropName (PropName.weaken h n) = toMiniPropName n :=
  match n with
  | .ident _ => rfl
  | .private_ _ => rfl
  | .string _ => rfl
  | .number _ => rfl
  | .computed e => by simp [PropName.weaken, toMiniPropName, toMiniExpr_weaken e]
termination_by structural n

theorem toMiniProperty_weaken {c m : Nat} (p : Global.Property c m g) :
    toMiniProperty (Property.weaken h p) = toMiniProperty p :=
  match p with
  | .keyValue k v => by
      simp [Property.weaken, toMiniProperty, toMiniPropName_weaken k, toMiniExpr_weaken v]
  | .spread e => by simp [Property.weaken, toMiniProperty, toMiniExpr_weaken e]
  | .method _ k _ _ body => by
      simp [Property.weaken, toMiniProperty, toMiniPropName_weaken k, toMiniBlock_weaken body]
termination_by structural p

theorem toMiniProperties_weaken {c m : Nat} (l : Global.Properties c m g) :
    toMiniProperties (Properties.weaken h l) = toMiniProperties l :=
  match l with
  | .nil => rfl
  | .cons p r => by
      simp [Properties.weaken, toMiniProperties, toMiniProperty_weaken p,
        toMiniProperties_weaken r]
termination_by structural l

theorem toMiniClassElem_weaken {c m : Nat} (e : Global.ClassElem c m g) :
    toMiniClassElem (ClassElem.weaken h e) = toMiniClassElem e :=
  match e with
  | .method ds _ _ k _ _ body => by
      simp [ClassElem.weaken, toMiniClassElem, toMiniExprs_weaken ds, toMiniPropName_weaken k,
        toMiniBlock_weaken body]
  | .field ds _ k init => by
      simp [ClassElem.weaken, toMiniClassElem, toMiniExprs_weaken ds, toMiniPropName_weaken k,
        toMiniOptExpr_weaken init]
  | .staticBlock body => by
      simp [ClassElem.weaken, toMiniClassElem, toMiniBlock_weaken body]
termination_by structural e

theorem toMiniClassElems_weaken {c m : Nat} (l : Global.ClassElems c m g) :
    toMiniClassElems (ClassElems.weaken h l) = toMiniClassElems l :=
  match l with
  | .nil => rfl
  | .cons e r => by
      simp [ClassElems.weaken, toMiniClassElems, toMiniClassElem_weaken e,
        toMiniClassElems_weaken r]
termination_by structural l

theorem toMiniArrowBody_weaken {c m : Nat} (b : Global.ArrowBody c m g) :
    toMiniArrowBody (ArrowBody.weaken h b) = toMiniArrowBody b :=
  match b with
  | .expr e => by simp [ArrowBody.weaken, toMiniArrowBody, toMiniExpr_weaken e]
  | .block b => by simp [ArrowBody.weaken, toMiniArrowBody, toMiniBlock_weaken b]
termination_by structural b

theorem toMiniForInit_weaken {c m dc dm : Nat} (i : Global.ForInit c m g dc dm) :
    toMiniForInit (ForInit.weaken h i) = toMiniForInit i :=
  match i with
  | .none => rfl
  | .expr e => by simp [ForInit.weaken, toMiniForInit, toMiniExpr_weaken e]
  | .constDecl init => by simp [ForInit.weaken, toMiniForInit, toMiniExpr_weaken init]
  | .letDecl init => by simp [ForInit.weaken, toMiniForInit, toMiniOptExpr_weaken init]
termination_by structural i

theorem toMiniForHead_weaken {c m dc dm : Nat} (head : Global.ForHead c m g dc dm) :
    toMiniForHead (ForHead.weaken h head) = toMiniForHead head :=
  match head with
  | .target t => by simp [ForHead.weaken, toMiniForHead, toMiniTarget_weaken t]
  | .constBind => rfl
  | .letBind => rfl
termination_by structural head

theorem toMiniSwitchCase_weaken {c m : Nat} (k : Global.SwitchCase c m g) :
    toMiniSwitchCase (SwitchCase.weaken h k) = toMiniSwitchCase k :=
  match k with
  | .case t b => by
      simp [SwitchCase.weaken, toMiniSwitchCase, toMiniExpr_weaken t, toMiniBlock_weaken b]
  | .default b => by simp [SwitchCase.weaken, toMiniSwitchCase, toMiniBlock_weaken b]
termination_by structural k

theorem toMiniSwitchCases_weaken {c m : Nat} (l : Global.SwitchCases c m g) :
    toMiniSwitchCases (SwitchCases.weaken h l) = toMiniSwitchCases l :=
  match l with
  | .nil => rfl
  | .cons k r => by
      simp [SwitchCases.weaken, toMiniSwitchCases, toMiniSwitchCase_weaken k,
        toMiniSwitchCases_weaken r]
termination_by structural l

theorem toMiniOptBlock_weaken {c m : Nat} (b : Global.OptBlock c m g) :
    toMiniOptBlock (OptBlock.weaken h b) = toMiniOptBlock b :=
  match b with
  | .none => rfl
  | .some b => by simp [OptBlock.weaken, toMiniOptBlock, toMiniBlock_weaken b]
termination_by structural b

theorem toMiniTryTail_weaken {c m : Nat} (tail : Global.TryTail c m g) :
    toMiniTryTail (TryTail.weaken h tail) = toMiniTryTail tail :=
  match tail with
  | .catch_ body .none => by
      simp [TryTail.weaken, toMiniTryTail, OptBlock.weaken, toMiniBlock_weaken body]
  | .catch_ body (.some b) => by
      simp [TryTail.weaken, toMiniTryTail, OptBlock.weaken, toMiniBlock_weaken body,
        toMiniBlock_weaken b]
  | .finallyOnly b => by simp [TryTail.weaken, toMiniTryTail, toMiniBlock_weaken b]
termination_by structural tail

/-- Weakening does not change the statement a tree denotes.

Unlike the cases above, these are written as a `show` that names the shape
both sides reduce to, followed by the rewrites: `Stmt` is indexed by what
the statement binds, and asking `simp` to unfold `Stmt.weaken` there makes
it reason about that dependency, which is needlessly expensive. -/
theorem toMiniStmt_weaken {c m dc dm : Nat} (s : Global.Stmt c m g dc dm) :
    toMiniStmt (Stmt.weaken h s) = toMiniStmt s :=
  match s with
  | .expr e => congrArg MiniStatement.expr (toMiniExpr_weaken e)
  | .constDecl init => by
      show MiniStatement.decl _ _ = MiniStatement.decl _ _
      rw [toMiniExpr_weaken init]
  | .letDecl init => by
      show MiniStatement.decl _ _ = MiniStatement.decl _ _
      rw [toMiniOptExpr_weaken init]
  | .usingDecl _ init => by
      show MiniStatement.using_ _ _ = MiniStatement.using_ _ _
      rw [toMiniExpr_weaken init]
  | .block b => congrArg MiniStatement.block (toMiniBlock_weaken b)
  | .if_ cond t e => by
      show MiniStatement.if_ _ _ _ = MiniStatement.if_ _ _ _
      rw [toMiniExpr_weaken cond, toMiniBlock_weaken t, toMiniOptBlock_weaken e]
  | .while_ cond b => by
      show MiniStatement.while_ _ _ = MiniStatement.while_ _ _
      rw [toMiniExpr_weaken cond, toMiniBlock_weaken b]
  | .doWhile b cond => by
      show MiniStatement.doWhile _ _ = MiniStatement.doWhile _ _
      rw [toMiniBlock_weaken b, toMiniExpr_weaken cond]
  | .for_ init cond step body => by
      show MiniStatement.for_ _ _ _ _ = MiniStatement.for_ _ _ _ _
      rw [toMiniForInit_weaken init, toMiniOptExpr_weaken cond, toMiniOptExpr_weaken step,
        toMiniBlock_weaken body]
  | .forIn head obj body => by
      show MiniStatement.forIn _ _ _ = MiniStatement.forIn _ _ _
      rw [toMiniForHead_weaken head, toMiniExpr_weaken obj, toMiniBlock_weaken body]
  | .forOf head obj body => by
      show MiniStatement.forOf _ _ _ = MiniStatement.forOf _ _ _
      rw [toMiniForHead_weaken head, toMiniExpr_weaken obj, toMiniBlock_weaken body]
  | .funcDecl _ _ _ _ body => by
      show MiniStatement.funcDecl _ _ _ _ _ = MiniStatement.funcDecl _ _ _ _ _
      rw [toMiniBlock_weaken body]
  | .classDecl ds her body => by
      show MiniStatement.classDecl _ _ _ _ = MiniStatement.classDecl _ _ _ _
      rw [toMiniExprs_weaken ds, toMiniOptExpr_weaken her, toMiniClassElems_weaken body]
  | .return_ e => congrArg MiniStatement.return_ (toMiniOptExpr_weaken e)
  | .throw e => congrArg MiniStatement.throw (toMiniExpr_weaken e)
  | .break_ _ => rfl
  | .continue_ _ => rfl
  | .labelled l s => congrArg (MiniStatement.labelled l) (toMiniStmt_weaken s)
  | .switch d cs => by
      show MiniStatement.switch _ _ = MiniStatement.switch _ _
      rw [toMiniExpr_weaken d, toMiniSwitchCases_weaken cs]
  | .try_ b tail => by
      show MiniStatement.try_ _ _ = MiniStatement.try_ _ _
      rw [toMiniBlock_weaken b, toMiniTryTail_weaken tail]
termination_by structural s

theorem toMiniBlock_weaken {c m : Nat} (b : Global.Block c m g) :
    toMiniBlock (Block.weaken h b) = toMiniBlock b :=
  match b with
  | .nil => rfl
  | .cons s r => by
      simp [Block.weaken, toMiniBlock, toMiniStmt_weaken s, toMiniBlock_weaken r]
termination_by structural b

end

/-! ## Module items

An export specifier names a local binding, so `ExportLocal.weaken` needs no
inclusion at all; the rest follow the tree. -/

theorem toMiniExportLocal_weaken {c m : Nat} (e : Global.ExportLocal c m g) :
    toMiniExportLocal (ExportLocal.weaken (g' := g') e) = toMiniExportLocal e :=
  match e with
  | .const _ _ => rfl
  | .mut _ _ => rfl

theorem toMiniExportLocals_weaken {c m : Nat} (l : Global.ExportLocals c m g) :
    toMiniExportLocals (ExportLocals.weaken h l) = toMiniExportLocals l :=
  match l with
  | .nil => rfl
  | .cons e r => by
      simp [ExportLocals.weaken, toMiniExportLocals, toMiniExportLocal_weaken (g' := g') e,
        toMiniExportLocals_weaken r]
termination_by structural l

theorem toMiniModuleItem_weaken {c m dc dm : Nat} (i : Global.ModuleItem c m g dc dm) :
    toMiniModuleItem (ModuleItem.weaken h i) = toMiniModuleItem i :=
  match i with
  | .stmt s => by simp [ModuleItem.weaken, toMiniModuleItem, toMiniStmt_weaken h s]
  | .importBare _ _ => rfl
  | .importClause _ => rfl
  | .exportFrom _ _ _ => rfl
  | .exportAll _ _ _ => rfl
  | .exportDefaultExpr e => by
      simp [ModuleItem.weaken, toMiniModuleItem, toMiniExpr_weaken h e]
  | .exportLocals specs => by
      simp [ModuleItem.weaken, toMiniModuleItem, toMiniExportLocals_weaken h specs]
  | .exportDecl s => by simp [ModuleItem.weaken, toMiniModuleItem, toMiniStmt_weaken h s]

theorem toMiniModuleItems_weaken {c m : Nat} (l : Global.ModuleItems c m g) :
    toMiniModuleItems (ModuleItems.weaken h l) = toMiniModuleItems l :=
  match l with
  | .nil => rfl
  | .cons i r => by
      simp [ModuleItems.weaken, toMiniModuleItems, toMiniModuleItem_weaken h i,
        toMiniModuleItems_weaken r]
termination_by structural l

/-- Weakening the globals of a whole program leaves the program it denotes
unchanged. -/

theorem toMiniProgram_weakenTo (p : Program) {g' : Finset NEString} (h : p.globals ⊆ g') :
    toMiniProgram (p.weakenTo h) = toMiniProgram p := by
  simp [Program.weakenTo, toMiniProgram, toMiniModuleItems_weaken h p.items]

end Naming

/-! ## What is printed

`printProgram` and `printExpr` go through `toMini`, so weakening does not
change the source they produce either. -/

/-- Weakening the globals of a program does not change the source it is
printed as. -/
theorem printProgram_weakenTo (p : Program) {g' : Finset NEString} (h : p.globals ⊆ g') :
    printProgram (p.weakenTo h) = printProgram p := by
  simp [printProgram, toMiniProgram_weakenTo p h]

/-- Weakening the globals of an expression does not change the source it is
printed as. -/
theorem printExpr_weaken {c m : Nat} {g g' : Finset NEString} (h : g ⊆ g') (e : Global.Expr c m g) :
    printExpr (Expr.weaken h e) = printExpr e := by
  simp [printExpr, toMiniExpr_weaken h e]

/-- Putting two scoped expressions into the union of their globals changes
neither of them. -/
theorem printScopedExpr_union {c m : Nat} (a b : ScopedExpr c m) :
    printExpr (ScopedExpr.union a b).1 = printScopedExpr a ∧
      printExpr (ScopedExpr.union a b).2 = printScopedExpr b :=
  ⟨printExpr_weaken _ a.expr, printExpr_weaken _ b.expr⟩

end Language.JavaScript.BrujinAST
