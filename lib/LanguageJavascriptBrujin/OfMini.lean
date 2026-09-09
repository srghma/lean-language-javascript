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

abbrev ConvM := Except String

def fail (msg : String) : ConvM α := .error ("BrujinAST: " ++ msg)

def resolveVar (env : Env) (c m : Nat) (n : NEString) : ConvM (Expr c m) :=
  match idxIdent? n with
  | some (true, i) =>
      if h : i < c then pure (.constVar ⟨i, h⟩)
      else fail s!"the de Bruijn index c#{i} is out of range: {c} const bindings are in scope"
  | some (false, i) =>
      if h : i < m then pure (.mutVar ⟨i, h⟩)
      else fail s!"the de Bruijn index l#{i} is out of range: {m} mutable bindings are in scope"
  | none =>
    match env.lookup n with
    | none => pure (.unsafeGlobal n)
    | some b =>
        if b.isConst then
          match constIndex? c b.level with
          | some i => pure (.constVar i)
          | none => pure (.unsafeGlobal n)
        else
          match mutIndex? m b.level with
          | some i => pure (.mutVar i)
          | none => pure (.unsafeGlobal n)

def resolveTarget (env : Env) (c m : Nat) (n : NEString) : ConvM (Target c m) :=
  match idxIdent? n with
  | some (true, i) => fail s!"assignment to the const variable c#{i}"
  | some (false, i) =>
      if h : i < m then pure (.mut ⟨i, h⟩)
      else fail s!"the de Bruijn index l#{i} is out of range: {m} mutable bindings are in scope"
  | none =>
    match env.lookup n with
    | none => pure (.unsafeGlobal n)
    | some b =>
        if b.isConst then
          fail s!"assignment to the const variable {n.val}"
        else
          match mutIndex? m b.level with
          | some i => pure (.mut i)
          | none => pure (.unsafeGlobal n)

def resolveExportLocal (env : Env) (c m : Nat) (n exported : NEString) :
    ConvM (ExportLocal c m) :=
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

def binderName : MiniExpr → ConvM NEString
  | .ident n => pure n
  | .array _ | .object _ => fail "a destructuring pattern in a binder"
  | .assign _ _ _ => fail "a default value in a binder"
  | _ => fail "a binder that is not a name"

def paramNamesOf (params : List MiniExpr) : ConvM (List NEString) :=
  params.mapM binderName

def splitDecl : MiniStatement → List MiniStatement
  | .empty => []
  | .decl kind decls => decls.toList.map fun d => .decl kind ⟨d, []⟩
  | s => [s]

def expandStmts (l : List MiniStatement) : List MiniStatement := l.flatMap splitDecl

def expandItems (items : List MiniModuleItem) : List MiniModuleItem :=
  items.flatMap fun
    | .stmt s => (splitDecl s).map .stmt
    | .exportDecl (.decl s) => (splitDecl s).map fun s => .exportDecl (.decl s)
    | it => [it]

structure StmtRes (c m : Nat) where
  dc : Nat
  dm : Nat
  stmt : Stmt c m dc dm
  binds : List Binding

structure ItemRes (c m : Nat) where
  dc : Nat
  dm : Nat
  item : ModuleItem c m dc dm
  binds : List Binding

mutual

partial def ofExpr (env : Env) (c m : Nat) (e : MiniExpr) : ConvM (Expr c m) := do
  match e with
  | .ident n => resolveVar env c m n
  | .number raw => pure (.number raw)
  | .string v => pure (.string v)
  | .regex raw => pure (.regex raw)
  | .null => pure .null
  | .true_ => pure .true_
  | .false_ => pure .false_
  | .this => pure .this
  | .array els => pure (.array (ArrayElems.ofList (← els.mapM (ofArrayElem env c m))))
  | .object ps => pure (.object (Properties.ofList (← ps.mapM (ofProperty env c m))))
  | .assign lhs op rhs =>
      pure (.assign (← ofTarget env c m lhs) op (← ofExpr env c m rhs))
  | .postfix x op => pure (.update (← ofTarget env c m x) op false)
  | .unary op x =>
      match op with
      | .preIncr => pure (.update (← ofTarget env c m x) .incr true)
      | .preDecr => pure (.update (← ofTarget env c m x) .decr true)
      | _ => pure (.unary op (← ofExpr env c m x))
  | .await x => pure (.await (← ofExpr env c m x))
  | .call f args => pure (.call (← ofExpr env c m f) (Exprs.ofList (← args.mapM (ofExpr env c m))))
  | .new f args => pure (.new (← ofExpr env c m f) (Exprs.ofList (← args.mapM (ofExpr env c m))))
  | .dot o n => pure (.dot (← ofExpr env c m o) n)
  | .index o i => pure (.index (← ofExpr env c m o) (← ofExpr env c m i))
  | .classExpr name heritage body =>
      let her ← ofOptExpr env c m heritage
      match name with
      | none => pure (.classAnon her (← ofClassElems env c m body))
      | some n =>
          pure (.classSelf her (← ofClassElems (env.pushConsts c [n]) (c + 1) m body))
  | .seq a b => pure (.seq (← ofExpr env c m a) (← ofExpr env c m b))
  | .binary a op b => pure (.binary (← ofExpr env c m a) op (← ofExpr env c m b))
  | .ternary a b d =>
      pure (.ternary (← ofExpr env c m a) (← ofExpr env c m b) (← ofExpr env c m d))
  | .arrow params body =>
      let ps ← paramNamesOf params
      let inner := env.pushMuts m ps
      match body with
      | .expr x => pure (.arrow ps.length (.expr (← ofExpr inner c (m + ps.length) x)))
      | .block b => pure (.arrow ps.length (.block (← ofBlock inner c (m + ps.length) b)))
  | .func isAsync isGen name params body =>
      let ps ← paramNamesOf params
      match name with
      | none =>
          let inner := env.pushMuts m ps
          pure (.func isAsync isGen ps.length (← ofBlock inner c (m + ps.length) body))
      | some n =>
          let inner := (env.pushConsts c [n]).pushMuts m ps
          pure (.funcSelf isAsync isGen ps.length (← ofBlock inner (c + 1) (m + ps.length) body))
  | .spread x => pure (.spread (← ofExpr env c m x))
  | .template tag head parts =>
      pure (.template (← ofOptExpr env c m tag) head
        (TemplateParts.ofList (← parts.mapM fun p => do
          pure (TemplatePart.mk (← ofExpr env c m p.expr) p.suffix))))
  | .yield x => pure (.yield (← ofOptExpr env c m x))
  | .yieldFrom x => pure (.yieldFrom (← ofExpr env c m x))

partial def ofOptExpr (env : Env) (c m : Nat) : Option MiniExpr → ConvM (OptExpr c m)
  | none => pure .none
  | some e => do pure (.some (← ofExpr env c m e))

partial def ofTarget (env : Env) (c m : Nat) (e : MiniExpr) : ConvM (Target c m) := do
  match e with
  | .ident n => resolveTarget env c m n
  | .dot o n => pure (.dot (← ofExpr env c m o) n)
  | .index o i => pure (.index (← ofExpr env c m o) (← ofExpr env c m i))
  | _ => fail "an assignment target that is not a variable or a member"

partial def ofArrayElem (env : Env) (c m : Nat) : MiniArrayElement → ConvM (ArrayElem c m)
  | .hole => pure .hole
  | .elem e => do pure (.elem (← ofExpr env c m e))

partial def ofPropName (env : Env) (c m : Nat) : MiniPropertyName → ConvM (PropName c m)
  | .ident n => pure (.ident n)
  | .string v => pure (.string v)
  | .number raw => pure (.number raw)
  | .computed e => do pure (.computed (← ofExpr env c m e))

partial def ofProperty (env : Env) (c m : Nat) : MiniProperty → ConvM (Property c m)
  | .keyValue k v => do pure (.keyValue (← ofPropName env c m k) (← ofExpr env c m v))
  | .shorthand n => do pure (.keyValue (.ident n) (← resolveVar env c m n))
  | .method kind k params body => do
      let ps ← paramNamesOf params
      pure (.method kind (← ofPropName env c m k) ps.length
        (← ofBlock (env.pushMuts m ps) c (m + ps.length) body))

partial def ofClassElem (env : Env) (c m : Nat) (el : MiniClassElement) :
    ConvM (ClassElem c m) := do
  let ps ← paramNamesOf el.params
  pure (.mk el.isStatic el.kind (← ofPropName env c m el.key) ps.length
    (← ofBlock (env.pushMuts m ps) c (m + ps.length) el.body))

partial def ofClassElems (env : Env) (c m : Nat) (els : List MiniClassElement) :
    ConvM (ClassElems c m) := do
  pure (ClassElems.ofList (← els.mapM (ofClassElem env c m)))

partial def ofSwitchCase (env : Env) (c m : Nat) : MiniSwitchCase → ConvM (SwitchCase c m)
  | .case t b => do pure (.case (← ofExpr env c m t) (← ofBlock env c m b))
  | .default b => do pure (.default (← ofBlock env c m b))

partial def ofBody (env : Env) (c m : Nat) : MiniStatement → ConvM (Block c m)
  | .block b => ofBlock env c m b
  | .empty => pure .nil
  | s => ofBlock env c m [s]

partial def ofOptBody (env : Env) (c m : Nat) : Option MiniStatement → ConvM (OptBlock c m)
  | none => pure .none
  | some s => do pure (.some (← ofBody env c m s))

partial def ofBlock (env : Env) (c m : Nat) (stmts : List MiniStatement) :
    ConvM (Block c m) :=
  ofStmts env c m (expandStmts stmts)

partial def ofStmts (env : Env) (c m : Nat) : List MiniStatement → ConvM (Block c m)
  | [] => pure .nil
  | s :: rest => do
      let r ← ofStmt env c m s
      let tl ← ofStmts (r.binds.reverse ++ env) (c + r.dc) (m + r.dm) rest
      pure (.cons r.stmt tl)

partial def ofForInOf (env : Env) (c m : Nat) (isOf : Bool) (head : MiniForHead)
    (obj : MiniExpr) (body : MiniStatement) : ConvM (StmtRes c m) := do
  let obj' ← ofExpr env c m obj
  match head with
  | .pattern lhs =>
      let t ← ofTarget env c m lhs
      let b ← ofBody env c m body
      return ⟨0, 0, if isOf then .forOf (.target t) obj' b else .forIn (.target t) obj' b, []⟩
  | .decl kind lhs =>
      let n ← binderName lhs
      match kind with
      | .const =>
          let b ← ofBody (env.pushConsts c [n]) (c + 1) m body
          return ⟨0, 0, if isOf then .forOf .constBind obj' b else .forIn .constBind obj' b, []⟩
      | _ =>
          let b ← ofBody (env.pushMuts m [n]) c (m + 1) body
          return ⟨0, 0, if isOf then .forOf .letBind obj' b else .forIn .letBind obj' b, []⟩

partial def ofForC (env : Env) (c m : Nat) (init : MiniForInit) (cond step : Option MiniExpr)
    (body : MiniStatement) : ConvM (StmtRes c m) := do
  match init with
  | .none =>
      return ⟨0, 0, .for_ .none (← ofOptExpr env c m cond) (← ofOptExpr env c m step)
        (← ofBody env c m body), []⟩
  | .expr e =>
      let e' ← ofExpr env c m e
      return ⟨0, 0, .for_ (.expr e') (← ofOptExpr env c m cond) (← ofOptExpr env c m step)
        (← ofBody env c m body), []⟩
  | .decl kind decls =>
      match decls.tl with
      | _ :: _ => fail "a `for` clause that declares several variables"
      | [] =>
        let d := decls.hd
        let n ← binderName d.lhs
        match kind with
        | .const =>
            match d.init with
            | none => fail "a const declaration without an initialiser"
            | some i =>
                let i' ← ofExpr env c m i
                let inner := env.pushConsts c [n]
                return ⟨0, 0, .for_ (.constDecl i') (← ofOptExpr inner (c + 1) m cond)
                  (← ofOptExpr inner (c + 1) m step) (← ofBody inner (c + 1) m body), []⟩
        | _ =>
            let i' ← ofOptExpr env c m d.init
            let inner := env.pushMuts m [n]
            return ⟨0, 0, .for_ (.letDecl i') (← ofOptExpr inner c (m + 1) cond)
              (← ofOptExpr inner c (m + 1) step) (← ofBody inner c (m + 1) body), []⟩

partial def ofStmt (env : Env) (c m : Nat) (s : MiniStatement) : ConvM (StmtRes c m) := do
  match s with
  | .expr e => return ⟨0, 0, .expr (← ofExpr env c m e), []⟩
  | .empty => return ⟨0, 0, .block .nil, []⟩
  | .decl kind decls =>
      match decls.tl with
      | _ :: _ => fail "a declaration of several variables (it should have been split)"
      | [] =>
        let d := decls.hd
        let n ← binderName d.lhs
        match kind with
        | .const =>
            match d.init with
            | none => fail "a const declaration without an initialiser"
            | some i => return ⟨1, 0, .constDecl (← ofExpr env c m i), [⟨n, true, c⟩]⟩
        | _ => return ⟨0, 1, .letDecl (← ofOptExpr env c m d.init), [⟨n, false, m⟩]⟩
  | .block b => return ⟨0, 0, .block (← ofBlock env c m b), []⟩
  | .if_ cond t e =>
      return ⟨0, 0, .if_ (← ofExpr env c m cond) (← ofBody env c m t)
        (← ofOptBody env c m e), []⟩
  | .while_ cond b => return ⟨0, 0, .while_ (← ofExpr env c m cond) (← ofBody env c m b), []⟩
  | .doWhile b cond => return ⟨0, 0, .doWhile (← ofBody env c m b) (← ofExpr env c m cond), []⟩
  | .for_ init cond step body => ofForC env c m init cond step body
  | .forIn head obj body => ofForInOf env c m false head obj body
  | .forOf head obj body => ofForInOf env c m true head obj body
  | .funcDecl isAsync isGen name params body =>
      let ps ← paramNamesOf params
      let inner := (env.pushConsts c [name]).pushMuts m ps
      let b ← ofBlock inner (c + 1) (m + ps.length) body
      return ⟨1, 0, .funcDecl isAsync isGen ps.length b, [⟨name, true, c⟩]⟩
  | .classDecl name heritage body =>
      let her ← ofOptExpr env c m heritage
      let els ← ofClassElems (env.pushConsts c [name]) (c + 1) m body
      return ⟨1, 0, .classDecl her els, [⟨name, true, c⟩]⟩
  | .return_ e => return ⟨0, 0, .return_ (← ofOptExpr env c m e), []⟩
  | .throw e => return ⟨0, 0, .throw (← ofExpr env c m e), []⟩
  | .break_ l => return ⟨0, 0, .break_ l, []⟩
  | .continue_ l => return ⟨0, 0, .continue_ l, []⟩
  | .labelled l s' =>
      let ⟨dc, dm, st, _⟩ ← ofStmt env c m s'
      match dc, dm, st with
      | 0, 0, st' => return ⟨0, 0, .labelled l st', []⟩
      | _, _, _ => fail "a labelled statement that declares a variable"
  | .switch d cases =>
      return ⟨0, 0, .switch (← ofExpr env c m d)
        (SwitchCases.ofList (← cases.mapM (ofSwitchCase env c m))), []⟩
  | .try_ body tail =>
      let b ← ofBlock env c m body
      match tail with
      | .finallyOnly fb => return ⟨0, 0, .try_ b (.finallyOnly (← ofBlock env c m fb)), []⟩
      | .catches cs fin =>
          match cs.tl with
          | _ :: _ => fail "a `try` with several catch clauses"
          | [] =>
            let cat := cs.hd
            match cat.guard with
            | some _ => fail "a catch clause with a guard"
            | none =>
                let n ← binderName cat.param
                let cb ← ofBlock (env.pushMuts m [n]) c (m + 1) cat.body
                let f : OptBlock c m ←
                  match fin with
                  | .none => pure .none
                  | .some fb => do pure (.some (← ofBlock env c m fb))
                return ⟨0, 0, .try_ b (.catch_ cb f), []⟩
  | .with_ _ _ => fail "a `with` statement (its scope is dynamic)"

end

def ofModuleItem (env : Env) (c m : Nat) : MiniModuleItem → ConvM (ItemRes c m)
  | .stmt s => do
      let r ← ofStmt env c m s
      return ⟨r.dc, r.dm, .stmt r.stmt, r.binds⟩
  | .importDecl (.bare mod) => pure ⟨0, 0, .importBare mod, []⟩
  | .importDecl (.clause cl) => do
      let specs := cl.named.getD []
      let names := specs.map (·.name)
      let locals :=
        cl.default_.toList ++ cl.namespace_.toList ++ specs.map fun s => s.alias_.getD s.name
      match ImportClause.mk? cl.mod cl.default_.isSome cl.namespace_.isSome names with
      | none => fail "an import that binds nothing"
      | some clause =>
          return ⟨clause.count, 0, .importClause clause,
            locals.zipIdx.map fun (n, j) => ⟨n, true, c + j⟩⟩
  | .exportDecl (.fromClause specs mod) => pure ⟨0, 0, .exportFrom specs mod, []⟩
  | .exportDecl (.locals specs) => do
      let entries ← specs.mapM fun sp =>
        resolveExportLocal env c m sp.name (sp.alias_.getD sp.name)
      return ⟨0, 0, .exportLocals (ExportLocals.ofList entries), []⟩
  | .exportDecl (.decl s) => do
      let r ← ofStmt env c m s
      return ⟨r.dc, r.dm, .exportDecl r.stmt, r.binds⟩

partial def ofItems (env : Env) (c m : Nat) : List MiniModuleItem → ConvM (ModuleItems c m)
  | [] => pure .nil
  | it :: rest => do
      let r ← ofModuleItem env c m it
      let tl ← ofItems (r.binds.reverse ++ env) (c + r.dc) (m + r.dm) rest
      pure (.cons r.item tl)

def ofMiniProgram (p : MiniProgram) : ConvM Program := do
  pure ⟨← ofItems [] 0 0 (expandItems p.items)⟩

def parse (input : String) : ConvM Program := do
  ofMiniProgram (← MiniAST.parse input)

def isIdentChar (ch : Char) : Bool := ch.isAlphanum || ch == '_' || ch == '$'

inductive ScanMode where
  | code
  | subst (depth : Nat)
  | string (delim : Char)
  | template
  | lineComment
  | blockComment
deriving Repr, DecidableEq, Inhabited

partial def rewriteAux (stack : List ScanMode) (prev : Char) (cs : List Char) (acc : String) :
    String :=
  match cs with
  | [] => acc
  | ch :: rest =>
    match stack with
    | [] => acc ++ String.ofList cs
    | .string d :: st =>
        if ch == '\\' then
          match rest with
          | [] => acc.push ch
          | e :: more => rewriteAux stack e more ((acc.push ch).push e)
        else if ch == d then rewriteAux st ch rest (acc.push ch)
        else rewriteAux stack ch rest (acc.push ch)
    | .template :: st =>
        if ch == '\\' then
          match rest with
          | [] => acc.push ch
          | e :: more => rewriteAux stack e more ((acc.push ch).push e)
        else if ch == '`' then rewriteAux st ch rest (acc.push ch)
        else if ch == '$' && rest.head? == some '{' then
          rewriteAux (.subst 0 :: stack) ' ' (rest.drop 1) ((acc.push ch).push '{')
        else rewriteAux stack ch rest (acc.push ch)
    | .lineComment :: st =>
        if ch == '\n' then rewriteAux st ch rest (acc.push ch)
        else rewriteAux stack ch rest (acc.push ch)
    | .blockComment :: st =>
        if prev == '*' && ch == '/' then rewriteAux st ch rest (acc.push ch)
        else rewriteAux stack ch rest (acc.push ch)
    | m :: st =>
        if (ch == 'c' || ch == 'l') && !isIdentChar prev then
          match rest with
          | '#' :: more =>
              let ds := more.takeWhile Char.isDigit
              if ds.isEmpty then rewriteAux stack ch rest (acc.push ch)
              else
                let i := (String.ofList ds).toNat!
                let name := if ch == 'c' then (idxConstIdent i).val else (idxMutIdent i).val
                rewriteAux stack '0' (more.drop ds.length) (acc ++ name)
          | _ => rewriteAux stack ch rest (acc.push ch)
        else if ch == '"' || ch == '\'' then
          rewriteAux (.string ch :: stack) ch rest (acc.push ch)
        else if ch == '`' then rewriteAux (.template :: stack) ch rest (acc.push ch)
        else if ch == '/' && rest.head? == some '/' then
          rewriteAux (.lineComment :: stack) ' ' (rest.drop 1) ((acc.push ch).push '/')
        else if ch == '/' && rest.head? == some '*' then
          rewriteAux (.blockComment :: stack) ' ' (rest.drop 1) ((acc.push ch).push '*')
        else
          match m with
          | .subst d =>
              if ch == '{' then rewriteAux (.subst (d + 1) :: st) ch rest (acc.push ch)
              else if ch == '}' then
                if d == 0 then rewriteAux st ch rest (acc.push ch)
                else rewriteAux (.subst (d - 1) :: st) ch rest (acc.push ch)
              else rewriteAux stack ch rest (acc.push ch)
          | _ => rewriteAux stack ch rest (acc.push ch)

def rewriteIndexRefs (input : String) : String :=
  rewriteAux [.code] ' ' input.toList ""

def parseIndexed (input : String) : ConvM Program :=
  parse (rewriteIndexRefs input)

def parseIndexed! (input : String) : Program := (parseIndexed input).toOption.getD default

def parseExprIndexed (c m : Nat) (input : String) : ConvM (Expr c m) := do
  ofExpr [] c m (← MiniAST.parseExpr (rewriteIndexRefs input))

def parseExprIndexed! (c m : Nat) (input : String) : Expr c m :=
  (parseExprIndexed c m input).toOption.getD default

end Language.JavaScript.BrujinAST
