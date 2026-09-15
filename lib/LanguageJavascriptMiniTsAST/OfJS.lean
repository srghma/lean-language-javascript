import MiniTsAST.Syntax

/-!
# The JavaScript tree read as a TypeScript one

Every JavaScript program is a TypeScript program.  This file makes that
concrete: it embeds the `MiniAST` syntax tree into the `MiniTsAST` one,
by filling in the TypeScript parts — type annotations, type parameters
and arguments, member modifiers — with nothing.

The embedding is what lets the TypeScript printer be checked against the
whole JavaScript corpus and its random programs: the text it prints for
an embedded program has to be the text the JavaScript printer prints.
-/

namespace Language.TypeScript.MiniTsAST.OfJS

open Language.JavaScript
open Language.JavaScript.MiniAST renaming
  MiniExpr → JSExpr, MiniStatement → JSStatement, MiniPattern → JSPattern,
  MiniParam → JSParam, MiniProperty → JSProperty, MiniPropertyName → JSPropertyName,
  MiniClassElement → JSClassElement, MiniDeclarator → JSDeclarator,
  MiniForInit → JSForInit, MiniForHead → JSForHead, MiniSwitchCase → JSSwitchCase,
  MiniCatchClause → JSCatchClause, MiniFinallyClause → JSFinallyClause,
  MiniTryTail → JSTryTail, MiniArrayElement → JSArrayElement,
  MiniArrowBody → JSArrowBody, MiniTemplatePart → JSTemplatePart,
  MiniChainLink → JSChainLink, MiniArrayPatternElem → JSArrayPatternElem,
  MiniObjectPatternProp → JSObjectPatternProp, MiniJSXNode → JSJSXNode,
  MiniJSXAttribute → JSJSXAttribute, MiniJSXAttrValue → JSJSXAttrValue,
  MiniJSXChild → JSJSXChild, MiniModuleItem → JSModuleItem,
  MiniImportDeclaration → JSImportDeclaration, MiniImportClause → JSImportClause,
  MiniExportDeclaration → JSExportDeclaration, MiniProgram → JSProgram

/-- One specifier of an import or export clause, which carries no
`type` in JavaScript. -/
def ofSpecifier (s : Specifier) : TsSpecifier := ⟨false, s.name, s.alias_⟩

mutual

/-- An expression. -/
def ofExpr : JSExpr → MiniExpr
  | .ident n => .ident n
  | .number v => .number v
  | .string v => .string v
  | .regex r => .regex r
  | .null => .null
  | .true_ => .true_
  | .false_ => .false_
  | .this => .this
  | .superDot n => .superDot n
  | .superIndex i => .superIndex (ofExpr i)
  | .superCall args => .superCall (ofExprs args)
  | .newTarget => .newTarget
  | .array els => .array (ofArrayElements els)
  | .object props => .object (ofProperties props)
  | .assign l op r => .assign (ofExpr l) op (ofExpr r)
  | .assignPattern l r => .assignPattern (ofPattern l) (ofExpr r)
  | .await e => .await (ofExpr e)
  | .call f args => .call (ofExpr f) [] (ofExprs args)
  | .dot o n => .dot (ofExpr o) n
  | .privateDot o n => .privateDot (ofExpr o) n
  | .privateName n => .privateName n
  | .index o i => .index (ofExpr o) (ofExpr i)
  | .chain base links => .chain (ofExpr base) ⟨ofChainLink links.hd, ofChainLinks links.tl⟩
  | .importMeta => .importMeta
  | .importCall spec options =>
      .importCall (ofExpr spec) (match options with | none => none | some o => some (ofExpr o))
  | .classExpr decorators name heritage body =>
      .classExpr (ofExprs decorators) name []
        (match heritage with | none => none | some h => some ⟨ofExpr h, []⟩) []
        (ofClassElements body)
  | .seq l r => .seq (ofExpr l) (ofExpr r)
  | .binary l op r => .binary (ofExpr l) op (ofExpr r)
  | .postfix e op => .postfix (ofExpr e) op
  | .ternary c a b => .ternary (ofExpr c) (ofExpr a) (ofExpr b)
  | .arrow isAsync params body => .arrow isAsync [] (ofParams params) none (ofArrowBody body)
  | .func isAsync isGen name params body =>
      .func isAsync isGen name [] (ofParams params) none (ofStatements body)
  | .new callee args => .new (ofExpr callee) [] (ofExprs args)
  | .spread e => .spread (ofExpr e)
  | .template tag head parts =>
      .template (match tag with | none => none | some tg => some (ofExpr tg)) [] head
        (ofTemplateParts parts)
  | .unary op e => .unary op (ofExpr e)
  | .yield none => .yield none
  | .yield (some e) => .yield (some (ofExpr e))
  | .yieldFrom e => .yieldFrom (ofExpr e)
  | .jsx n => .jsx (ofJSXNode n)

def ofExprs : List JSExpr → List MiniExpr
  | [] => []
  | e :: rest => ofExpr e :: ofExprs rest

def ofArrayElements : List JSArrayElement → List MiniArrayElement
  | [] => []
  | .hole :: rest => .hole :: ofArrayElements rest
  | .elem e :: rest => .elem (ofExpr e) :: ofArrayElements rest

def ofProperties : List JSProperty → List MiniProperty
  | [] => []
  | .keyValue k v :: rest => .keyValue (ofPropertyName k) (ofExpr v) :: ofProperties rest
  | .shorthand n :: rest => .shorthand n :: ofProperties rest
  | .spread e :: rest => .spread (ofExpr e) :: ofProperties rest
  | .method kind key params body :: rest =>
      .method kind (ofPropertyName key) [] (ofParams params) none (ofStatements body)
        :: ofProperties rest

def ofPropertyName : JSPropertyName → MiniPropertyName
  | .ident n => .ident n
  | .private_ n => .private_ n
  | .string v => .string v
  | .number v => .number v
  | .computed e => .computed (ofExpr e)

def ofPattern : JSPattern → MiniPattern
  | .ident n => .ident n
  | .array els => .array (ofArrayPatternElems els)
  | .object props rest =>
      .object (ofObjectPatternProps props)
        (match rest with | none => none | some r => some (ofPattern r))
  | .withDefault p v => .withDefault (ofPattern p) (ofExpr v)
  | .target e => .target (ofExpr e)

def ofArrayPatternElems : List JSArrayPatternElem → List MiniArrayPatternElem
  | [] => []
  | .hole :: rest => .hole :: ofArrayPatternElems rest
  | .elem p :: rest => .elem (ofPattern p) :: ofArrayPatternElems rest
  | .rest p :: rest => .rest (ofPattern p) :: ofArrayPatternElems rest

def ofObjectPatternProps : List JSObjectPatternProp → List MiniObjectPatternProp
  | [] => []
  | ⟨key, value⟩ :: rest =>
      ⟨ofPropertyName key, ofPattern value⟩ :: ofObjectPatternProps rest

def ofParams : List JSParam → List MiniParam
  | [] => []
  | .plain p :: rest => .plain [] {} (ofPattern p) false none :: ofParams rest
  | .rest p :: rest => .rest [] (ofPattern p) none :: ofParams rest

def ofArrowBody : JSArrowBody → MiniArrowBody
  | .expr e => .expr (ofExpr e)
  | .block body => .block (ofStatements body)

def ofTemplateParts : List JSTemplatePart → List MiniTemplatePart
  | [] => []
  | ⟨e, suffix⟩ :: rest => ⟨ofExpr e, suffix⟩ :: ofTemplateParts rest

def ofChainLink : JSChainLink → MiniChainLink
  | .dot o n => .dot o n
  | .privateDot o n => .privateDot o n
  | .index o i => .index o (ofExpr i)
  | .call o args => .call o [] (ofExprs args)

def ofChainLinks : List JSChainLink → List MiniChainLink
  | [] => []
  | l :: rest => ofChainLink l :: ofChainLinks rest

def ofJSXNode : JSJSXNode → MiniJSXNode
  | .element name attrs children =>
      .element name [] (ofJSXAttributes attrs)
        (match children with | none => none | some cs => some (ofJSXChildren cs))
  | .fragment children => .fragment (ofJSXChildren children)

def ofJSXAttributes : List JSJSXAttribute → List MiniJSXAttribute
  | [] => []
  | .attr name value :: rest =>
      .attr name (match value with | none => none | some v => some (ofJSXAttrValue v))
        :: ofJSXAttributes rest
  | .spread e :: rest => .spread (ofExpr e) :: ofJSXAttributes rest

def ofJSXAttrValue : JSJSXAttrValue → MiniJSXAttrValue
  | .string v => .string v
  | .expr e => .expr (ofExpr e)
  | .node n => .node (ofJSXNode n)

def ofJSXChildren : List JSJSXChild → List MiniJSXChild
  | [] => []
  | .text v :: rest => .text v :: ofJSXChildren rest
  | .expr e :: rest => .expr (ofExpr e) :: ofJSXChildren rest
  | .emptyExpr :: rest => .emptyExpr :: ofJSXChildren rest
  | .node n :: rest => .node (ofJSXNode n) :: ofJSXChildren rest

def ofClassElements : List JSClassElement → List MiniClassElement
  | [] => []
  | .method decorators isStatic kind key params body :: rest =>
      .method (ofExprs decorators) { isStatic := isStatic } kind (ofPropertyName key) false []
          (ofParams params) none (some (ofStatements body))
        :: ofClassElements rest
  | .field decorators isStatic isAccessor key init :: rest =>
      .field (ofExprs decorators) { isStatic := isStatic } isAccessor (ofPropertyName key)
          false false none (match init with | none => none | some e => some (ofExpr e))
        :: ofClassElements rest
  | .staticBlock body :: rest => .staticBlock (ofStatements body) :: ofClassElements rest

def ofDeclarator : JSDeclarator → MiniDeclarator
  | ⟨lhs, init⟩ =>
      ⟨ofPattern lhs, false, none, match init with | none => none | some e => some (ofExpr e)⟩

def ofDeclarators : List JSDeclarator → List MiniDeclarator
  | [] => []
  | d :: rest => ofDeclarator d :: ofDeclarators rest

def ofForInit : JSForInit → MiniForInit
  | .none => .none
  | .expr e => .expr (ofExpr e)
  | .decl kind decls => .decl kind ⟨ofDeclarator decls.hd, ofDeclarators decls.tl⟩

def ofForHead : JSForHead → MiniForHead
  | .pattern p => .pattern (ofPattern p)
  | .decl kind p => .decl kind (ofPattern p)
  | .usingDecl isAwait p => .usingDecl isAwait (ofPattern p)

def ofSwitchCases : List JSSwitchCase → List MiniSwitchCase
  | [] => []
  | .case test body :: rest =>
      .case (ofExpr test) (ofStatements body) :: ofSwitchCases rest
  | .default body :: rest => .default (ofStatements body) :: ofSwitchCases rest

def ofCatchClause : JSCatchClause → MiniCatchClause
  | ⟨param, guard, body⟩ =>
      ⟨ofPattern param, none, (match guard with | none => none | some g => some (ofExpr g)),
        ofStatements body⟩

def ofCatchClauses : List JSCatchClause → List MiniCatchClause
  | [] => []
  | c :: rest => ofCatchClause c :: ofCatchClauses rest

def ofTryTail : JSTryTail → MiniTryTail
  | .catches cs fin =>
      .catches ⟨ofCatchClause cs.hd, ofCatchClauses cs.tl⟩
        (match fin with | .none => .none | .some body => .some (ofStatements body))
  | .finallyOnly body => .finallyOnly (ofStatements body)

def ofStatement : JSStatement → MiniStatement
  | .block body => .block (ofStatements body)
  | .break_ l => .break_ l
  | .continue_ l => .continue_ l
  | .classDecl decorators name heritage body =>
      .classDecl (ofExprs decorators) false name []
        (match heritage with | none => none | some h => some ⟨ofExpr h, []⟩) []
        (ofClassElements body)
  | .decl kind decls => .decl kind ⟨ofDeclarator decls.hd, ofDeclarators decls.tl⟩
  | .using_ isAwait decls =>
      .using_ isAwait ⟨ofDeclarator decls.hd, ofDeclarators decls.tl⟩
  | .debugger => .debugger
  | .doWhile body cond => .doWhile (ofStatement body) (ofExpr cond)
  | .for_ init cond step body =>
      .for_ (ofForInit init) (match cond with | none => none | some c => some (ofExpr c))
        (match step with | none => none | some s => some (ofExpr s)) (ofStatement body)
  | .forIn head obj body => .forIn (ofForHead head) (ofExpr obj) (ofStatement body)
  | .forOf isAwait head obj body =>
      .forOf isAwait (ofForHead head) (ofExpr obj) (ofStatement body)
  | .funcDecl isAsync isGen name params body =>
      .funcDecl isAsync isGen name [] (ofParams params) none (some (ofStatements body))
  | .if_ cond thenS elseS =>
      .if_ (ofExpr cond) (ofStatement thenS)
        (match elseS with | none => none | some e => some (ofStatement e))
  | .labelled l s => .labelled l (ofStatement s)
  | .empty => .empty
  | .expr e => .expr (ofExpr e)
  | .return_ none => .return_ none
  | .return_ (some e) => .return_ (some (ofExpr e))
  | .switch disc cases => .switch (ofExpr disc) (ofSwitchCases cases)
  | .throw e => .throw (ofExpr e)
  | .try_ body tail => .try_ (ofStatements body) (ofTryTail tail)
  | .while_ cond body => .while_ (ofExpr cond) (ofStatement body)
  | .with_ obj body => .with_ (ofExpr obj) (ofStatement body)

def ofStatements : List JSStatement → List MiniStatement
  | [] => []
  | s :: rest => ofStatement s :: ofStatements rest

def ofExportDeclaration : JSExportDeclaration → MiniExportDeclaration
  | .fromClause specs mod attrs => .fromClause false (specs.map ofSpecifier) mod attrs
  | .locals specs => .locals false (specs.map ofSpecifier)
  | .all alias_ mod attrs => .all false alias_ mod attrs
  | .defaultExpr e => .defaultExpr (ofExpr e)
  | .decl s => .decl (ofStatement s)

def ofModuleItem : JSModuleItem → MiniModuleItem
  | .stmt s => .stmt (ofStatement s)
  | .importDecl d => .importDecl (ofImportDeclaration d)
  | .exportDecl d => .exportDecl (ofExportDeclaration d)

def ofImportDeclaration : JSImportDeclaration → MiniImportDeclaration
  | .bare mod attrs => .bare mod attrs
  | .clause c =>
      .clause (MiniImportClause.mk! c.default_ c.namespace_
        (match c.named with | none => none | some specs => some (specs.map ofSpecifier))
        c.mod c.attrs false)

def ofModuleItems : List JSModuleItem → List MiniModuleItem
  | [] => []
  | i :: rest => ofModuleItem i :: ofModuleItems rest

end

/-- A whole program. -/
def ofProgram (p : JSProgram) : MiniProgram := ⟨ofModuleItems p.items⟩

end Language.TypeScript.MiniTsAST.OfJS
