/-
An opinionated printer for `MiniAST`.

Unlike `RequestProject.JavaScript.Printer`, which reproduces the source text
recorded in the annotations of the parsed AST, this printer ignores how the
program was written and lays it out in one canonical style, the one
`prettier` uses by default:

* two spaces of indentation, no tabs;
* one statement per line, always terminated by a semicolon;
* double quoted strings (unless single quotes need less escaping);
* a space around binary operators, after a comma, and inside the braces of
  an object literal;
* `(a) => a + 1`, `if (x) { ... } else { ... }`, `} catch (e) {`;
* a construct is printed on one line if it fits into 80 columns and is
  broken over several lines, with a trailing comma, if it does not;
* parentheses only where the precedence needs them.
-/
import LanguageJavascriptMini.AST
import LanguageJavascriptMini.Doc

namespace Language.JavaScript.MiniAST

open Language.JavaScript.Doc

namespace Printer

/-- The line width the layout aims at. -/
def defaultWidth : Nat := 80

/-- The number of spaces of one indentation step. -/
def indentWidth : Nat := 2

private def t (s : String) : Doc := .text s

private def parens (d : Doc) : Doc := t "(" ++ d ++ t ")"

/-! ## Operators -/

def binOpText : MiniBinOp → String
  | .and => "&&" | .or => "||"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .eq => "==" | .neq => "!=" | .strictEq => "===" | .strictNeq => "!=="
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .lsh => "<<" | .rsh => ">>" | .ursh => ">>>"
  | .plus => "+" | .minus => "-" | .times => "*" | .divide => "/" | .mod => "%"
  | .inOp => "in" | .instanceOf => "instanceof"

/-- The precedence level of a binary operator; higher binds tighter. -/
def binOpPrec : MiniBinOp → Nat
  | .or => 4
  | .and => 5
  | .bitOr => 6
  | .bitXor => 7
  | .bitAnd => 8
  | .eq | .neq | .strictEq | .strictNeq => 9
  | .lt | .le | .gt | .ge | .inOp | .instanceOf => 10
  | .lsh | .rsh | .ursh => 11
  | .plus | .minus => 12
  | .times | .divide | .mod => 13

def unaryOpText : MiniUnaryOp → String
  | .not => "!" | .tilde => "~" | .plus => "+" | .minus => "-"
  | .typeof => "typeof " | .void => "void " | .delete => "delete "
  | .preIncr => "++" | .preDecr => "--"

def postfixOpText : MiniPostfixOp → String
  | .incr => "++" | .decr => "--"

def assignOpText : MiniAssignOp → String
  | .assign => "="
  | .plus => "+=" | .minus => "-=" | .times => "*=" | .divide => "/=" | .mod => "%="
  | .lsh => "<<=" | .rsh => ">>=" | .ursh => ">>>="
  | .bitAnd => "&=" | .bitXor => "^=" | .bitOr => "|="

def varKindText : MiniVarKind → String
  | .var => "var" | .let_ => "let" | .const => "const"

/-! ## Precedence -/

/-- The precedence of an expression: 1 for the comma operator up to 17 for a
primary expression.  A subexpression is parenthesised when its precedence is
lower than the one its position requires. -/
def exprPrec : MiniExpr → Nat
  | .seq _ _ => 1
  | .assign .. | .arrow .. | .yield _ | .yieldFrom _ | .spread _ => 2
  | .ternary .. => 3
  | .binary _ op _ => binOpPrec op
  | .unary .. | .await _ => 14
  | .postfix .. => 15
  | .call .. | .dot .. | .index .. | .new .. => 16
  | .template (some _) _ _ => 16
  | _ => 17

/-- Can this expression be the callee of a `new` without parentheses?  It
has to be a member expression that does not itself contain a call. -/
def newCalleeOk : MiniExpr → Bool
  | .ident _ | .this => true
  | .dot o _ => newCalleeOk o
  | .index o _ => newCalleeOk o
  | _ => false

/-- Would printing `op` directly in front of `e` run the two operators
together, as `-` in front of `-1` would give `--1`? -/
def unaryClash (op : MiniUnaryOp) (e : MiniExpr) : Bool :=
  match e with
  | .unary op' _ =>
      let plusLike (o : MiniUnaryOp) := o == .plus || o == .preIncr
      let minusLike (o : MiniUnaryOp) := o == .minus || o == .preDecr
      (plusLike op && plusLike op') || (minusLike op && minusLike op')
  | _ => false

/-- Does this expression, printed as a statement, have to be parenthesised?
An expression statement may not start with `{`, `function`, `class` or
`let [`, since it would then be read as a block or a declaration. -/
partial def needsStatementParens : MiniExpr → Bool
  | .object _ => true
  | .func .. => true
  | .classExpr .. => true
  -- the callee of a call is parenthesised already when it is a function
  | .call (.func ..) _ => false
  | .call f _ => needsStatementParens f
  | .index (.ident n) _ => n.val == "let"
  | .dot o _ | .index o _ | .postfix o _ => needsStatementParens o
  | .binary l _ _ | .seq l _ | .assign l _ _ => needsStatementParens l
  | .ternary c _ _ => needsStatementParens c
  | .template (some tag) _ _ => needsStatementParens tag
  | _ => false

/-! ## Layout helpers -/

/-- A bracketed, comma separated list: on one line if it fits, otherwise one
element per line.  `spaced` puts a space inside the brackets in the flat
layout (as for object literals), `trailingComma` adds a comma after the last
element in the broken layout. -/
def sepList (opener closer : String) (spaced : Bool) (trailingComma : Bool)
    (items : List Doc) : Doc :=
  if items.isEmpty then t (opener ++ closer)
  else
    let br : Doc := if spaced then .line else .softline
    let trailer : Doc := if trailingComma then .ifBreak (t ",") .nil else .nil
    .group (t opener ++ .nest indentWidth (br ++ Doc.joinWith (t "," ++ .line) items ++ trailer)
      ++ br ++ t closer)

/-! ## The printer -/

mutual

/-- An expression in a position that requires precedence `minPrec`. -/
partial def exprDoc (minPrec : Nat) (e : MiniExpr) : Doc :=
  let d := exprCore e
  if exprPrec e < minPrec then parens d else d

/-- An expression, without the parentheses its context may require. -/
partial def exprCore : MiniExpr → Doc
  | .ident n => t n.val
  | .number r => t r.val
  | .string v => t (encodeStringLiteral v)
  | .regex r => t r.val
  | .null => t "null"
  | .true_ => t "true"
  | .false_ => t "false"
  | .this => t "this"
  | .array els => arrayDoc els
  | .object props => sepList "{" "}" true true (props.map propertyDoc)
  | .assign l op r => exprDoc 16 l ++ t (" " ++ assignOpText op ++ " ") ++ exprDoc 2 r
  | .await e => t "await " ++ exprDoc 14 e
  | .call f args => calleeDoc f ++ argsDoc args
  | .dot o n => memberObjectDoc o ++ t ("." ++ n.val)
  | .index o i => memberObjectDoc o ++ t "[" ++ exprDoc 1 i ++ t "]"
  | .classExpr name heritage body => classDoc name heritage body
  | .seq l r => exprDoc 1 l ++ t ", " ++ exprDoc 2 r
  | .binary l op r =>
      let p := binOpPrec op
      .group (exprDoc p l ++ t (" " ++ binOpText op)
        ++ .nest indentWidth (.line ++ exprDoc (p + 1) r))
  | .postfix e op => exprDoc 16 e ++ t (postfixOpText op)
  | .ternary c a b =>
      .group (exprDoc 4 c ++ .nest indentWidth
        (.line ++ t "? " ++ exprDoc 2 a ++ .line ++ t ": " ++ exprDoc 2 b))
  | .arrow params body => paramsDoc params ++ t " => " ++ arrowBodyDoc body
  | .func isAsync isGen name params body => functionDoc isAsync isGen name params body
  | .new callee args =>
      t "new " ++ (if newCalleeOk callee then exprCore callee else parens (exprCore callee))
        ++ argsDoc args
  | .spread e => t "..." ++ exprDoc 2 e
  | .template tag head parts =>
      let tagDoc := match tag with
        | none => Doc.nil
        | some tag => exprDoc 16 tag
      tagDoc ++ t "`" ++ t head
        ++ Doc.concat (parts.map fun p => t "${" ++ exprDoc 1 p.expr ++ t "}" ++ t p.suffix)
        ++ t "`"
  | .unary op e =>
      t (unaryOpText op)
        ++ (if unaryClash op e then parens (exprCore e) else exprDoc 14 e)
  | .yield none => t "yield"
  | .yield (some e) => t "yield " ++ exprDoc 2 e
  | .yieldFrom e => t "yield* " ++ exprDoc 2 e

/-- The object of a `.` or `[]` access. -/
partial def memberObjectDoc : MiniExpr → Doc
  | .number r => parens (t r.val)
  | e => exprDoc 16 e

/-- The callee of a call; a function expression is parenthesised, as
`prettier` does for an immediately invoked function. -/
partial def calleeDoc : MiniExpr → Doc
  | .func isAsync isGen name params body =>
      parens (functionDoc isAsync isGen name params body)
  | e => memberObjectDoc e

partial def argsDoc (args : List MiniExpr) : Doc :=
  sepList "(" ")" false true (args.map (exprDoc 2))

/-- A parameter list.  No trailing comma is added after a rest parameter,
where it would be a syntax error. -/
partial def paramsDoc (params : List MiniExpr) : Doc :=
  let restLast := match params.getLast? with
    | some (.spread _) => true
    | _ => false
  sepList "(" ")" false (!restLast) (params.map (exprDoc 2))

partial def arrayDoc (els : List MiniArrayElement) : Doc :=
  if els.isEmpty then t "[]"
  else
    let lastIsHole := match els.getLast? with
      | some .hole => true
      | _ => false
    let items := els.map fun
      | .elem e => exprDoc 2 e
      | .hole => Doc.nil
    -- an elision at the end needs its comma in both layouts
    let trailer : Doc := if lastIsHole then t "," else .ifBreak (t ",") .nil
    .group (t "[" ++ .nest indentWidth
      (.softline ++ Doc.joinWith (t "," ++ .line) items ++ trailer) ++ .softline ++ t "]")

partial def propertyNameDoc : MiniPropertyName → Doc
  | .ident n => t n.val
  | .string v => t (encodeStringLiteral v)
  | .number r => t r.val
  | .computed e => t "[" ++ exprDoc 2 e ++ t "]"

partial def propertyDoc : MiniProperty → Doc
  | .keyValue k v => propertyNameDoc k ++ t ": " ++ exprDoc 2 v
  | .shorthand n => t n.val
  | .method kind key params body => methodDoc kind key params body

partial def methodDoc (kind : MiniMethodKind) (key : MiniPropertyName)
    (params : List MiniExpr) (body : List MiniStatement) : Doc :=
  let prefix_ := match kind with
    | .normal => ""
    | .generator => "*"
    | .get => "get "
    | .set => "set "
  t prefix_ ++ propertyNameDoc key ++ paramsDoc params ++ t " " ++ blockDoc body

partial def classElementDoc (el : MiniClassElement) : Doc :=
  (if el.isStatic then t "static " else Doc.nil)
    ++ methodDoc el.kind el.key el.params el.body

partial def classBodyDoc (body : List MiniClassElement) : Doc :=
  if body.isEmpty then t "{}"
  else
    t "{" ++ .nest indentWidth (.hardline ++ Doc.joinWith .hardline (body.map classElementDoc))
      ++ .hardline ++ t "}"

partial def classDoc (name : Option NEString) (heritage : Option MiniExpr)
    (body : List MiniClassElement) : Doc :=
  t "class"
    ++ (match name with | none => Doc.nil | some n => t (" " ++ n.val))
    ++ (match heritage with | none => Doc.nil | some e => t " extends " ++ exprDoc 16 e)
    ++ t " " ++ classBodyDoc body

partial def functionDoc (isAsync isGen : Bool) (name : Option NEString)
    (params : List MiniExpr) (body : List MiniStatement) : Doc :=
  t (if isAsync then "async function" else "function")
    ++ t (if isGen then "*" else "")
    ++ (match name with | none => t " " | some n => t (" " ++ n.val))
    ++ paramsDoc params ++ t " " ++ blockDoc body

partial def arrowBodyDoc : MiniArrowBody → Doc
  | .block body => blockDoc body
  | .expr (.object props) => parens (sepList "{" "}" true true (props.map propertyDoc))
  | .expr e => exprDoc 2 e

/-- A brace enclosed statement list. -/
partial def blockDoc (body : List MiniStatement) : Doc :=
  if body.isEmpty then t "{}"
  else
    t "{" ++ .nest indentWidth (.hardline ++ statementsDoc body) ++ .hardline ++ t "}"

partial def statementsDoc (body : List MiniStatement) : Doc :=
  Doc.joinWith .hardline (body.map statementDoc)

/-- The body of an `if`, `for`, `while` or `with`, attached to its head.  A
body that is not a block stays on the same line if it fits, and is indented
on the next line if it does not. -/
partial def attachedBodyDoc : MiniStatement → Doc
  | .block body => t " " ++ blockDoc body
  | .empty => t ";"
  | s => .group (.nest indentWidth (.line ++ statementDoc s))

partial def declaratorDoc (d : MiniDeclarator) : Doc :=
  exprDoc 2 d.lhs ++ (match d.init with
    | none => Doc.nil
    | some e => t " = " ++ exprDoc 2 e)

partial def declarationDoc (kind : MiniVarKind) (decls : NEList MiniDeclarator) : Doc :=
  t (varKindText kind ++ " ")
    ++ .group (Doc.joinWith (t "," ++ .line) (decls.toList.map declaratorDoc))

partial def forInitDoc : MiniForInit → Doc
  | .none => Doc.nil
  | .expr e => exprDoc 1 e
  | .decl kind decls =>
      t (varKindText kind ++ " ")
        ++ Doc.joinWith (t ", ") (decls.toList.map declaratorDoc)

partial def forHeadDoc : MiniForHead → Doc
  | .pattern e => exprDoc 2 e
  | .decl kind lhs => t (varKindText kind ++ " ") ++ exprDoc 2 lhs

partial def switchCaseDoc : MiniSwitchCase → Doc
  | .case test body => t "case " ++ exprDoc 2 test ++ t ":" ++ caseBodyDoc body
  | .default body => t "default:" ++ caseBodyDoc body

partial def caseBodyDoc (body : List MiniStatement) : Doc :=
  match body with
  | [] => Doc.nil
  | [.block b] => t " " ++ blockDoc b
  | body => .nest indentWidth (.hardline ++ statementsDoc body)

partial def catchDoc (c : MiniCatchClause) : Doc :=
  t " catch (" ++ exprDoc 1 c.param
    ++ (match c.guard with | none => Doc.nil | some g => t " if " ++ exprDoc 1 g)
    ++ t ") " ++ blockDoc c.body

partial def tryTailDoc : MiniTryTail → Doc
  | .finallyOnly body => t " finally " ++ blockDoc body
  | .catches cs fin =>
      Doc.concat (cs.toList.map catchDoc)
        ++ (match fin with
            | .none => Doc.nil
            | .some body => t " finally " ++ blockDoc body)

partial def statementDoc : MiniStatement → Doc
  | .block body => blockDoc body
  | .break_ none => t "break;"
  | .break_ (some l) => t ("break " ++ l.val ++ ";")
  | .continue_ none => t "continue;"
  | .continue_ (some l) => t ("continue " ++ l.val ++ ";")
  | .classDecl name heritage body => classDoc (some name) heritage body
  | .decl kind decls => declarationDoc kind decls ++ t ";"
  | .doWhile body cond =>
      t "do" ++ attachedBodyDoc body
        ++ (match body with | .block _ => t " " | _ => .hardline)
        ++ t "while (" ++ exprDoc 1 cond ++ t ");"
  | .for_ init cond step body =>
      t "for (" ++ forInitDoc init ++ t ";"
        ++ (match cond with | none => Doc.nil | some c => t " " ++ exprDoc 1 c) ++ t ";"
        ++ (match step with | none => Doc.nil | some s => t " " ++ exprDoc 1 s) ++ t ")"
        ++ attachedBodyDoc body
  | .forIn head obj body =>
      t "for (" ++ forHeadDoc head ++ t " in " ++ exprDoc 2 obj ++ t ")"
        ++ attachedBodyDoc body
  | .forOf head obj body =>
      t "for (" ++ forHeadDoc head ++ t " of " ++ exprDoc 2 obj ++ t ")"
        ++ attachedBodyDoc body
  | .funcDecl isAsync isGen name params body =>
      functionDoc isAsync isGen (some name) params body
  | .if_ cond thenS elseS =>
      let head := t "if (" ++ exprDoc 1 cond ++ t ")" ++ attachedBodyDoc thenS
      match elseS with
      | none => head
      | some e =>
          let kw := match thenS with
            | .block _ => t " else"
            | _ => .hardline ++ t "else"
          let tail := match e with
            | .if_ .. => t " " ++ statementDoc e
            | _ => attachedBodyDoc e
          head ++ kw ++ tail
  | .labelled l s => t (l.val ++ ": ") ++ statementDoc s
  | .empty => t ";"
  | .expr e =>
      let d := exprDoc 1 e
      if needsStatementParens e then parens d ++ t ";" else d ++ t ";"
  | .return_ none => t "return;"
  | .return_ (some e) => t "return " ++ exprDoc 1 e ++ t ";"
  | .switch disc cases =>
      t "switch (" ++ exprDoc 1 disc ++ t ") "
        ++ (if cases.isEmpty then t "{}"
            else t "{" ++ .nest indentWidth
              (.hardline ++ Doc.joinWith .hardline (cases.map switchCaseDoc))
              ++ .hardline ++ t "}")
  | .throw e => t "throw " ++ exprDoc 1 e ++ t ";"
  | .try_ body tail => t "try " ++ blockDoc body ++ tryTailDoc tail
  | .while_ cond body => t "while (" ++ exprDoc 1 cond ++ t ")" ++ attachedBodyDoc body
  | .with_ obj body => t "with (" ++ exprDoc 1 obj ++ t ")" ++ attachedBodyDoc body

end

/-! ## Modules -/

def specifierDoc (s : MiniSpecifier) : Doc :=
  t s.name.val ++ (match s.alias_ with | none => Doc.nil | some a => t (" as " ++ a.val))

def specifiersDoc (specs : List MiniSpecifier) : Doc :=
  sepList "{" "}" true true (specs.map specifierDoc)

def importDoc : MiniImportDeclaration → Doc
  | .bare mod => t ("import " ++ encodeStringLiteral mod.val ++ ";")
  | .clause c =>
      let parts : List Doc :=
        (match c.default_ with | none => [] | some d => [t d.val])
        ++ (match c.namespace_ with | none => [] | some n => [t ("* as " ++ n.val)])
        ++ (match c.named with | none => [] | some specs => [specifiersDoc specs])
      t "import " ++ Doc.joinWith (t ", ") parts
        ++ t (" from " ++ encodeStringLiteral c.mod.val ++ ";")

def exportDoc : MiniExportDeclaration → Doc
  | .fromClause specs mod =>
      t "export " ++ specifiersDoc specs ++ t (" from " ++ encodeStringLiteral mod.val ++ ";")
  | .locals specs => t "export " ++ specifiersDoc specs ++ t ";"
  | .decl s => t "export " ++ statementDoc s

def moduleItemDoc : MiniModuleItem → Doc
  | .stmt s => statementDoc s
  | .importDecl d => importDoc d
  | .exportDecl d => exportDoc d

def programDoc (p : MiniProgram) : Doc :=
  Doc.joinWith .hardline (p.items.map moduleItemDoc)

end Printer

/-! ## Entry points -/

/-- Print a program in the canonical style, at a given line width. -/
def printProgramWidth (width : Nat) (p : MiniProgram) : String :=
  if p.items.isEmpty then ""
  else Doc.render width (Printer.programDoc p) ++ "\n"

/-- Print a program in the canonical style: two space indentation, double
quotes, semicolons, and lines of at most 80 columns. -/
def printProgram (p : MiniProgram) : String :=
  printProgramWidth Printer.defaultWidth p

/-- Print a single statement. -/
def printStatement (s : MiniStatement) : String :=
  Doc.render Printer.defaultWidth (Printer.statementDoc s)

/-- Print a single expression. -/
def printExpr (e : MiniExpr) : String :=
  Doc.render Printer.defaultWidth (Printer.exprDoc 1 e)

end Language.JavaScript.MiniAST
