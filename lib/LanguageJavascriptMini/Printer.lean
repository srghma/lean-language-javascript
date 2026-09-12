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

def binOpText : BinOp → String
  | .and => "&&" | .or => "||" | .coalesce => "??"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .eq => "==" | .neq => "!=" | .strictEq => "===" | .strictNeq => "!=="
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .lsh => "<<" | .rsh => ">>" | .ursh => ">>>"
  | .plus => "+" | .minus => "-" | .times => "*" | .divide => "/" | .mod => "%"
  | .inOp => "in" | .instanceOf => "instanceof"

/-- The precedence level of a binary operator; higher binds tighter.
`??` sits at the level of `||`; JavaScript refuses to mix the two without
parentheses, which `logicalMix` puts back. -/
def binOpPrec : BinOp → Nat
  | .or | .coalesce => 4
  | .and => 5
  | .bitOr => 6
  | .bitXor => 7
  | .bitAnd => 8
  | .eq | .neq | .strictEq | .strictNeq => 9
  | .lt | .le | .gt | .ge | .inOp | .instanceOf => 10
  | .lsh | .rsh | .ursh => 11
  | .plus | .minus => 12
  | .times | .divide | .mod => 13

def unaryOpText : UnaryOp → String
  | .not => "!" | .tilde => "~" | .plus => "+" | .minus => "-"
  | .typeof => "typeof " | .void => "void " | .delete => "delete "
  | .preIncr => "++" | .preDecr => "--"

def postfixOpText : PostfixOp → String
  | .incr => "++" | .decr => "--"

/-- `??` may not be written next to `&&` or `||` without parentheses, so an
operand which mixes the two is parenthesised even though the precedences
would allow it. -/
def logicalMix (op : BinOp) (child : MiniExpr) : Bool :=
  match child with
  | .binary _ childOp _ =>
      (op == .coalesce && (childOp == .and || childOp == .or))
        || ((op == .and || op == .or) && childOp == .coalesce)
  | _ => false

def assignOpText : AssignOp → String
  | .assign => "="
  | .logicalAnd => "&&=" | .logicalOr => "||=" | .coalesce => "??="
  | .plus => "+=" | .minus => "-=" | .times => "*=" | .divide => "/=" | .mod => "%="
  | .lsh => "<<=" | .rsh => ">>=" | .ursh => ">>>="
  | .bitAnd => "&=" | .bitXor => "^=" | .bitOr => "|="

def varKindText : VarKind → String
  | .var => "var" | .let_ => "let" | .const => "const"

/-! ## Precedence -/

/-- The precedence of an expression: 1 for the comma operator up to 17 for a
primary expression.  A subexpression is parenthesised when its precedence is
lower than the one its position requires. -/
def exprPrec : MiniExpr → Nat
  | .seq _ _ => 1
  | .assign .. | .assignPattern .. | .arrow .. | .yield _ | .yieldFrom _ | .spread _ => 2
  | .ternary .. => 3
  | .binary _ op _ => binOpPrec op
  | .unary .. | .await _ => 14
  | .postfix .. => 15
  | .call .. | .dot .. | .privateDot .. | .index .. | .new .. | .chain .. | .importCall .. => 16
  | .superDot .. | .superIndex .. | .superCall .. => 16
  | .template (some _) _ _ => 16
  | _ => 17

/-- Can this expression be the callee of a `new` without parentheses?  It
has to be a member expression that does not itself contain a call. -/
def newCalleeOk : MiniExpr → Bool
  | .ident _ | .this => true
  | .dot o _ => newCalleeOk o
  | .privateDot o _ => newCalleeOk o
  | .index o _ => newCalleeOk o
  | _ => false

/-- Would printing `op` directly in front of `e` run the two operators
together, as `-` in front of `-1` would give `--1`? -/
def unaryClash (op : UnaryOp) (e : MiniExpr) : Bool :=
  match e with
  | .unary op' _ =>
      let plusLike (o : UnaryOp) := o == .plus || o == .preIncr
      let minusLike (o : UnaryOp) := o == .minus || o == .preDecr
      (plusLike op && plusLike op') || (minusLike op && minusLike op')
  | _ => false

/-- Does this expression, printed as a statement, have to be parenthesised?
An expression statement may not start with `{`, `function`, `class` or
`let [`, since it would then be read as a block or a declaration. -/
def needsStatementParens : MiniExpr → Bool
  | .object _ => true
  | .func .. => true
  | .classExpr .. => true
  -- the callee of a call is parenthesised already when it is a function
  | .call (.func ..) _ => false
  | .call f _ => needsStatementParens f
  | .index (.ident n) _ => n.val == "let"
  | .dot o _ | .privateDot o _ | .index o _ | .postfix o _ | .chain o _ =>
      needsStatementParens o
  -- `{ a } = o` at the start of a statement would be read as a block
  | .assignPattern (.object ..) _ => true
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

/-! ## The printer

The printer is *structurally* recursive: each function walks its own
argument and calls the others on strict subterms of it, so the kernel can
unfold it and what a given tree prints as can be reasoned about.  Two
shapes would break that and are avoided here: a function which looks at an
argument another one has already printed, which is written as a helper
taking the printed document (`exprDocWith`, `memberObjectWith`,
`calleeWith`, `attachedBodyWith`, `caseBodyWith`, `blockDocOf`, …), and a
`List.map` with a recursive function, which is written out as a function of
the list (`argDocs`, `paramDocs`, `statementDocs`, …).  The names the
printer used before are kept, as wrappers, after the block. -/

/-- Parenthesise `d` when `cond` holds. -/
def parenIf (cond : Bool) (d : Doc) : Doc := if cond then parens d else d

/-- An expression in a position that requires precedence `minPrec`, given
the document the expression itself prints as. -/
def exprDocWith (minPrec : Nat) (e : MiniExpr) (d : Doc) : Doc :=
  parenIf (exprPrec e < minPrec) d

/-- The object of a `.` or `[]` access, given the document it prints as. -/
def memberObjectWith (e : MiniExpr) (d : Doc) : Doc :=
  match e with
  | .number n => parens (t n.render)
  -- a chain written as the object of a plain access was parenthesised in the
  -- source, and has to stay so: `(a?.b).c` is not `a?.b.c`
  | .chain _ _ => parens d
  | _ => exprDocWith 16 e d

/-- The callee of a call, given the document it prints as; a function
expression is parenthesised, as `prettier` does for an immediately invoked
function. -/
def calleeWith (e : MiniExpr) (d : Doc) : Doc :=
  match e with
  | .func .. => parens d
  | _ => memberObjectWith e d

/-- A parameter list, given the documents of the parameters.  No trailing
comma is added after a rest parameter, where it would be a syntax error. -/
def paramsDocOf (params : List MiniParam) (items : List Doc) : Doc :=
  let restLast := match params.getLast? with
    | some (.rest _) => true
    | _ => false
  sepList "(" ")" false (!restLast) items

/-- An array literal, given the documents of its elements. -/
def arrayDocOf (els : List MiniArrayElement) (items : List Doc) : Doc :=
  if els.isEmpty then t "[]"
  else
    let lastIsHole := match els.getLast? with
      | some .hole => true
      | _ => false
    -- an elision at the end needs its comma in both layouts
    let trailer : Doc := if lastIsHole then t "," else .ifBreak (t ",") .nil
    .group (t "[" ++ .nest indentWidth
      (.softline ++ Doc.joinWith (t "," ++ .line) items ++ trailer) ++ .softline ++ t "]")

/-- An array pattern, given the documents of its elements.  A trailing
comma may not follow a `...rest`, and an elision at the end needs its comma
in both layouts. -/
def arrayPatternDocOf (els : List MiniArrayPatternElem) (items : List Doc) : Doc :=
  if els.isEmpty then t "[]"
  else
    let trailer : Doc := match els.getLast? with
      | some .hole => t ","
      | some (.rest _) => Doc.nil
      | _ => .ifBreak (t ",") .nil
    .group (t "[" ++ .nest indentWidth
      (.softline ++ Doc.joinWith (t "," ++ .line) items ++ trailer) ++ .softline ++ t "]")

/-- An object pattern, given the documents of its properties and of its
rest element; a trailing comma may not follow the rest element. -/
def objectPatternDocOf (rest : Option MiniPattern) (items : List Doc) : Doc :=
  sepList "{" "}" true rest.isNone items

/-- May the property `key: value` of an object pattern be written in the
short form, as `{ a }` or `{ a = 1 }`? -/
def patternShorthand (key : MiniPropertyName) (value : MiniPattern) : Bool :=
  match key, value with
  | .ident k, .ident v => k == v
  | .ident k, .withDefault (.ident v) _ => k == v
  | _, _ => false

/-- The decorators in front of a class or of a class member, given their
documents. -/
def decoratorsPrefix (items : List Doc) : Doc :=
  Doc.joinWith Doc.nil (items.map (fun d => d ++ t " "))

/-- A brace enclosed statement list, given the document of the list. -/
def blockDocOf (body : List MiniStatement) (inner : Doc) : Doc :=
  if body.isEmpty then t "{}"
  else t "{" ++ .nest indentWidth (.hardline ++ inner) ++ .hardline ++ t "}"

/-- A class body, given the documents of its members. -/
def classBodyOf (body : List MiniClassElement) (items : List Doc) : Doc :=
  if body.isEmpty then t "{}"
  else
    t "{" ++ .nest indentWidth (.hardline ++ Doc.joinWith .hardline items)
      ++ .hardline ++ t "}"

/-- A class, given the documents of its decorators, of its heritage clause
(`" extends …"`, or nothing) and of its members. -/
def classDocOf (decorators : List Doc) (name : Option NEString) (heritage : Doc)
    (body : List MiniClassElement) (items : List Doc) : Doc :=
  decoratorsPrefix decorators
    ++ t "class"
    ++ (match name with | none => Doc.nil | some n => t (" " ++ n.val))
    ++ heritage ++ t " " ++ classBodyOf body items

/-- A function, given the documents of its parameters and of its body. -/
def functionDocOf (isAsync isGen : Bool) (name : Option NEString)
    (params : List MiniParam) (paramItems : List Doc)
    (body : List MiniStatement) (bodyInner : Doc) : Doc :=
  t (if isAsync then "async function" else "function")
    ++ t (if isGen then "*" else "")
    ++ (match name with | none => t " " | some n => t (" " ++ n.val))
    ++ paramsDocOf params paramItems ++ t " " ++ blockDocOf body bodyInner

/-- A method, given the documents of its name, its parameters and its
body. -/
def methodDocOf (kind : MethodKind) (key : Doc)
    (params : List MiniParam) (paramItems : List Doc)
    (body : List MiniStatement) (bodyInner : Doc) : Doc :=
  let prefix_ := match kind with
    | .normal => ""
    | .generator => "*"
    | .get => "get "
    | .set => "set "
  t prefix_ ++ key ++ paramsDocOf params paramItems ++ t " " ++ blockDocOf body bodyInner

/-- The body of an `if`, `for`, `while` or `with`, attached to its head,
given the document the statement prints as.  A body that is not a block
stays on the same line if it fits, and is indented on the next line if it
does not. -/
def attachedBodyWith (s : MiniStatement) (d : Doc) : Doc :=
  match s with
  | .block _ => t " " ++ d
  | .empty => t ";"
  | _ => .group (.nest indentWidth (.line ++ d))

/-- The statements of one `case` of a `switch`, given the document their
list prints as. -/
def caseBodyWith (body : List MiniStatement) (inner : Doc) : Doc :=
  match body with
  | [] => Doc.nil
  | [.block _] => t " " ++ inner
  | _ => .nest indentWidth (.hardline ++ inner)

mutual

/-- An expression, without the parentheses its context may require. -/
def exprCore : MiniExpr → Doc
  | .ident n => t n.val
  | .number n => t n.render
  | .string v => t (encodeStringLiteral v)
  | .regex r => t r.render
  | .null => t "null"
  | .true_ => t "true"
  | .false_ => t "false"
  | .this => t "this"
  | .superDot n => t ("super." ++ n.val)
  | .superIndex i => t "super[" ++ exprDocWith 1 i (exprCore i) ++ t "]"
  | .superCall args => t "super" ++ sepList "(" ")" false true (argDocs args)
  | .newTarget => t "new.target"
  | .array els => arrayDocOf els (arrayItemDocs els)
  | .object props => sepList "{" "}" true true (propertyDocs props)
  | .assign l op r =>
      exprDocWith 16 l (exprCore l) ++ t (" " ++ assignOpText op ++ " ")
        ++ exprDocWith 2 r (exprCore r)
  | .assignPattern l r =>
      patternDoc l ++ t " = " ++ exprDocWith 2 r (exprCore r)
  | .await e => t "await " ++ exprDocWith 14 e (exprCore e)
  | .call f args =>
      calleeWith f (exprCore f) ++ sepList "(" ")" false true (argDocs args)
  | .dot o n => memberObjectWith o (exprCore o) ++ t ("." ++ n.val)
  | .privateDot o n => memberObjectWith o (exprCore o) ++ t (".#" ++ n.val)
  | .privateName n => t ("#" ++ n.val)
  | .index o i =>
      memberObjectWith o (exprCore o) ++ t "[" ++ exprDocWith 1 i (exprCore i) ++ t "]"
  | .chain base ⟨hd, tl⟩ =>
      memberObjectWith base (exprCore base) ++ chainLinksAux (chainLinkDoc hd) tl
  | .importMeta => t "import.meta"
  | .importCall spec none =>
      t "import(" ++ exprDocWith 2 spec (exprCore spec) ++ t ")"
  | .importCall spec (some o) =>
      t "import(" ++ exprDocWith 2 spec (exprCore spec) ++ t ", "
        ++ exprDocWith 2 o (exprCore o) ++ t ")"
  | .classExpr decorators name heritage body =>
      classDocOf (decoratorDocs decorators) name
        (match heritage with
          | none => Doc.nil
          | some e => t " extends " ++ exprDocWith 16 e (exprCore e))
        body (classElemDocs body)
  | .seq l r => exprDocWith 1 l (exprCore l) ++ t ", " ++ exprDocWith 2 r (exprCore r)
  | .binary l op r =>
      let p := binOpPrec op
      .group (parenIf (logicalMix op l) (exprDocWith p l (exprCore l)) ++ t (" " ++ binOpText op)
        ++ .nest indentWidth
            (.line ++ parenIf (logicalMix op r) (exprDocWith (p + 1) r (exprCore r))))
  | .postfix e op => exprDocWith 16 e (exprCore e) ++ t (postfixOpText op)
  | .ternary c a b =>
      .group (exprDocWith 4 c (exprCore c) ++ .nest indentWidth
        (.line ++ t "? " ++ exprDocWith 2 a (exprCore a)
          ++ .line ++ t ": " ++ exprDocWith 2 b (exprCore b)))
  | .arrow params body =>
      paramsDocOf params (paramDocs params) ++ t " => " ++ arrowBodyDoc body
  | .func isAsync isGen name params body =>
      functionDocOf isAsync isGen name params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs body))
  | .new callee args =>
      t "new " ++ (if newCalleeOk callee then exprCore callee else parens (exprCore callee))
        ++ sepList "(" ")" false true (argDocs args)
  | .spread e => t "..." ++ exprDocWith 2 e (exprCore e)
  | .template tag head parts =>
      (match tag with
        | none => Doc.nil
        | some tg => exprDocWith 16 tg (exprCore tg))
        ++ t "`" ++ t head ++ templatePartsAux .nil parts ++ t "`"
  | .unary op e =>
      t (unaryOpText op)
        ++ (if unaryClash op e then parens (exprCore e) else exprDocWith 14 e (exprCore e))
  | .yield none => t "yield"
  | .yield (some e) => t "yield " ++ exprDocWith 2 e (exprCore e)
  | .yieldFrom e => t "yield* " ++ exprDocWith 2 e (exprCore e)

/-- The arguments of a call or of a `new`. -/
def argDocs : List MiniExpr → List Doc
  | [] => []
  | a :: rest => exprDocWith 2 a (exprCore a) :: argDocs rest

/-- One link of an optional chain. -/
def chainLinkDoc : MiniChainLink → Doc
  | .dot optional n => t ((if optional then "?." else ".") ++ n.val)
  | .privateDot optional n => t ((if optional then "?.#" else ".#") ++ n.val)
  | .index optional i =>
      t (if optional then "?.[" else "[") ++ exprDocWith 1 i (exprCore i) ++ t "]"
  | .call optional args =>
      t (if optional then "?." else "") ++ sepList "(" ")" false true (argDocs args)

/-- The links of an optional chain, appended to the document of the base. -/
def chainLinksAux (acc : Doc) : List MiniChainLink → Doc
  | [] => acc
  | l :: rest => chainLinksAux (acc ++ chainLinkDoc l) rest

/-- The decorators of a class or of a class member, each written `@expr`. -/
def decoratorDocs : List MiniExpr → List Doc
  | [] => []
  | d :: rest => (t "@" ++ exprDocWith 16 d (exprCore d)) :: decoratorDocs rest

/-- A binding pattern. -/
def patternDoc : MiniPattern → Doc
  | .ident n => t n.val
  | .array els => arrayPatternDocOf els (arrayPatternElemDocs els)
  | .object props none => objectPatternDocOf none (objectPatternPropDocs props)
  | .object props (some r) =>
      objectPatternDocOf (some r)
        (objectPatternPropDocs props ++ [t "..." ++ patternDoc r])
  | .withDefault p v => patternDoc p ++ t " = " ++ exprDocWith 2 v (exprCore v)
  | .target e => exprDocWith 2 e (exprCore e)

def arrayPatternElemDocs : List MiniArrayPatternElem → List Doc
  | [] => []
  | .hole :: rest => Doc.nil :: arrayPatternElemDocs rest
  | .elem p :: rest => patternDoc p :: arrayPatternElemDocs rest
  | .rest p :: rest => (t "..." ++ patternDoc p) :: arrayPatternElemDocs rest

def objectPatternPropDocs : List MiniObjectPatternProp → List Doc
  | [] => []
  | ⟨key, value⟩ :: rest =>
      (if patternShorthand key value then patternDoc value
        else propertyNameDoc key ++ t ": " ++ patternDoc value)
        :: objectPatternPropDocs rest

/-- The elements of an array literal; an elision prints as nothing. -/
def arrayItemDocs : List MiniArrayElement → List Doc
  | [] => []
  | .elem e :: rest => exprDocWith 2 e (exprCore e) :: arrayItemDocs rest
  | .hole :: rest => Doc.nil :: arrayItemDocs rest

/-- The `${…}` substitutions of a template literal, and the text between
them. -/
def templatePartsAux (acc : Doc) : List MiniTemplatePart → Doc
  | [] => acc
  | ⟨e, suffix⟩ :: rest =>
      templatePartsAux
        (acc ++ (t "${" ++ exprDocWith 1 e (exprCore e) ++ t "}" ++ t suffix)) rest

def propertyNameDoc : MiniPropertyName → Doc
  | .ident n => t n.val
  | .private_ n => t ("#" ++ n.val)
  | .string v => t (encodeStringLiteral v)
  | .number n => t n.render
  | .computed e => t "[" ++ exprDocWith 2 e (exprCore e) ++ t "]"

def propertyDoc : MiniProperty → Doc
  | .keyValue k v => propertyNameDoc k ++ t ": " ++ exprDocWith 2 v (exprCore v)
  | .shorthand n => t n.val
  | .spread e => t "..." ++ exprDocWith 2 e (exprCore e)
  | .method kind key params body =>
      methodDocOf kind (propertyNameDoc key) params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs body))

def propertyDocs : List MiniProperty → List Doc
  | [] => []
  | p :: rest => propertyDoc p :: propertyDocs rest

/-- One parameter. -/
def paramDoc : MiniParam → Doc
  | .plain p => patternDoc p
  | .rest p => t "..." ++ patternDoc p

def paramDocs : List MiniParam → List Doc
  | [] => []
  | p :: rest => paramDoc p :: paramDocs rest

def classElemDoc : MiniClassElement → Doc
  | .method decorators isStatic kind key params body =>
      decoratorsPrefix (decoratorDocs decorators)
        ++ (if isStatic then t "static " else Doc.nil)
        ++ methodDocOf kind (propertyNameDoc key) params (paramDocs params) body
            (Doc.joinWith .hardline (statementDocs body))
  | .field decorators isStatic key init =>
      decoratorsPrefix (decoratorDocs decorators)
        ++ (if isStatic then t "static " else Doc.nil)
        ++ propertyNameDoc key
        ++ (match init with
            | none => Doc.nil
            | some e => t " = " ++ exprDocWith 2 e (exprCore e))
        ++ t ";"
  | .staticBlock body =>
      t "static " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body))

def classElemDocs : List MiniClassElement → List Doc
  | [] => []
  | el :: rest => classElemDoc el :: classElemDocs rest

def arrowBodyDoc : MiniArrowBody → Doc
  | .block body => blockDocOf body (Doc.joinWith .hardline (statementDocs body))
  | .expr (.object props) => parens (sepList "{" "}" true true (propertyDocs props))
  | .expr e => exprDocWith 2 e (exprCore e)

def declaratorDoc : MiniDeclarator → Doc
  | ⟨lhs, init⟩ =>
      patternDoc lhs ++ (match init with
        | none => Doc.nil
        | some e => t " = " ++ exprDocWith 2 e (exprCore e))

def declaratorDocs : List MiniDeclarator → List Doc
  | [] => []
  | d :: rest => declaratorDoc d :: declaratorDocs rest

def forInitDoc : MiniForInit → Doc
  | .none => Doc.nil
  | .expr e => exprDocWith 1 e (exprCore e)
  | .decl kind ⟨hd, tl⟩ =>
      t (varKindText kind ++ " ")
        ++ Doc.joinWith (t ", ") (declaratorDoc hd :: declaratorDocs tl)

def forHeadDoc : MiniForHead → Doc
  | .pattern p => patternDoc p
  | .decl kind lhs => t (varKindText kind ++ " ") ++ patternDoc lhs

def switchCaseDoc : MiniSwitchCase → Doc
  | .case test body =>
      t "case " ++ exprDocWith 2 test (exprCore test) ++ t ":"
        ++ caseBodyWith body (Doc.joinWith .hardline (statementDocs body))
  | .default body =>
      t "default:" ++ caseBodyWith body (Doc.joinWith .hardline (statementDocs body))

def switchCaseDocs : List MiniSwitchCase → List Doc
  | [] => []
  | c :: rest => switchCaseDoc c :: switchCaseDocs rest

def catchDoc : MiniCatchClause → Doc
  | ⟨param, guard, body⟩ =>
      t " catch (" ++ patternDoc param
        ++ (match guard with
            | none => Doc.nil
            | some g => t " if " ++ exprDocWith 1 g (exprCore g))
        ++ t ") " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body))

def catchDocsAux (acc : Doc) : List MiniCatchClause → Doc
  | [] => acc
  | c :: rest => catchDocsAux (acc ++ catchDoc c) rest

def tryTailDoc : MiniTryTail → Doc
  | .finallyOnly body =>
      t " finally " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body))
  | .catches ⟨hd, tl⟩ fin =>
      catchDocsAux (Doc.nil ++ catchDoc hd) tl
        ++ (match fin with
            | .none => Doc.nil
            | .some body =>
                t " finally " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body)))

def statementDoc : MiniStatement → Doc
  | .block body => blockDocOf body (Doc.joinWith .hardline (statementDocs body))
  | .break_ none => t "break;"
  | .break_ (some l) => t ("break " ++ l.val ++ ";")
  | .continue_ none => t "continue;"
  | .continue_ (some l) => t ("continue " ++ l.val ++ ";")
  | .classDecl decorators name heritage body =>
      classDocOf (decoratorDocs decorators) (some name)
        (match heritage with
          | none => Doc.nil
          | some e => t " extends " ++ exprDocWith 16 e (exprCore e))
        body (classElemDocs body)
  | .decl kind ⟨hd, tl⟩ =>
      t (varKindText kind ++ " ")
        ++ .group (Doc.joinWith (t "," ++ .line) (declaratorDoc hd :: declaratorDocs tl))
        ++ t ";"
  | .using_ isAwait ⟨hd, tl⟩ =>
      t (if isAwait then "await using " else "using ")
        ++ .group (Doc.joinWith (t "," ++ .line) (declaratorDoc hd :: declaratorDocs tl))
        ++ t ";"
  | .doWhile body cond =>
      t "do" ++ attachedBodyWith body (statementDoc body)
        ++ (match body with | .block _ => t " " | _ => .hardline)
        ++ t "while (" ++ exprDocWith 1 cond (exprCore cond) ++ t ");"
  | .for_ init cond step body =>
      t "for (" ++ forInitDoc init ++ t ";"
        ++ (match cond with
            | none => Doc.nil
            | some c => t " " ++ exprDocWith 1 c (exprCore c)) ++ t ";"
        ++ (match step with
            | none => Doc.nil
            | some s => t " " ++ exprDocWith 1 s (exprCore s)) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)
  | .forIn head obj body =>
      t "for (" ++ forHeadDoc head ++ t " in " ++ exprDocWith 2 obj (exprCore obj) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)
  | .forOf head obj body =>
      t "for (" ++ forHeadDoc head ++ t " of " ++ exprDocWith 2 obj (exprCore obj) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)
  | .funcDecl isAsync isGen name params body =>
      functionDocOf isAsync isGen (some name) params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs body))
  | .if_ cond thenS elseS =>
      let head :=
        t "if (" ++ exprDocWith 1 cond (exprCore cond) ++ t ")"
          ++ attachedBodyWith thenS (statementDoc thenS)
      match elseS with
      | none => head
      | some e =>
          let kw := match thenS with
            | .block _ => t " else"
            | _ => .hardline ++ t "else"
          let tail := match e with
            | .if_ .. => t " " ++ statementDoc e
            | _ => attachedBodyWith e (statementDoc e)
          head ++ kw ++ tail
  | .labelled l s => t (l.val ++ ": ") ++ statementDoc s
  | .empty => t ";"
  | .expr e =>
      let d := exprDocWith 1 e (exprCore e)
      if needsStatementParens e then parens d ++ t ";" else d ++ t ";"
  | .return_ none => t "return;"
  | .return_ (some e) => t "return " ++ exprDocWith 1 e (exprCore e) ++ t ";"
  | .switch disc cases =>
      t "switch (" ++ exprDocWith 1 disc (exprCore disc) ++ t ") "
        ++ (if cases.isEmpty then t "{}"
            else t "{" ++ .nest indentWidth
              (.hardline ++ Doc.joinWith .hardline (switchCaseDocs cases))
              ++ .hardline ++ t "}")
  | .throw e => t "throw " ++ exprDocWith 1 e (exprCore e) ++ t ";"
  | .try_ body tail =>
      t "try " ++ blockDocOf body (Doc.joinWith .hardline (statementDocs body))
        ++ tryTailDoc tail
  | .while_ cond body =>
      t "while (" ++ exprDocWith 1 cond (exprCore cond) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)
  | .with_ obj body =>
      t "with (" ++ exprDocWith 1 obj (exprCore obj) ++ t ")"
        ++ attachedBodyWith body (statementDoc body)

def statementDocs : List MiniStatement → List Doc
  | [] => []
  | s :: rest => statementDoc s :: statementDocs rest

end

/-! ### The printer, as it is called

The functions above take the documents of the subtrees; these are the
ordinary entry points, which compute them. -/

/-- An expression in a position that requires precedence `minPrec`. -/
def exprDoc (minPrec : Nat) (e : MiniExpr) : Doc := exprDocWith minPrec e (exprCore e)

/-- The object of a `.` or `[]` access. -/
def memberObjectDoc (e : MiniExpr) : Doc := memberObjectWith e (exprCore e)

/-- The callee of a call. -/
def calleeDoc (e : MiniExpr) : Doc := calleeWith e (exprCore e)

def argsDoc (args : List MiniExpr) : Doc := sepList "(" ")" false true (argDocs args)

/-- A parameter list. -/
def paramsDoc (params : List MiniParam) : Doc := paramsDocOf params (paramDocs params)

def arrayDoc (els : List MiniArrayElement) : Doc := arrayDocOf els (arrayItemDocs els)

def classBodyDoc (body : List MiniClassElement) : Doc := classBodyOf body (classElemDocs body)

def classElementDoc (el : MiniClassElement) : Doc := classElemDoc el

/-- A binding pattern. -/
def patternDocOf (p : MiniPattern) : Doc := patternDoc p

/-- One decorator, `@expr`. -/
def decoratorDoc (e : MiniExpr) : Doc := t "@" ++ exprDoc 16 e

def classDoc (decorators : List MiniExpr) (name : Option NEString)
    (heritage : Option MiniExpr) (body : List MiniClassElement) : Doc :=
  classDocOf (decoratorDocs decorators) name
    (match heritage with | none => Doc.nil | some e => t " extends " ++ exprDoc 16 e)
    body (classElemDocs body)

def methodDoc (kind : MethodKind) (key : MiniPropertyName)
    (params : List MiniParam) (body : List MiniStatement) : Doc :=
  methodDocOf kind (propertyNameDoc key) params (paramDocs params) body
    (Doc.joinWith .hardline (statementDocs body))

def functionDoc (isAsync isGen : Bool) (name : Option NEString)
    (params : List MiniParam) (body : List MiniStatement) : Doc :=
  functionDocOf isAsync isGen name params (paramDocs params) body
    (Doc.joinWith .hardline (statementDocs body))

/-- A statement list, one statement per line. -/
def statementsDoc (body : List MiniStatement) : Doc :=
  Doc.joinWith .hardline (statementDocs body)

/-- A brace enclosed statement list. -/
def blockDoc (body : List MiniStatement) : Doc := blockDocOf body (statementsDoc body)

/-- The body of an `if`, `for`, `while` or `with`, attached to its head. -/
def attachedBodyDoc (s : MiniStatement) : Doc := attachedBodyWith s (statementDoc s)

/-- The statements of one `case` of a `switch`. -/
def caseBodyDoc (body : List MiniStatement) : Doc := caseBodyWith body (statementsDoc body)

def declarationDoc (kind : VarKind) (decls : NEList MiniDeclarator) : Doc :=
  t (varKindText kind ++ " ")
    ++ .group (Doc.joinWith (t "," ++ .line) (declaratorDocs decls.toList))

/-! ## Modules -/

def specifierDoc (s : Specifier) : Doc :=
  t s.name.val ++ (match s.alias_ with | none => Doc.nil | some a => t (" as " ++ a.val))

def specifiersDoc (specs : List Specifier) : Doc :=
  sepList "{" "}" true true (specs.map specifierDoc)

/-- The `with { type: "json" }` of an import; nothing when there is no
attribute. -/
def importAttrsDoc (attrs : List ImportAttr) : Doc :=
  if attrs.isEmpty then Doc.nil
  else
    t " with "
      ++ sepList "{" "}" true true
          (attrs.map fun a =>
            t (encodeStringLiteral a.key ++ ": " ++ encodeStringLiteral a.value))

def importDoc : MiniImportDeclaration → Doc
  | .bare mod attrs =>
      t ("import " ++ encodeStringLiteral mod.val) ++ importAttrsDoc attrs ++ t ";"
  | .clause c =>
      let parts : List Doc :=
        (match c.default_ with | none => [] | some d => [t d.val])
        ++ (match c.namespace_ with | none => [] | some n => [t ("* as " ++ n.val)])
        ++ (match c.named with | none => [] | some specs => [specifiersDoc specs])
      t "import " ++ Doc.joinWith (t ", ") parts
        ++ t (" from " ++ encodeStringLiteral c.mod.val) ++ importAttrsDoc c.attrs ++ t ";"

def exportDoc : MiniExportDeclaration → Doc
  | .fromClause specs mod attrs =>
      t "export " ++ specifiersDoc specs ++ t (" from " ++ encodeStringLiteral mod.val)
        ++ importAttrsDoc attrs ++ t ";"
  | .locals specs => t "export " ++ specifiersDoc specs ++ t ";"
  | .all alias_ mod attrs =>
      t "export *"
        ++ (match alias_ with | none => Doc.nil | some n => t (" as " ++ n.val))
        ++ t (" from " ++ encodeStringLiteral mod.val) ++ importAttrsDoc attrs ++ t ";"
  | .defaultExpr e => t "export default " ++ exprDocWith 2 e (exprCore e) ++ t ";"
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
