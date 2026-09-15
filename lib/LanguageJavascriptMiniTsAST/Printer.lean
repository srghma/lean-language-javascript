import MiniTsAST.Syntax
import MiniAST.Unicode
import MiniTsAST.JSX
import MiniAST.Options

/-!
# The printer

A printer for `MiniTsAST` that reproduces the output of the `prettier`
code formatter.  It is read as a `Language.JavaScript.Options`,
prettier's options record, which every function of the printer takes as
an instance argument; `Language.JavaScript.defaultOptions` is prettier's
default style (two space indentation, eighty column lines, double quotes,
semicolons and trailing commas).

The layout decisions follow prettier's: the precedence-and-clarity
parenthesisation rules, the flattening of binary operator chains, the
assignment layouts, the member chain layout, and the hugging of a final
function argument.
-/

namespace Language.TypeScript.MiniTsAST

open Language.JavaScript
open Language.JavaScript.Doc
open Language.JavaScript.MiniAST
  (encodeStringLiteral encodeStringLiteralQuoted encodeJSXText encodeJSXAttrString
    encodeJSXAttrStringQuoted encodeTemplateText)

namespace Printer

/-- Prettier's default line width, which the entry points that are given
no options lay out for. -/
def defaultWidth : Nat := 80

variable [o : Options]

/-- The line width the layout aims at: prettier's `printWidth`. -/
def printWidth : Nat := Options.printWidth

/-- The number of columns of one indentation step: prettier's
`tabWidth`. -/
def indentWidth : Nat := Options.tabWidth

/-- Prettier's `tabWidth`, used by some of its heuristics. -/
def tabWidth : Nat := Options.tabWidth

private def t (s : String) : Doc := .text s

private def parens (d : Doc) : Doc := t "(" ++ d ++ t ")"

/-- Parenthesise `d` when `cond` holds. -/
def parenIf (cond : Bool) (d : Doc) : Doc := if cond then parens d else d

/-- The terminator of a statement: a semicolon, or nothing under
`semi: false`. -/
def semiDoc : Doc := t Options.semiText

/-- The break just inside the braces of an object type: a space while the
type stands on one line, and nothing at all under `bracketSpacing:
false`. -/
def braceLine : Doc := if Options.bracketSpacing then .line else .softline

/-- The separator between two members of an object type: a semicolon,
which under `semi: false` prettier writes only while the type stands on
one line, where the members would otherwise run together. -/
def tsMemberSep : Doc := if Options.semi then t ";" else .ifBreak .nil (t ";")

/-- The separator between two members of an object type that is written
over several lines: nothing under `semi: false`. -/
def tsBrokenMemberSep : Doc := if Options.semi then t ";" else .nil

/-- The semicolon after the last member of an object type, written only
where the type is broken over several lines, and not at all under
`semi: false`. -/
def tsMemberTrailer : Doc := if Options.semi then .ifBreak (t ";") .nil else .nil

/-- A string literal, quoted the way `singleQuote` asks for. -/
def strLit (s : String) : String := encodeStringLiteralQuoted Options.preferredQuote s

/-- The value of a JSX attribute, quoted the way `jsxSingleQuote` asks
for. -/
def jsxAttrLit (s : String) : String := encodeJSXAttrStringQuoted Options.preferredJSXQuote s

/-! ## Operators -/

def binOpText : BinOp → String
  | .and => "&&" | .or => "||" | .coalesce => "??"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .eq => "==" | .neq => "!=" | .strictEq => "===" | .strictNeq => "!=="
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .lsh => "<<" | .rsh => ">>" | .ursh => ">>>"
  | .plus => "+" | .minus => "-" | .times => "*" | .divide => "/" | .mod => "%"
  | .inOp => "in" | .instanceOf => "instanceof"

/-- Binary operator precedence, as prettier orders them; higher binds
tighter. -/
def binOpPrec : BinOp → Nat
  | .coalesce => 1
  | .or => 2
  | .and => 3
  | .bitOr => 4
  | .bitXor => 5
  | .bitAnd => 6
  | .eq | .neq | .strictEq | .strictNeq => 7
  | .lt | .le | .gt | .ge | .inOp | .instanceOf => 8
  | .lsh | .rsh | .ursh => 9
  | .plus | .minus => 10
  | .times | .divide | .mod => 11

/-- `&&`, `||` and `??`, the operators of a logical expression. -/
def isLogicalOp : BinOp → Bool
  | .and | .or | .coalesce => true
  | _ => false

def isEqualityOp : BinOp → Bool
  | .eq | .neq | .strictEq | .strictNeq => true
  | _ => false

def isMultiplicativeOp : BinOp → Bool
  | .times | .divide | .mod => true
  | _ => false

def isBitshiftOp : BinOp → Bool
  | .lsh | .rsh | .ursh => true
  | _ => false

def isBitwiseOp : BinOp → Bool
  | .bitAnd | .bitOr | .bitXor => true
  | o => isBitshiftOp o

/-- Whether a child operator of the same precedence may be flattened into
the operator chain of its parent. -/
def shouldFlatten (parentOp childOp : BinOp) : Bool :=
  binOpPrec parentOp == binOpPrec childOp
    && !(isEqualityOp parentOp && isEqualityOp childOp)
    && !((childOp == .mod && isMultiplicativeOp parentOp)
          || (parentOp == .mod && isMultiplicativeOp childOp))
    && !(childOp != parentOp && isMultiplicativeOp childOp && isMultiplicativeOp parentOp)
    && !(isBitshiftOp parentOp && isBitshiftOp childOp)

def unaryOpText : UnaryOp → String
  | .not => "!" | .tilde => "~" | .plus => "+" | .minus => "-"
  | .typeof => "typeof " | .void => "void " | .delete => "delete "
  | .preIncr => "++" | .preDecr => "--"

def postfixOpText : PostfixOp → String
  | .incr => "++" | .decr => "--"

def assignOpText : AssignOp → String
  | .assign => "="
  | .logicalAnd => "&&=" | .logicalOr => "||=" | .coalesce => "??="
  | .plus => "+=" | .minus => "-=" | .times => "*=" | .divide => "/=" | .mod => "%="
  | .lsh => "<<=" | .rsh => ">>=" | .ursh => ">>>="
  | .bitAnd => "&=" | .bitXor => "^=" | .bitOr => "|="

def varKindText : VarKind → String
  | .var => "var" | .let_ => "let" | .const => "const"

/-! ## Positions -/

/-- The syntactic position an expression is printed in.  It decides both
the parentheses the expression needs and, for a binary expression, how its
operator chain is laid out. -/
inductive Pos where
  /-- An expression statement. -/
  | statement
  /-- The condition of an `if`, `while`, `switch` or `do ... while`. -/
  | ifTest
  /-- The object of a `with`.  It stands between parentheses like the
  condition of a `while`, but prettier does not treat those parentheses as
  the ones of a condition: a binary expression written here is laid out as
  it is anywhere else, and so is grouped and indented. -/
  | withObject
  /-- The initialiser or the update of a `for (;;)`. -/
  | forHeadPart
  /-- The test of a `for (;;)`. -/
  | forTest
  /-- An operand of a comma operator in the head of a `for (;;)`; `tail`
  says that it is not the first one, and so already stands inside the
  indentation the chain gives its operands. -/
  | forSeqTail (tail : Bool)
  /-- The argument of `return` or `throw`. -/
  | returnThrow
  /-- Inside `[ ]`. -/
  | computed
  /-- Inside a `${ }` substitution of a template literal. -/
  | templateSubst
  /-- Another operand of the comma operator.  `indented` says that the
  chain indents the operands after the first, which it does when the chain
  is an expression statement; `tail` that this operand is not the first
  one, and so already stands inside that indentation. -/
  | seqTail (indented tail : Bool)
  /-- An argument of a call, an element of an array, ... -/
  | arg
  /-- An element of an array literal. -/
  | arrayElement
  /-- The value a `case` of a `switch` is compared with. -/
  | caseTest
  /-- The object a `for (... in ...)` or a `for (... of ...)` walks. -/
  | forInObject
  /-- The expression of a `{ }` substitution written as a child of a JSX
  element. -/
  | jsxChildExpr
  /-- The expression of a `{ }` value of a JSX attribute. -/
  | jsxAttrExpr
  /-- An argument of a call or of a `new`. -/
  | callArg
  /-- An argument of a call of a test framework, whose arguments prettier
  keeps on the line of the call; a function written here keeps its whole
  parameter list on one line as well. -/
  | testCallArg
  /-- The argument of a call that the layout may expand in place, keeping
  the rest of the call on one line.  `sole` says that it is the only
  argument, where a function expression keeps its parameter list on one
  line only when every parameter is a plain identifier; `newExpr` that the
  call is a `new`, where the parameter list keeps its own layout; `first`
  that it is the first argument rather than the last one, where a function
  expression keeps its own layout as well. -/
  | hugArg (sole newExpr first : Bool)
  /-- The right hand side of an assignment or of a declarator.  `nested`
  says that the assignment is not itself an expression statement or a
  declaration, so that a further assignment here is laid out as a link of
  a chain; `inlineMembers` that the assignment is one whose left hand side
  is not a plain identifier, which keeps the member accesses of the right
  hand side on the line of their object; `ofAssign` that the parent is an
  assignment expression, rather than a declarator or a default value;
  `arrowChain` that the assignment lays a chain of arrow functions written
  here out as the tail of a chain of assignments, which always breaks the
  signatures of the chain. -/
  | assignRhs (nested inlineMembers ofAssign arrowChain : Bool)
  /-- The value of a property of an object literal, or of a class field;
  `accessor` says that it is the value of a field written with the
  `accessor` keyword, whose operator chains prettier indents once more
  than those of an ordinary field. -/
  | propValue (accessor classField : Bool)
  /-- The body of an arrow function. -/
  | arrowBody
  /-- The body of an arrow function that is itself expanded in place as
  the argument of a call. -/
  | hugArrowBody
  /-- The operand of `...`. -/
  | spreadArg
  /-- The operand of the `...` of a `{...children}` written as a child of
  a JSX element, which takes fewer parentheses than the operand of a `...`
  written anywhere else: the braces around it already delimit it. -/
  | jsxSpreadChildArg
  /-- The argument of `yield` or of `yield*`.  It needs the same
  parentheses as an argument of a call, but a conditional expression in a
  chain written here is indented inside the parentheses it needs. -/
  | yieldArg
  /-- The consequent of a conditional expression.  `outerIndents` says
  that the conditional itself stands in a `return`, a `throw`, or the
  arguments or the callee of a call or a `new`, where prettier indents the
  operator chain of a binary expression written here; `jsx` that the chain
  of conditionals this one belongs to holds a JSX element, which prettier
  lays the whole chain out for. -/
  | ternaryBranch (outerIndents jsx : Bool)
  /-- The alternate of a conditional expression; `outerIndents` and `jsx`
  are as for the consequent. -/
  | ternaryAlternate (outerIndents jsx : Bool)
  /-- The condition of a conditional expression; `outerIndents` is as for
  the consequent. -/
  | ternaryTest (outerIndents : Bool)
  /-- The operand of a prefix or postfix operator. -/
  | unaryArg
  /-- The operand of `await`.  It needs the same parentheses as the
  operand of a prefix operator, but a binary expression here is laid out
  as it is anywhere else, rather than breaking between the parentheses. -/
  | awaitArg
  /-- The object of a member access.  `computed` says that the access is
  written `[ ]` rather than `.`; `extra` that the chain the access belongs
  to stands in one of the places prettier indents a conditional expression
  inside the parentheses it needs: the right hand side of an assignment,
  or the argument of `return`, `throw`, `await` or a unary operator;
  `inline` that the chain is assigned to something other than a plain
  identifier, which keeps the access on the line of its object. -/
  | memberObject (computed extra inline : Bool)
  /-- The left hand side of an assignment. -/
  | assignTarget
  /-- The tag of a tagged template literal. -/
  | templateTag
  /-- The callee of a `new`. -/
  | newCallee
  /-- The expression of a decorator, `@expr`.  It is parenthesised as the
  object of a member access is, but a member access written here keeps
  the line of its object, as prettier writes the `.` of a decorator. -/
  | decorator
  /-- The callee of a call.  `extra` is as for the object of a member
  access; `parentArgs` is the number of arguments the call itself takes,
  which decides whether a call written here is a link of a long curried
  chain, `f(a, b)(c)`. -/
  | callee (extra : Bool) (parentArgs : Nat)
  /-- The `extends` clause of a class. -/
  | classHeritage
  /-- The expression of an `as` or of a `satisfies`.  `extra` says that
  the `as` itself stands where prettier indents what it holds inside the
  parentheses it needs: on the right of an assignment or of a declarator,
  or as the argument of `return`, `throw`, `await`, `yield` or a unary
  operator. -/
  | tsTypeOperand (extra : Bool)
  /-- The expression of a `!`, or the one an instantiation `f<T>` reads
  at a type.  `extra` says that the `!` itself stands where prettier
  indents what it holds inside the parentheses it needs: on the right of
  an assignment or of a declarator, or as the argument of `return`,
  `throw`, `await`, `yield` or a unary operator. -/
  | tsNonNullArg (extra : Bool)
  /-- An operand of a binary or logical operator. -/
  | binOperand (op : BinOp) (isLeft : Bool)
  /-- What a TypeScript export assignment exports, `export = expr;`.  It
  takes the parentheses an argument takes, and a JSX element written here
  keeps parentheses of its own, unlike one exported by default. -/
  | tsExportAssign
  /-- Any other position; parentheses as for an argument. -/
  | generic
deriving BEq, Inhabited

/-- The precedence an expression must have not to be parenthesised. -/
def Pos.minPrec : Pos → Nat
  | .statement | .ifTest | .withObject | .forHeadPart | .forTest | .forSeqTail .. | .returnThrow
  | .computed | .templateSubst | .seqTail .. => 0
  | .arg | .arrayElement | .caseTest | .forInObject | .jsxChildExpr | .jsxAttrExpr
  | .callArg | .testCallArg | .hugArg .. | .assignRhs .. | .propValue .. | .arrowBody
  | .yieldArg
  | .hugArrowBody | .spreadArg | .jsxSpreadChildArg | .ternaryBranch ..
  | .ternaryAlternate .. | .tsExportAssign | .generic => 1
  | .ternaryTest .. => 3
  | .unaryArg | .awaitArg => 14
  | .tsTypeOperand .. => 10
  | .memberObject .. | .assignTarget | .templateTag | .callee .. | .newCallee
  | .classHeritage | .tsNonNullArg .. | .decorator => 16
  | .binOperand op _ => 2 + binOpPrec op

/-- The precedence of an expression, from 0 for the comma operator to 17
for a primary expression. -/
def exprPrec : MiniExpr → Nat
  | .seq _ _ => 0
  | .assign .. | .assignPattern .. | .arrow .. | .yield _ | .yieldFrom _ | .spread _ => 1
  | .ternary .. => 2
  | .binary _ op _ => 2 + binOpPrec op
  | .asExpr .. | .satisfies .. => 10
  | .unary .. | .await _ => 14
  | .postfix .. => 15
  | .call .. | .dot .. | .privateDot .. | .index .. | .new .. | .chain ..
  | .importCall .. | .nonNull _ | .instantiation .. => 16
  | .superDot .. | .superIndex .. | .superCall .. => 16
  | .template (some _) _ _ _ => 16
  | _ => 17

/-- Whether a binary operand needs parentheses inside a binary parent. -/
def binaryOperandParens (parentOp childOp : BinOp) (isLeft : Bool) : Bool :=
  if isLogicalOp parentOp && isLogicalOp childOp then parentOp != childOp
  else
    let pp := binOpPrec parentOp
    let cp := binOpPrec childOp
    if pp > cp then true
    else if pp == cp && !isLeft then true
    else if pp == cp && !shouldFlatten parentOp childOp then true
    else if pp < cp && childOp == .mod && (parentOp == .plus || parentOp == .minus) then true
    else if isBitwiseOp parentOp then true
    else false

/-- The position the parenthesisation rules use: the positions that differ
only in the layout they ask for are the same for them. -/
def Pos.forParens : Pos → Pos
  | .withObject => .ifTest
  | .testCallArg => .callArg
  | .assignTarget | .templateTag | .memberObject .. | .decorator =>
      .memberObject false false false
  | .newCallee | .callee .. => .callee false 0
  | .hugArg .. => .hugArg false false false
  | .yieldArg | .arrayElement | .caseTest | .forInObject | .jsxChildExpr | .jsxAttrExpr => .arg
  | .assignRhs .. => .assignRhs false false false false
  | .ternaryBranch .. => .ternaryBranch false false
  | .ternaryAlternate .. => .ternaryAlternate false false
  | .ternaryTest _ => .ternaryTest false
  | p => p

/-- Whether the position is the object of a member access. -/
def isMemberObjectPos : Pos → Bool
  | .memberObject .. => true
  | _ => false

/-- Whether the position is the callee of a call. -/
def isCalleePos : Pos → Bool
  | .callee .. => true
  | _ => false

/-- Whether the position is the right hand side of an assignment or of a
declarator. -/
def isAssignRhsPos : Pos → Bool
  | .assignRhs .. => true
  | _ => false

/-- Whether prettier parenthesises a JSX element written here.  It writes
no parentheses where a `<` can only be read as the start of an element:
an expression statement, an element of an array literal, an argument of a
call or of a `new`, an operand of a binary or logical operator, a branch
of a conditional, either side of an assignment, the value of a property of
an object literal, the body of an arrow function, the argument of
`return`, `throw` or `yield`, what is exported by default, and anything
written inside a JSX element.  Everywhere else it writes them. -/
def jsxNeedsParens : Pos → Bool
  | .statement | .arrayElement | .arg | .generic => false
  | .callArg | .testCallArg | .hugArg .. => false
  | .assignRhs .. | .assignTarget => false
  | .binOperand .. => false
  | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => false
  | .arrowBody | .hugArrowBody => false
  | .propValue _ classField => classField
  | .returnThrow | .yieldArg => false
  | .jsxChildExpr | .jsxAttrExpr => false
  | _ => true

/-- Whether prettier writes no parentheses of its own around a JSX
element standing here: it does not where the element already stands
between delimiters of its own, that is, as a statement, an element of an
array literal, an argument of a call, a branch of a conditional, or inside
a `{ }` of another element.  The callee of a call and of a `new` are of
that kind too: the parentheses a `<` asks for there are written around the
element as it stands, rather than around lines of its own. -/
def jsxNoWrapPos : Pos → Bool
  | .statement | .arrayElement | .callArg | .testCallArg | .hugArg .. => true
  | .jsxChildExpr | .jsxAttrExpr => true
  | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => true
  | .callee .. | .newCallee => true
  | _ => false

/-- Whether a chain holds a link written with `?.`.  A chain whose links
are all `!`, `.` and calls is an ordinary member expression, which asks
for no parentheses of its own. -/
def chainIsOptional (links : NEList MiniChainLink) : Bool :=
  links.toList.any fun link =>
    match link with
    | .dot o _ | .privateDot o _ | .index o _ | .call o _ _ => o
    | .nonNull => false

/-- Whether the expression has to be parenthesised in this position. -/
def needsParens (pos0 : Pos) (e : MiniExpr) : Bool :=
  let pos := pos0.forParens
  match e with
  | .binary _ op _ =>
      match pos with
      | .binOperand pop isLeft => binaryOperandParens pop op isLeft
      | .unaryArg | .awaitArg | .callee .. | .spreadArg | .memberObject ..
      | .tsTypeOperand ..
      | .classHeritage => true
      | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => op == .coalesce
      | _ => exprPrec e < pos.minPrec
  -- `await await a`: an `await` written as the operand of another one
  -- keeps no parentheses, while a `yield` written there does
  | .await _ =>
      match pos with
      | .awaitArg => false
      | .unaryArg | .spreadArg | .memberObject .. | .callee ..
      | .tsTypeOperand ..
      | .ternaryTest .. => true
      | .binOperand .. => true
      | _ => exprPrec e < pos.minPrec
  | .yield _ | .yieldFrom _ =>
      match pos with
      | .unaryArg | .awaitArg | .spreadArg | .memberObject .. | .callee ..
      | .tsTypeOperand ..
      | .ternaryTest .. => true
      | .binOperand .. => true
      | _ => exprPrec e < pos.minPrec
  | .seq _ _ =>
      match pos with
      | .forHeadPart | .forTest | .forSeqTail .. | .seqTail .. => false
      | _ => true
  -- An assignment is parenthesised everywhere but in an expression
  -- statement, in the head of a `for (;;)` and on the right of another
  -- assignment; `const x = (a = 1);` is parenthesised, since the
  -- declarator is not an assignment expression
  | .assign _ _ _ =>
      match pos0 with
      | .statement | .forHeadPart | .forSeqTail .. => false
      | .assignRhs _ _ ofAssign _ => !ofAssign
      | _ => true
  -- `({ a } = o);`: an assignment to an object pattern is parenthesised
  -- even as a statement of its own, since it would otherwise be read as a
  -- block
  | .assignPattern l _ =>
      match pos0 with
      | .statement => (match l with | .object .. => true | _ => false)
      | .forHeadPart | .forSeqTail .. => false
      | .assignRhs _ _ ofAssign _ => !ofAssign
      | _ => true
  -- `f(...(a ? b : c))`: a conditional spread needs parentheses.  Under
  -- `experimentalTernaries` a conditional written as the test of another
  -- takes none: the layout writes the two of them as one chain
  | .ternary .. =>
      pos == .spreadArg
        || (if Options.experimentalTernaries && (match pos with
              | .ternaryTest _ => true | _ => false) then false
            else exprPrec e < pos.minPrec)
  -- `(a + b) as T`: prettier parenthesises an `as` or a `satisfies`
  -- written as an operand of an operator, anywhere in a conditional,
  -- and after a `...`, where the parentheses are not needed but say
  -- what is read at the type
  | .asExpr .. | .satisfies .. =>
      match pos with
      | .spreadArg | .jsxSpreadChildArg => true
      | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => true
      | .binOperand .. => true
      | _ => exprPrec e < pos.minPrec
  -- `(void a) in b`: a unary operand of `in` or of `instanceof` keeps its
  -- parentheses on the left of the operator
  -- an update written with `++` or `--` is not one of them
  | .unary uop _ =>
      (uop != .preIncr && uop != .preDecr &&
        match pos with
        | .binOperand op true => op == .inOp || op == .instanceOf
        | _ => false)
        || exprPrec e < pos.minPrec
  -- `(x) => ({ a: 1 })`: an object literal body needs parentheses
  | .object _ => pos == .arrowBody || pos == .hugArrowBody
  -- `(5).toFixed()`: a number needs parentheses to be the object of a
  -- `.`, which a `BigInt` literal, written with its `n`, does not
  | .number (.bigint ..) => exprPrec e < pos.minPrec
  | .number _ => isMemberObjectPos pos
  -- `(f<T>).x`: prettier keeps parentheses around an instantiation
  -- expression read through a `.`, a `[]` or a `?.`, and writes none
  -- anywhere else — not as the callee of a call or of a `new`, not
  -- before a `!`, and not as an operand
  | .instantiation .. =>
      match pos0 with
      | .memberObject .. | .decorator => true
      | .templateTag => false
      | _ => exprPrec e < pos.minPrec
  -- `(a?.b).c` is not `a?.b.c`, so the parentheses have to stay; a chain
  -- which holds no `?.` at all — `a.b!()` — is read as the member
  -- expression it is, and keeps none
  | .chain _ links =>
      chainIsOptional links && (isMemberObjectPos pos || isCalleePos pos)
  | .jsx _ => jsxNeedsParens pos0
  -- `(function () {})()` and ``(function () {})`t` ``: a function
  -- expression keeps its parentheses as the callee of a call and as the
  -- tag of a template, but a class expression does not
  | .func .. => isCalleePos pos || pos0 == .templateTag || exprPrec e < pos.minPrec
  | .classExpr .. => exprPrec e < pos.minPrec
  | _ => exprPrec e < pos.minPrec

/-- Whether the expression is a class expression which has decorators.
Prettier breaks the parentheses such a class takes, so that the decorators
stand on lines of their own inside them. -/
def isDecoratedClass : MiniExpr → Bool
  | .classExpr (_ :: _) _ _ _ _ _ => true
  | _ => false

/-- The parentheses the expression `e` takes, given the document it prints
as.  A decorated class expression breaks inside them. -/
def parenIfExpr (cond : Bool) (e : MiniExpr) (d : Doc) : Doc :=
  if !cond then d
  else if isDecoratedClass e then
    t "(" ++ .nest indentWidth (.hardline ++ d) ++ .hardline ++ t ")"
  else parens d

/-- An expression in position `pos`, given the document it prints as. -/
def inPos (pos : Pos) (e : MiniExpr) (d : Doc) : Doc := parenIfExpr (needsParens pos e) e d

/-- Whether a conditional expression in the object of a member access, or
in the callee of a call, that stands here is indented inside the
parentheses it needs.  Prettier does so when the chain that holds it is
the right hand side of an assignment or of a declarator, or the argument
of `return`, `throw`, `await`, `yield` or a unary operator. -/
def extraIndentRoot : Pos → Bool
  | .assignRhs .. | .returnThrow | .unaryArg | .awaitArg | .yieldArg => true
  | .memberObject _ extra _ => extra
  | .callee extra _ => extra
  | _ => false

/-- Whether prettier lets the parentheses an `await` expression takes here
break, writing its operand on a line of its own inside them.  It does so
where the `await` is the object of a member access or the callee of a
call, which are the places the parentheses come from; the callee of a
`new` and the tag of a template literal are not among them. -/
def awaitBreaksInParens : Pos → Bool
  | .memberObject .. | .callee .. => true
  | _ => false

/-- Whether prettier lets the parentheses an `as` or a `satisfies`
expression takes here break, writing the expression on a line of its own
inside them.  It does so where the parentheses come from reading the
expression through a member access, calling it, or building it with
`new`; the tag of a template literal, and an operand of an operator, keep
theirs on the line. -/
def tsTypeExprBreaksInParens : Pos → Bool
  | .memberObject .. | .callee .. | .newCallee => true
  | _ => false

/-- Whether the position is the test, the consequent or the alternate of a
conditional expression. -/
def isTernaryPos : Pos → Bool
  | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => true
  | _ => false

/-- For a position inside a conditional expression: whether the
conditional itself stands where prettier indents the operator chain of a
binary expression written in it. -/
def ternaryOuterIndents : Pos → Bool
  | .ternaryTest g | .ternaryBranch g _ | .ternaryAlternate g _ => g
  | _ => false

/-- Whether a conditional expression in this position is the child of a
`return`, of a `throw`, or of a call or a `new`, which is what decides
whether the operator chain of a binary expression inside the conditional
is indented. -/
def ternaryParentIndents : Pos → Bool
  | .returnThrow | .callArg | .hugArg .. | .callee .. | .newCallee => true
  | _ => false

/-- Whether prettier keeps the member accesses of a chain that stands here
on the line of their object: the chain is assigned to something other than
a plain identifier. -/
def inlineMemberRoot : Pos → Bool
  | .assignRhs _ inline _ _ => inline
  | .memberObject _ _ inline => inline
  -- the left hand side of an assignment is a member access itself, and so
  -- is not a plain identifier
  | .assignTarget => true
  -- prettier looks past the accesses of a chain for what holds it, so
  -- every access of the callee of a `new` keeps its line
  | .newCallee => true
  | _ => false

/-- The position of the object of a member access that stands in `pos`;
`computed` says that the access is written `[ ]`. -/
def memberObjectPos (computed : Bool) (pos : Pos) : Pos :=
  .memberObject computed (extraIndentRoot pos) (inlineMemberRoot pos)

/-- The position of the callee of a call that stands in `pos` and takes
`parentArgs` arguments. -/
def calleePos (pos : Pos) (parentArgs : Nat) : Pos :=
  .callee (extraIndentRoot pos) parentArgs

/-- Whether a call with `argCount` arguments written in `pos` is a link of
a long curried chain, `f(a, b)(c)`: it is the callee of a call that takes
fewer arguments than it does, and at least one.  Prettier leaves the
argument list of such a call ungrouped, so that it breaks together with
the line that holds the call rather than on its own. -/
def isLongCurriedCall (pos : Pos) (argCount : Nat) : Bool :=
  match pos with
  | .callee _ parentArgs => 0 < parentArgs && parentArgs < argCount
  | _ => false

/-- Whether the expression is one prettier counts as a call: an ordinary
call, a call of `super`, a dynamic `import()`, or an optional chain whose
last link is a call.  A `new` is not one of them. -/
def isCallLikeExpr : MiniExpr → Bool
  | .call .. | .superCall .. | .importCall .. => true
  | .chain _ links =>
      match links.toList.getLast? with
      | some (.call ..) => true
      | _ => false
  | _ => false

/-- Whether the expression may not be written at the start of a statement,
because it would be read as a block, a function declaration or a class
declaration. -/
def cannotStartStatement : MiniExpr → Bool
  | .object _ | .func .. | .classExpr .. => true
  | _ => false

/-- Whether the link of an optional chain is written with `?.`. -/
def chainLinkIsOptional : MiniChainLink → Bool
  | .dot o _ | .privateDot o _ | .index o _ => o
  | .call o _ _ => o
  | .nonNull => false

/-- Whether the link of an optional chain is a call. -/
def chainLinkIsCall : MiniChainLink → Bool
  | .call .. => true
  | _ => false

/-- Whether every link is a `!`, so that the link in front of them is the
last one that is not. -/
def linksAllNonNull : List MiniChainLink → Bool
  | [] => true
  | .nonNull :: rest => linksAllNonNull rest
  | _ => false

/-- Whether an optional chain used as the base of another one merges into
it: it does when the link that follows it is optional, which makes the
parentheses around the base unnecessary. -/
def chainMergesBase (links : NEList MiniChainLink) : Bool := chainLinkIsOptional links.hd

/-- Whether the leftmost token of the expression opens a function or a
class expression, so that `export default` in front of it would be read as
a declaration.  `pos` is the position the expression itself stands in: the
walk stops at a subexpression which is parenthesised there, since the
parentheses are then the leftmost token.  A call or a tagged template
whose callee is a function expression is one such place. -/
def startsWithFunctionOrClassAt (merged : Bool) (pos : Pos) (e : MiniExpr) : Bool :=
  -- an optional chain that merges into the one which holds it keeps no
  -- parentheses of its own, so the walk goes on into its base
  let isChain := match e with | .chain .. => true | _ => false
  if needsParens pos e && !(merged && isChain) then false
  else
    match e with
    | .func .. | .classExpr .. => true
    | .binary l op _ => startsWithFunctionOrClassAt false (.binOperand op true) l
    | .assign l _ _ => startsWithFunctionOrClassAt false .assignTarget l
    | .seq l _ => startsWithFunctionOrClassAt false (.seqTail false false) l
    | .ternary c _ _ => startsWithFunctionOrClassAt false (.ternaryTest false) c
    | .postfix l _ => startsWithFunctionOrClassAt false .unaryArg l
    | .dot o _ | .privateDot o _ | .index o _ =>
        startsWithFunctionOrClassAt false (.memberObject false false false) o
    | .template (some tag) _ _ _ => startsWithFunctionOrClassAt false .templateTag tag
    | .call callee _ _ => startsWithFunctionOrClassAt false (.callee false 0) callee
    | .asExpr o _ | .satisfies o _ => startsWithFunctionOrClassAt false (.tsTypeOperand false) o
    | .nonNull o => startsWithFunctionOrClassAt false (.tsNonNullArg false) o
    | .chain base links =>
        -- the base of a chain stands in parentheses unless the first link
        -- of the chain is optional, which merges the two
        startsWithFunctionOrClassAt (chainMergesBase links)
          (.memberObject false false false) base
    | _ => false

/-- Whether the leftmost token of an expression written after
`export default` opens a function or a class expression. -/
def startsWithFunctionOrClass (e : MiniExpr) : Bool :=
  startsWithFunctionOrClassAt false .generic e

/-- Where the leftmost token of an expression stands, which says which
expressions the place forbids there. -/
inductive StartCtx where
  /-- Not a place where the leftmost token matters. -/
  | none
  /-- The start of an expression statement, which may not be read as a
  block, a function declaration or a class declaration. -/
  | statement
  /-- The start of the body of an arrow function, which may not be read as
  a block. -/
  | arrowBody
  /-- The start of the initialiser of a `for (;;)`, where the identifier
  `let` would be read as the keyword when a `[` follows it. -/
  | forInit
  /-- The start of the binder of a `for (... in ...)` or of a
  `for (... of ...)`, which may not be the identifier `let` at all. -/
  | forInHead
  /-- The leftmost token of the operand of an `await`.  Nothing may not be
  written there, but prettier does not group the parentheses an `await`
  standing here takes, so that they break with the line that holds the
  `await` which the operand belongs to. -/
  | awaitArgument
  /-- An argument of a call which is itself written directly in a `{ }` of
  a JSX element.  Prettier always writes a JSX element that is the body of
  an arrow function standing here on lines of its own. -/
  | jsxCallArg
  /-- The start of the body of an arrow function which is the argument of
  such a call. -/
  | jsxArrowBody
deriving BEq, Inhabited

/-- Whether the expression is the identifier `let`, which is a keyword
where a declaration may stand. -/
def isLetIdent : MiniExpr → Bool
  | .ident n => n.val == "let"
  | _ => false

/-- Whether the position is the object of a `[ ]` access, where the
identifier `let` is read as the keyword of a declaration. -/
def isComputedMemberObjectPos : Pos → Bool
  | .memberObject computed _ _ => computed
  | _ => false

/-- Whether the expression needs parentheses because of what stands to its
left.  `pos` is the position of the expression itself, which says whether
a `[` follows the identifier `let` written here. -/
def cannotStartWith : StartCtx → Pos → MiniExpr → Bool
  | .none, _, _ => false
  | .awaitArgument, _, _ => false
  | .forInit, pos, e => isLetIdent e && isComputedMemberObjectPos pos
  | .forInHead, _, e => isLetIdent e
  | .statement, pos, e =>
      cannotStartStatement e || (isLetIdent e && isComputedMemberObjectPos pos)
  | .arrowBody, _, .object _ => true
  | .arrowBody, _, _ => false
  | .jsxArrowBody, _, .object _ => true
  | .jsxArrowBody, _, _ => false
  | .jsxCallArg, _, _ => false

/-- The start context an argument of a call is printed with.  The mark
that says the call stands directly in a `{ }` of a JSX element belongs to
an arrow function written as the argument itself: a JSX element deeper
inside another kind of argument, such as the test of a conditional, is
not one prettier writes on lines of its own. -/
def argStartCtx (st : StartCtx) : MiniExpr → StartCtx
  | .arrow .. => st
  | _ => .none

/-- An expression in position `pos`, where `atStart` says what it is the
leftmost part of, so that an object literal, a function or a class
expression there needs parentheses. -/
def inPosStart (atStart : StartCtx) (pos : Pos) (e : MiniExpr) (d : Doc) : Doc :=
  parenIf (needsParens pos e || cannotStartWith atStart pos e) d

/-! ## Small predicates on expressions -/

def isLogicalExpr : MiniExpr → Bool
  | .binary _ op _ => isLogicalOp op
  | _ => false

def isBinaryish : MiniExpr → Bool
  | .binary .. => true
  | _ => false

/-- The kind of a node, as prettier distinguishes `BinaryExpression` from
`LogicalExpression`. -/
inductive BinKind where
  | logical | arith | other
deriving BEq, Inhabited

def binKind : MiniExpr → BinKind
  | .binary _ op _ => if isLogicalOp op then .logical else .arith
  | _ => .other

/-- The last operand of a chain of the same logical operator that leans to
the right: the right hand operand of the chain once it is rebalanced.  A
chain of one logical operator is written without parentheses, so a tree
which leans to the right is read back as one which leans to the left, and
it is the operand of the tree so read that the layout looks at. -/
def logicalLastOperand (op : BinOp) : MiniExpr → MiniExpr
  | .binary l rop r =>
      if isLogicalOp op && rop == op then logicalLastOperand op r else .binary l rop r
  | e => e

/-- A logical expression whose right operand is a non-empty object or
array literal, or a JSX element, is kept on one line. -/
def shouldInlineLogical : MiniExpr → Bool
  | .binary _ op r =>
      isLogicalOp op &&
        (match logicalLastOperand op r with
          | .object (_ :: _) => true
          | .array (_ :: _) => true
          | .jsx _ => true
          | _ => false)
  | _ => false

def isFunctionLike : MiniExpr → Bool
  | .func .. | .arrow .. => true
  | _ => false

def isNumericLit : MiniExpr → Bool
  | .number _ => true
  | _ => false

def isStringLit : MiniExpr → Bool
  | .string _ => true
  | _ => false

/-- `this`, or an identifier. -/
def isSingleWord : MiniExpr → Bool
  | .ident _ | .this | .privateName _ => true
  | _ => false

def isLiteralExpr : MiniExpr → Bool
  | .number _ | .string _ | .regex _ | .null | .true_ | .false_ => true
  | _ => false

/-- A name prettier treats as a factory: it starts with a capital letter,
or consists of `_` and `$` only. -/
def isFactoryName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => c.isUpper || s.all (fun ch => ch == '_' || ch == '$')

/-- Whether the expression is one of the simple arguments prettier allows
in a member chain that is printed on one line. -/
def isSimpleCallArgument : Nat → MiniExpr → Bool
  | 0, _ => false
  | _ + 1, .regex r => r.source.val.length ≤ 5
  | d + 1, e =>
    match e with
    | .number _ | .string _ | .null | .true_ | .false_ => true
    | .ident _ | .this | .privateName _ => true
    -- a tagged template is not one of them
    | .template none _ head parts =>
        !head.contains '\n' && simpleTemplateParts d parts
    | .object props => simpleProps d props
    | .array els => simpleElements d els
    | .call f _ args => isSimpleCallArgument (d + 1) f && args.length ≤ d + 1 && simpleArgs d args
    | .new f _ args => isSimpleCallArgument (d + 1) f && args.length ≤ d + 1 && simpleArgs d args
    | .dot o _ => isSimpleCallArgument (d + 1) o
    | .privateDot o _ => isSimpleCallArgument (d + 1) o
    | .index o i => isSimpleCallArgument (d + 1) o && isSimpleCallArgument (d + 1) i
    | .unary op a =>
        (op == .not || op == .minus || op == .plus || op == .tilde
          || op == .preIncr || op == .preDecr)
          && isSimpleCallArgument (d + 1) a
    | .postfix a _ => isSimpleCallArgument (d + 1) a
    -- a `!` is read through: `a!.b()` is as simple as `a.b()`
    | .nonNull a => isSimpleCallArgument (d + 1) a
    | .chain base ⟨hd, tl⟩ =>
        isSimpleCallArgument (d + 1) base && simpleChainLink d hd && simpleChainLinks d tl
    -- a dynamic `import()` is call-like, but has no callee to look at
    | .importCall spec options =>
        (match options with
          | none => true
          | some o => 2 ≤ d + 1 && isSimpleCallArgument d o)
          && isSimpleCallArgument d spec
    | _ => false
where
  simpleArgs (d : Nat) : List MiniExpr → Bool
    | [] => true
    | a :: rest => isSimpleCallArgument d a && simpleArgs d rest
  simpleElements (d : Nat) : List MiniArrayElement → Bool
    | [] => true
    | .hole :: rest => simpleElements d rest
    | .elem a :: rest => isSimpleCallArgument d a && simpleElements d rest
  simpleProps (d : Nat) : List MiniProperty → Bool
    | [] => true
    | .shorthand _ :: rest => simpleProps d rest
    | .keyValue k v :: rest =>
        (match k with | .computed _ => false | _ => true)
          && isSimpleCallArgument d v && simpleProps d rest
    | _ => false
  simpleTemplateParts (d : Nat) : List MiniTemplatePart → Bool
    | [] => true
    | ⟨e, suffix⟩ :: rest =>
        isSimpleCallArgument d e && !suffix.contains '\n' && simpleTemplateParts d rest
  simpleChainLink (d : Nat) : MiniChainLink → Bool
    | .dot .. | .privateDot .. | .nonNull => true
    | .index _ i => isSimpleCallArgument (d + 1) i
    | .call _ _ args => args.length ≤ d + 1 && simpleArgs d args
  simpleChainLinks (d : Nat) : List MiniChainLink → Bool
    | [] => true
    | l :: rest => simpleChainLink d l && simpleChainLinks d rest

/-- Whether `e` is a chain of member accesses ending in an identifier or
`this`, which prettier breaks after the `=` of an assignment. -/
def isMemberExpressionChain : MiniExpr → Bool
  | .dot o _ | .privateDot o _ | .index o _ =>
      match o with
      | .ident _ | .this => true
      | _ => isMemberExpressionChain o
  | _ => false

/-- The length prettier calls short for the lone argument of a call: a
quarter of the line width. -/
def shortArgWidth : Nat := Options.printWidth / 4

/-- Whether the lone argument of a call is short enough for the call to
keep its line. -/
def isLoneShortArgument : MiniExpr → Bool
  | .this => true
  | .ident n => n.val.length ≤ shortArgWidth
  | .string s => (strLit s).length ≤ shortArgWidth
  | .number _ => true
  -- `++x` and `--x` update what they read, and are not unary operators to
  -- prettier, which does not read through them
  | .unary .preIncr _ | .unary .preDecr _ => false
  -- the argument of any unary operator, `!` and `typeof` included, is
  -- read through
  | .unary _ a => isLoneShortArgument a
  | .regex r => r.source.val.length ≤ shortArgWidth
  -- a template literal of no substitution, whose text is short and stands
  -- on one line
  | .template none _ head [] =>
      (encodeTemplateText head).length ≤ shortArgWidth && !head.contains '\n'
  | .call (.ident n) _ [] => n.val.length + 2 ≤ shortArgWidth
  | e => isLiteralExpr e

/-- Whether the arguments of a call let the call keep its line: there are
none, or there is one short one. -/
def argumentsAreShort : List MiniExpr → Bool
  | [] => true
  | [a] => isLoneShortArgument a
  | _ => false

/-- Whether the type arguments of a call are complex ones, which prettier
counts as breakable however short the call is: there is more than one of
them, or the one there is is a union, an intersection or an object
type. -/
def tsTypeArgsAreComplex : List MiniTsType → Bool
  | [] => false
  | [ty] =>
      match ty with
      | .union _ | .intersection _ | .objectType _ => true
      | _ => false
  | _ => true

/-- Whether the links of an optional chain, outermost first, make a chain
prettier considers poorly breakable.  `baseOk` says whether the base of
the chain is one. -/
def linksArePoorlyBreakable (baseOk : Bool) : List MiniChainLink → Bool
  | [] => baseOk
  | .call _ targs args :: rest =>
      argumentsAreShort args && !tsTypeArgsAreComplex targs
        && (match rest with
            -- the callee of the call is itself a call
            | .call .. :: _ => false
            | _ => linksArePoorlyBreakable baseOk rest)
  | _ :: rest => linksArePoorlyBreakable baseOk rest

/-- Whether `e` is a chain of member accesses and calls whose calls have
no argument, or one short argument. -/
def isPoorlyBreakableChain : Bool → MiniExpr → Bool
  -- the callee is read through, whatever it is: a member access, a
  -- parenthesised optional chain, or a call of its own
  | _, .call f targs args =>
      argumentsAreShort args && !tsTypeArgsAreComplex targs && isPoorlyBreakableChain true f
  | _, .dot o _ | _, .privateDot o _ | _, .index o _ => isPoorlyBreakableChain true o
  -- a `!` is one of the links of the chain prettier reads, and is read
  -- through here: `a.b!.c.d` is as poorly breakable as `a.b.c.d`
  | deep, .nonNull o => isPoorlyBreakableChain deep o
  | _, .chain base ⟨hd, tl⟩ =>
      linksArePoorlyBreakable (isPoorlyBreakableChain true base) (hd :: tl).reverse
  | deep, .ident _ => deep
  | deep, .this => deep
  | _, _ => false

/-- Whether a quoted property name can be written without its quotes: it
is one exactly when it is an ECMAScript 5 `IdentifierName`, whose
characters are those of the Unicode properties `ID_Start` and
`ID_Continue`. -/
def isIdentifierName (s : String) : Bool := Unicode.isIdentifierName s

/-- The literal a string of the shape `123` or `2.5` denotes; `none` for a
string of any other shape. -/
def simpleNumberOf (s : String) : Option JSNumber :=
  match s.splitOn "." with
  | [a] =>
      if a.length > 0 && a.all Char.isDigit then a.toNat?.map (fun m => .decimal m 0)
      else none
  | [a, b] =>
      if a.length > 0 && b.length > 0 && a.all Char.isDigit && b.all Char.isDigit then
        (a ++ b).toNat?.map (fun m => .decimal m (-(Int.ofNat b.length)))
      else none
  | _ => none

/-- Whether the string is a plain decimal number, as `123` or `2.5`, which
is moreover written the way JavaScript writes the number it denotes.  A
property name may lose its quotes only then: the name `01` is not the name
`1`, and the number `01` denotes is written `1`.  A number of more than
fifteen digits is left alone, since the double it rounds to may well be
written differently. -/
def isSimpleNumberString (s : String) : Bool :=
  match simpleNumberOf s with
  | none => false
  | some n =>
      n.render == s &&
        (match n.normalize with
          | .decimal m _ => (JSNumber.digitsOf 10 m).length ≤ 15
          | _ => false)

/-- Whether a property name has to keep its quotes: it is a string that is
neither an identifier name nor the plain spelling of the number it
denotes.  Under `quoteProps: "consistent"` one such name among the
properties of an object, of a class, of a type or of an enum quotes them
all. -/
def keyNeedsQuotes : MiniPropertyName → Bool
  | .string v => !isIdentifierName v && !isSimpleNumberString v
  | _ => false

/-- Whether every name of a list of property names is written quoted:
`quoteProps: "consistent"` and one of them that cannot lose its
quotes. -/
def quoteAllKeys (keys : List MiniPropertyName) : Bool :=
  Options.quoteProps == .consistent && keys.any keyNeedsQuotes

/-- The names of the properties of an object literal. -/
def propertyKeys : List MiniProperty → List MiniPropertyName
  | [] => []
  | .keyValue k _ :: rest | .method _ k _ _ _ _ :: rest => k :: propertyKeys rest
  | _ :: rest => propertyKeys rest

/-- Whether the properties of an object literal are all written quoted. -/
def quoteAllProps (props : List MiniProperty) : Bool := quoteAllKeys (propertyKeys props)

/-- The names of the members of a class. -/
def classElemKeys : List MiniClassElement → List MiniPropertyName
  | [] => []
  | .method _ _ _ k _ _ _ _ _ :: rest | .field _ _ _ k _ _ _ _ :: rest => k :: classElemKeys rest
  | _ :: rest => classElemKeys rest

/-- Whether the members of a class are all written quoted. -/
def quoteAllMembers (body : List MiniClassElement) : Bool := quoteAllKeys (classElemKeys body)

/-- The names bound by an object pattern. -/
def objectPatternKeys : List MiniObjectPatternProp → List MiniPropertyName
  | [] => []
  | ⟨key, _⟩ :: rest => key :: objectPatternKeys rest

/-- Whether the names bound by an object pattern are all written
quoted. -/
def quoteAllPatternKeys (props : List MiniObjectPatternProp) : Bool :=
  quoteAllKeys (objectPatternKeys props)

/-- The names of the members of an interface or of an object type. -/
def tsTypeMemberKeys : List MiniTsTypeMember → List MiniPropertyName
  | [] => []
  | .property _ k _ _ :: rest | .method _ k _ _ _ _ :: rest => k :: tsTypeMemberKeys rest
  | _ :: rest => tsTypeMemberKeys rest

/-- Whether the members of an interface or of an object type are all
written quoted. -/
def quoteAllTypeMembers (members : List MiniTsTypeMember) : Bool :=
  quoteAllKeys (tsTypeMemberKeys members)

/-- The names of the members of an enum. -/
def tsEnumMemberKeys : List MiniTsEnumMember → List MiniPropertyName
  | [] => []
  | m :: rest => m.key :: tsEnumMemberKeys rest

/-- Whether the members of an enum are all written quoted. -/
def quoteAllEnumMembers (members : List MiniTsEnumMember) : Bool :=
  quoteAllKeys (tsEnumMemberKeys members)

/-! ## Semicolons -/

/-- Whether the name is one of `static`, `get` and `set` written as a
plain identifier: a field of that name, with neither a value nor a type
annotation, keeps its semicolon under `semi: false`, since the line that
follows it would otherwise be read as its value. -/
def keyIsStaticGetSet : MiniPropertyName → Bool
  | .ident n => n.val == "static" || n.val == "get" || n.val == "set"
  | _ => false

/-- Whether the name is `in` or `instanceof`, which a member written after
a field would be read as an operator of. -/
def keyIsInOrInstanceof : MiniPropertyName → Bool
  | .ident n => n.val == "in" || n.val == "instanceof"
  | _ => false

/-- Whether the name is a computed one, `[e]`. -/
def keyIsComputed : MiniPropertyName → Bool
  | .computed _ => true
  | _ => false

/-- Whether the modifiers of a member make prettier leave the field in
front of it without its semicolon: a member written `static`, `readonly`
or with an accessibility modifier is one prettier never reads a field
on into. -/
def modsStopReading (m : TsMemberMods) : Bool :=
  m.isStatic || m.isReadonly || m.accessibility.isSome

/-- Under `semi: false`, whether the member written after a field would be
read as part of that field, so that the field keeps its semicolon: it is
prettier's `shouldPrintSemicolonAfterClassProperty`. -/
def memberFollowsField : Option MiniClassElement → Bool
  | none => false
  | some (.staticBlock _) => false
  -- an index signature begins with a `[`, which a field is read on
  -- into, just as a computed name is
  | some (.indexSig mods ..) => !modsStopReading mods
  -- an `accessor` field is not one prettier reads a computed name as
  -- the continuation of: only the `in` and `instanceof` rule applies
  | some (.field _ mods isAccessor key ..) =>
      !modsStopReading mods
        && (keyIsInOrInstanceof key || (!isAccessor && keyIsComputed key))
  | some (.method _ mods kind key ..) =>
      !modsStopReading mods
        && (keyIsInOrInstanceof key
            || (match kind with
                | .get | .set | .async | .asyncGenerator => false
                | .generator => true
                | .normal => keyIsComputed key))

/-- The semicolon written after a class field: always under `semi: true`,
and under `semi: false` only where a parser would otherwise read on. -/
def fieldSemiDoc (key : MiniPropertyName) (type : Option MiniTsType)
    (init : Option MiniExpr) (next : Option MiniClassElement) : Doc :=
  if Options.semi then t ";"
  else if init.isNone && type.isNone && keyIsStaticGetSet key then t ";"
  else if memberFollowsField next then t ";"
  else .nil

/-- Whether the parameters of an arrow function are written without their
parentheses: `arrowParens: "avoid"`, and one parameter which is a plain
name -- not a rest element, a pattern, a name with a default value, an
optional one or one that carries a type annotation, a decorator or a
modifier.  An arrow that is written with type parameters or with a return
type keeps its parentheses whatever its parameter is. -/
def arrowParensAvoided (typeParams : List MiniTsTypeParam) (params : List MiniParam)
    (retType : Option MiniTsType) : Bool :=
  Options.arrowParens == .avoid && typeParams.isEmpty && retType.isNone &&
    match params with
    | [.plain decorators mods (.ident _) false none] => decorators.isEmpty && mods.isEmpty
    | _ => false

/-- Whether a character is one a parser reads as the continuation of the
statement before it, so that a statement beginning with it takes a
semicolon of its own under `semi: false`. -/
def isASIHazardChar (c : Char) : Bool :=
  c == '(' || c == '[' || c == '`' || c == '+' || c == '-' || c == '/' || c == '<'

/-- Whether the leftmost token of the expression is a prefix `++` or `--`.
Prettier reads such a statement as one that needs no semicolon in front of
it, although it begins with `+` or `-`. -/
def startsWithPrefixUpdate : MiniExpr → Bool
  | .unary .preIncr _ | .unary .preDecr _ => true
  | .binary l _ _ | .seq l _ | .assign l _ _ => startsWithPrefixUpdate l
  | .dot o _ | .privateDot o _ | .index o _ | .chain o _ => startsWithPrefixUpdate o
  | .asExpr e _ | .satisfies e _ | .nonNull e | .instantiation e _ => startsWithPrefixUpdate e
  | _ => false

/-- Whether the leftmost token of the expression is that of an arrow
function whose parameters prettier writes between parentheses.  Such a
statement is one prettier guards under `semi: false`, even where the
arrow is written `async` first and so does not itself begin with `(`. -/
def startsWithParenArrow : MiniExpr → Bool
  | .arrow _ typeParams params retType _ => !arrowParensAvoided typeParams params retType
  | .binary l _ _ | .seq l _ | .assign l _ _ => startsWithParenArrow l
  | .dot o _ | .privateDot o _ | .index o _ | .chain o _ => startsWithParenArrow o
  | .call f _ _ => startsWithParenArrow f
  | .postfix e _ => startsWithParenArrow e
  | .ternary c _ _ => startsWithParenArrow c
  | .template (some tag) _ _ _ => startsWithParenArrow tag
  | .asExpr e _ | .satisfies e _ | .nonNull e | .instantiation e _ => startsWithParenArrow e
  | _ => false

/-- Under `semi: false`, the semicolon prettier writes in front of an
expression statement of a statement list whose first token would
otherwise continue the statement before it. -/
def asiGuard (s : MiniStatement) (d : Doc) : Doc :=
  if Options.semi then d
  else
    match s with
    | .expr e =>
        if startsWithParenArrow e then t ";" ++ d
        else
          match Doc.firstFlatChar d with
          | some c =>
              if isASIHazardChar c
                  && !((c == '+' || c == '-') && startsWithPrefixUpdate e) then
                t ";" ++ d
              else d
          | none => d
    | _ => d

/-! ## Layout helpers -/

/-- A bracketed, comma separated list.  `spaced` says that the list is one
whose brackets prettier's `bracketSpacing` puts a space inside, and
`comma` which of prettier's `trailingComma` settings write a comma after
its last item. -/
def sepList (opener closer : String) (spaced : Bool) (comma : CommaKind)
    (items : List Doc) : Doc :=
  if items.isEmpty then t (opener ++ closer)
  else
    let br : Doc := if spaced && Options.bracketSpacing then .line else .softline
    let trailer : Doc := if Options.hasTrailingComma comma then .ifBreak (t ",") .nil else .nil
    .group (t opener ++ .nest indentWidth (br ++ Doc.joinWith (t "," ++ .line) items ++ trailer)
      ++ br ++ t closer)

/-- A bracketed, comma separated list that is not wrapped in a group of
its own: it breaks together with the group that encloses it. -/
def sepListOpen (opener closer : String) (spaced : Bool) (comma : CommaKind)
    (items : List Doc) : Doc :=
  if items.isEmpty then t (opener ++ closer)
  else
    let br : Doc := if spaced && Options.bracketSpacing then .line else .softline
    let trailer : Doc := if Options.hasTrailingComma comma then .ifBreak (t ",") .nil else .nil
    t opener ++ .nest indentWidth (br ++ Doc.joinWith (t "," ++ .line) items ++ trailer)
      ++ br ++ t closer

/-- A bracketed, comma separated list that is always broken. -/
def sepListBroken (opener closer : String) (spaced : Bool) (comma : CommaKind)
    (items : List Doc) : Doc :=
  if items.isEmpty then t (opener ++ closer)
  else
    let br : Doc := if spaced && Options.bracketSpacing then .line else .softline
    let trailer : Doc := if Options.hasTrailingComma comma then t "," else .nil
    .groupBreak (t opener ++ .nest indentWidth (br ++ Doc.joinWith (t "," ++ .line) items ++ trailer)
      ++ br ++ t closer)

/-- The argument list of a call, hugging a first or a final function-like
argument the way prettier does.  `docs` are the arguments as they are
printed on their own, `hugFirstDocs` and `hugDocs` the same arguments with
the first, respectively the last, one printed as the layout prints an
argument it expands in place.  `openArgs` says that the call is a link of
a long curried chain, `f(a, b)(c)`, whose argument list prettier leaves
ungrouped: it then breaks together with the line that holds the call. -/
def argumentsDocOf (comma : CommaKind) (openArgs : Bool) (hookDeps forceBroken hugFirst canHug : Bool)
    (docs hugFirstDocs hugDocs : List Doc) : Doc :=
  match docs with
  | [] => t "()"
  | _ =>
    let allBroken := sepListBroken "(" ")" false comma docs
    -- `useEffect(() => { ... }, [a, b])` keeps the layout it is written in
    if hookDeps then t "(" ++ Doc.joinWith (t ", ") docs ++ t ")"
    else if forceBroken then allBroken
    else if hugFirst then
      let firstDoc := hugFirstDocs.headD Doc.nil
      let tailDocs := hugFirstDocs.drop 1
      if tailDocs.any Doc.hasForcedBreak then allBroken
      else
        let tail := Doc.concat (tailDocs.map (fun d => t ", " ++ d))
        let hug := t "(" ++ firstDoc ++ tail ++ t ")"
        let hugBroken := t "(" ++ .groupBreak firstDoc ++ tail ++ t ")"
        if Doc.hasForcedBreak firstDoc then
          .breakParent ++ .condGroup hugBroken allBroken
        else
          .condGroup hug (.condGroup hugBroken allBroken)
    else if !canHug then
      if openArgs then sepListOpen "(" ")" false comma docs
      else
        let shouldBreak := docs.any Doc.hasForcedBreak
        if shouldBreak then allBroken else sepList "(" ")" false comma docs
    else
      let headDocs := hugDocs.dropLast
      let lastDoc := hugDocs.getLastD Doc.nil
      if headDocs.any Doc.hasForcedBreak then allBroken
      else
        let head := Doc.concat (headDocs.map (fun d => d ++ t ", "))
        let hug := t "(" ++ head ++ lastDoc ++ t ")"
        let hugBroken := t "(" ++ head ++ .groupBreak lastDoc ++ t ")"
        if Doc.hasForcedBreak lastDoc then
          .breakParent ++ .condGroup hugBroken allBroken
        else
          .condGroup hug (.condGroup hugBroken allBroken)

/-- The argument list of an ordinary call, which gets a trailing comma
when it is broken over several lines. -/
def argumentsDoc : Bool → Bool → Bool → Bool → List Doc → List Doc → List Doc → Doc :=
  argumentsDocOf .all false

/-- The argument list of an ordinary call, which is left ungrouped when
the call is a link of a long curried chain. -/
def argumentsDocMaybeOpen (openArgs : Bool) :
    Bool → Bool → Bool → Bool → List Doc → List Doc → List Doc → Doc :=
  argumentsDocOf .all openArgs

/-- Whether a parameter is one prettier writes out between the
parentheses of the function, as in `function ({\n  a,\n}) {}`: it
destructures an object or an array, possibly with a plain default value.
It is hugged only when it is the one parameter of the function. -/
def shouldHugParameter (p : MiniPattern) (type : Option MiniTsType) : Bool :=
  let rec destructures : MiniPattern → Bool
    | .object .. | .array .. => true
    | _ => false
  -- an identifier whose type annotation is an object type is hugged too
  let objectTyped :=
    (match p with | .ident _ => true | _ => false) &&
      (match type with
        | some (.objectType _) => true
        | some (.mapped ..) => true
        | _ => false)
  objectTyped ||
  match p with
  | .withDefault q v =>
      destructures q &&
        (match v with
          | .ident _ => true
          | .object [] => true
          | .array [] => true
          | _ => false)
  | q => destructures q

/-- Whether the only parameter of a function is one prettier writes out
between the parentheses of the function.  A parameter property, which is
written with modifiers of its own, is never hugged: its parameter list
stands open instead. -/
def shouldHugTheOnlyParameter : List MiniParam → Bool
  | [.plain [] mods p _ type] => mods.isEmpty && shouldHugParameter p type
  | _ => false

/-- A parameter list.  `hug` says that the list is the one object or array
pattern prettier writes out between the parentheses of the function. -/
def paramsDocOf (hug restLast : Bool) (items : List Doc) : Doc :=
  if hug then t "(" ++ Doc.concat items ++ t ")"
  else sepList "(" ")" false (if restLast then .never else .all) items

/-- A brace enclosed statement list.  An empty body is written `{}` only
where prettier does so: in a function, a loop, or a `static` block. -/
def blockDocOf (collapseEmpty : Bool) (isEmpty : Bool) (inner : Doc) : Doc :=
  if isEmpty then
    if collapseEmpty then t "{}" else t "{" ++ .hardline ++ t "}"
  else t "{" ++ .nest indentWidth (.hardline ++ inner) ++ .hardline ++ t "}"

/-- Whether the statement can end with an `if` that has no `else`, so that
an `else` written after it would be read as belonging to that `if`. -/
def endsWithDanglingIf : MiniStatement → Bool
  | .if_ _ _ none => true
  | .if_ _ _ (some e) => endsWithDanglingIf e
  | .while_ _ b | .with_ _ b | .labelled _ b => endsWithDanglingIf b
  | .for_ _ _ _ b | .forIn _ _ b | .forOf _ _ _ b => endsWithDanglingIf b
  | _ => false

/-- The body attached to the head of an `if`, a loop or a `with`. -/
def clauseDoc (isBlock isEmptyStatement : Bool) (d : Doc) : Doc :=
  if isEmptyStatement then t ";"
  else if isBlock then t " " ++ d
  else .nest indentWidth (.line ++ d)

/-! ## Member chains -/

/-- What one element of a member chain is. -/
inductive ChainKind where
  | base | dot | index | call
  /-- The `!` of a non-null assertion written on an element of the chain,
  which prettier reads as an element of its own. -/
  | nonNull
deriving BEq, Inhabited

/-- One element of a member chain, together with what the layout
heuristics need to know about it. -/
structure ChainItem where
  /-- The kind of the element. -/
  kind : ChainKind
  /-- Its document. -/
  doc : Doc
  /-- For an index: whether the property is a number. -/
  numericIndex : Bool := false
  /-- For a `.name` access: the name. -/
  name : String := ""
  /-- For the base: whether it is `this`. -/
  isThis : Bool := false
  /-- For the base: its name, if it is an identifier. -/
  identName : String := ""
  /-- For the base: whether it is a call. -/
  isCallBase : Bool := false
  /-- For a call: whether all of its arguments are simple. -/
  simpleArgs : Bool := true
  /-- For a call: whether one of its arguments is a function. -/
  functionArg : Bool := false
  /-- For a call, or a base that is one: whether it has an argument. -/
  hasArgs : Bool := false
deriving Inhabited

/-- Whether the element continues a member chain, rather than ending it. -/
def ChainItem.isMemberish (i : ChainItem) : Bool := i.kind == .dot || i.kind == .index

/-- The `!` of a non-null assertion, as an element of a chain. -/
def nonNullItem : ChainItem := { kind := .nonNull, doc := Doc.text "!" }

/-- The index, if there is one, of the last call of the chain whose callee
carries a `!`, that is, of the last call written right after a `!`. -/
def lastNonNullCall (items : List ChainItem) : Option Nat :=
  let rec go (idx : Nat) (prevNonNull : Bool) (found : Option Nat) :
      List ChainItem → Option Nat
    | [] => found
    | i :: rest =>
        go (idx + 1) (i.kind == .nonNull)
          (if prevNonNull && i.kind == .call then some idx else found) rest
  go 0 false none items

/-- The head of a chain that is collapsed at a call written on a `!`,
written as the ordinary expression printer writes it: a name access reads
through an identifier on the line it stands on, and every other one may
take a line of its own. -/
def nonNullHeadDoc : List ChainItem → Doc
  | [] => .nil
  | base :: rest => go base.doc (base.identName != "") false rest
where
  go (acc : Doc) (objIsIdent seenCall : Bool) : List ChainItem → Doc
    | [] => acc
    | i :: rest =>
        if i.kind == .dot then
          let inline := objIsIdent && !seenCall
          go (acc ++ (if inline then i.doc
                else .group (.nest indentWidth (.softline ++ i.doc)))) false seenCall rest
        else go (acc ++ i.doc) false (seenCall || i.kind == .call) rest

/-- Collapse the head of a chain at the last call written on a `!`.
Prettier reads a member chain out of the outermost call whose callee is a
member access: a call whose callee is a non-null assertion, `a.b!()`, is
not one, so the chain starts above it and everything up to and including
it is the head the chain is read from, written as it is written anywhere
else. -/
def collapseNonNullHead (items : List ChainItem) : List ChainItem :=
  match lastNonNullCall items with
  | none => items
  | some k =>
    let head := items.take (k + 1)
    let rest := items.drop (k + 1)
    if rest.isEmpty then items
    else
      match head.getLast? with
      | none => items
      | some call =>
        { kind := .base, doc := nonNullHeadDoc head, isCallBase := true,
          simpleArgs := call.simpleArgs, functionArg := call.functionArg,
          hasArgs := call.hasArgs } :: rest

/-- A `.` or `[]` access. -/
def isMemberish : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. => true
  | _ => false

/-- Whether the first token of the expression is the `{` of an object
literal, so that the expression has to be parenthesised where a statement,
or the body of an arrow function, may not start with one. -/
def startsWithObjectLiteral : MiniExpr → Bool
  | .object _ => true
  | .call (.func ..) _ _ => false
  | .template (some (.func ..)) _ _ _ => false
  | .binary l _ _ | .assign l _ _ | .seq l _ => startsWithObjectLiteral l
  | .dot o _ | .privateDot o _ | .index o _ | .chain o _ | .postfix o _ =>
      startsWithObjectLiteral o
  | .call f _ _ => startsWithObjectLiteral f
  | .ternary c _ _ => startsWithObjectLiteral c
  | .template (some tag) _ _ _ => startsWithObjectLiteral tag
  | _ => false

/-- A conditional expression that does not start with an object literal.
Prettier keeps one on the line of the `=>` of an arrow function, and puts
parentheses around it when it stays on that line. -/
def isPlainConditional : MiniExpr → Bool
  | .ternary c _ _ => !startsWithObjectLiteral c
  | _ => false

/-- Whether the expression is a JSX element or fragment. -/
def isJsxExpr : MiniExpr → Bool
  | .jsx _ => true
  | _ => false

/-- Whether the expression is a conditional expression. -/
def consIsTernaryOf : MiniExpr → Bool
  | .ternary .. => true
  | _ => false

/-- Whether the chain of conditionals rooted at the expression holds a JSX
element in one of its tests or branches.  Prettier lays such a chain out
the way it lays JSX out. -/
def ternaryChainHasJsx : MiniExpr → Bool
  | .ternary c a b =>
      isJsxExpr c || isJsxExpr a || isJsxExpr b
        || ternaryChainHasJsx c || ternaryChainHasJsx a || ternaryChainHasJsx b
  | _ => false

/-! ## Conditional expressions under `experimentalTernaries`

Prettier's experimental layout of a conditional writes the `?` at the end
of the line of the test and the `:` in front of the alternate, and lays a
chain of conditionals out as a list of cases.  The helpers here are the
ones its rules ask about: how many nodes the test is made of, and whether
the consequent is a short expression.
-/

mutual

/-- The number of nodes the TypeScript syntax tree of the expression
holds, counted the way prettier's `getNodeContentCount` counts them: the
properties of a node which are nodes themselves, recursively, and not the
ones which are lists of nodes. -/
def babelNodeCount : MiniExpr → Nat
  | .ident _ | .number _ | .string _ | .regex _ | .null | .true_ | .false_
  | .this | .privateName _ => 0
  -- `new.target` and `import.meta` hold the two names they are made of
  | .newTarget | .importMeta => 2
  -- a list of nodes is not read: the elements of an array, the properties
  -- of an object, the operands of the comma operator and the arguments of
  -- a call are not counted
  | .array _ | .object _ | .seq _ _ => 0
  | .superDot _ => 2
  | .superIndex i => 2 + babelNodeCount i
  | .superCall _ => 1
  | .assign l _ r => 2 + babelNodeCount l + babelNodeCount r
  | .assignPattern _ r => 2 + babelNodeCount r
  | .await e | .unary _ e | .postfix e _ | .spread e | .yieldFrom e | .nonNull e =>
      1 + babelNodeCount e
  | .yield none => 0
  | .yield (some e) => 1 + babelNodeCount e
  | .call f targs _ | .new f targs _ =>
      1 + babelNodeCount f + (if targs.isEmpty then 0 else 1 + tsTypeListCount targs)
  | .instantiation e targs => 1 + babelNodeCount e + (if targs.isEmpty then 0 else 1 + tsTypeListCount targs)
  | .asExpr e ty | .satisfies e ty => 2 + babelNodeCount e + tsTypeCount ty
  | .importCall spec opts =>
      1 + babelNodeCount spec
        + (match opts with | some o => 1 + babelNodeCount o | none => 0)
  | .dot o _ | .privateDot o _ => 2 + babelNodeCount o
  | .index o i => 2 + babelNodeCount o + babelNodeCount i
  -- an optional chain is read into a chain expression of its own
  | .chain b links => 1 + babelNodeCount b + babelChainLinksCount (links.hd :: links.tl)
  | .classExpr _ name typeParams heritage _ _ =>
      1 + (if name.isSome then 1 else 0) + (if typeParams.isEmpty then 0 else 1)
        + (match heritage with | some _ => 1 | none => 0)
  | .func _ _ name typeParams _ ret _ =>
      1 + (if name.isSome then 1 else 0) + (if typeParams.isEmpty then 0 else 1)
        + (match ret with | some ty => 1 + tsTypeCount ty | none => 0)
  | .arrow _ typeParams _ ret body =>
      1 + (if typeParams.isEmpty then 0 else 1)
        + (match ret with | some ty => 1 + tsTypeCount ty | none => 0)
        + (match body with | .expr e => babelNodeCount e | .block _ => 0)
  | .binary l _ r => 2 + babelNodeCount l + babelNodeCount r
  | .ternary c a b => 3 + babelNodeCount c + babelNodeCount a + babelNodeCount b
  | .template none _ _ _ => 0
  | .template (some tag) targs _ _ => 2 + babelNodeCount tag + (if targs.isEmpty then 0 else 1 + tsTypeListCount targs)
  -- an element holds its opening element, and its closing one where it
  -- has children; each of them holds its name
  | .jsx (.element _ _ _ children) => if children.isSome then 4 else 2
  | .jsx (.fragment _) => 2
termination_by e => sizeOf e
decreasing_by
  all_goals try (obtain ⟨hd, tl⟩ := links)
  all_goals simp +arith
  all_goals omega

/-- The nodes the links of an optional chain hold. -/
def babelChainLinksCount : List MiniChainLink → Nat
  | [] => 0
  | l :: rest =>
      (match l with
        | .dot _ _ | .privateDot _ _ => 2
        | .index _ i => 2 + babelNodeCount i
        | .call _ targs _ => 1 + (if targs.isEmpty then 0 else 1 + tsTypeListCount targs)
        | .nonNull => 1)
      + babelChainLinksCount rest
termination_by ls => sizeOf ls

/-- The nodes the types of a list hold. -/
def tsTypeListCount : List MiniTsType → Nat
  | [] => 0
  | ty :: rest => tsTypeCount ty + tsTypeListCount rest
termination_by ls => sizeOf ls

/-- The nodes a type holds, counted as the nodes of an expression are. -/
def tsTypeCount : MiniTsType → Nat
  | .ref name args => tsEntityNameCount name + (if args.isEmpty then 0 else 1 + tsTypeListCount args)
  | .this | .uniqueSymbol => 0
  | .strLit _ | .numLit _ => 1
  | .negNumLit _ => 2
  | .array e | .keyof e | .readonlyOp e => 1 + tsTypeCount e
  | .indexed o i => 2 + tsTypeCount o + tsTypeCount i
  | .union _ | .intersection _ | .objectType _ | .tuple _ | .templateLit _ _ => 0
  | .fn typeParams _ ret =>
      1 + tsTypeCount ret + (if typeParams.isEmpty then 0 else 1)
  | .ctor _ typeParams _ ret =>
      1 + tsTypeCount ret + (if typeParams.isEmpty then 0 else 1)
  | .typeQuery name args => tsEntityNameCount name + (if args.isEmpty then 0 else 1 + tsTypeListCount args)
  | .infer_ _ constraint =>
      1 + 1 + (match constraint with | some c => tsTypeCount c | none => 0)
  | .conditional c e a b => 4 + tsTypeCount c + tsTypeCount e + tsTypeCount a + tsTypeCount b
  | .mapped _ _ constraint as_ _ value =>
      2 + tsTypeCount constraint
        + (match as_ with | some ty => tsTypeCount ty | none => 0)
        + (match value with | some ty => tsTypeCount ty | none => 0)
  | .importType _ _ _ qualifier args =>
      1 + (match qualifier with | some n => tsEntityNameCount n | none => 0)
        + (if args.isEmpty then 0 else 1 + tsTypeListCount args)
  | .predicate _ _ ty =>
      1 + (match ty with | some t => 1 + tsTypeCount t | none => 0)
termination_by ty => sizeOf ty

/-- The nodes a qualified name holds: one for each name of it. -/
def tsEntityNameCount : TsEntityName → Nat
  | .ident _ => 1
  | .qualified left _ => 2 + tsEntityNameCount left
termination_by n => sizeOf n

end

/-- Whether the expression is made of few enough nodes: prettier's
`isSmallNode`, which its experimental layout of a conditional asks of the
test. -/
def isSmallNode (limit : Nat) (e : MiniExpr) : Bool := babelNodeCount e ≤ limit

/-- Whether the expression is one prettier counts as short for its width:
`isSimpleExpressionByWidth`, which measures the text of a name, of a
string or of a regular expression against a quarter of the print width.
Its experimental layout of a conditional asks it of the consequent. -/
def isShortExpr : MiniExpr → Bool
  | .this => true
  | .ident n => 4 * n.val.length ≤ Options.printWidth
  -- a signed numeric literal is short whatever it holds
  | .unary .plus (.number _) | .unary .minus (.number _) => true
  | .regex r => 4 * r.source.val.length ≤ Options.printWidth
  | .string v => 4 * (strLit v).length ≤ Options.printWidth
  | .template none [] head [] =>
      4 * head.length ≤ Options.printWidth && !head.contains '\n'
  -- `++x` and `--x` are updates, not unary operators, and are not short
  | .unary .preIncr _ | .unary .preDecr _ => false
  | .unary _ e => isShortExpr e
  | .call (.ident n) [] [] => 4 * n.val.length + 8 ≤ Options.printWidth
  | e => isLiteralExpr e

/-- Whether the expression is `null` or `undefined`.  A branch of a
conditional laid out for JSX which is one takes no parentheses. -/
def isNilExpr : MiniExpr → Bool
  | .null => true
  | .ident n => n.val == "undefined"
  | _ => false

/-- Whether prettier keeps the body of an arrow function on the line of
its `=>`.  A chain of arrow functions that is always broken does not keep
a conditional body on that line. -/
def keepsArrowBodyOnLine (breakChain : Bool) : MiniExpr → Bool
  | .object _ | .array _ | .arrow .. => true
  | .jsx _ => true
  | .seq _ _ => true
  | e => !breakChain && isPlainConditional e

/-- The parameter lists of the arrow functions of a chain, and the body at
the end of the chain. -/
def arrowChainParts (params : List MiniParam) :
    MiniArrowBody → List (List MiniParam) × MiniArrowBody
  | .expr (.arrow _ _ ps _ b) =>
      let (rest, body) := arrowChainParts ps b
      (params :: rest, body)
  | b => ([params], b)

/-- Whether the parameter is a plain identifier.  Prettier always breaks a
chain of arrow functions one of whose parameters is not one. -/
def paramIsPlainIdent : MiniParam → Bool
  | .plain [] mods (.ident _) isOptional type =>
      mods.isEmpty && !isOptional && type.isNone
  | _ => false

/-- Whether prettier keeps the body of a chain of arrow functions on the
line of the last `=>` of the chain. -/
def arrowBodyStaysOnLine (breakChain : Bool) : MiniArrowBody → Bool
  | .block _ => true
  | .expr e => keepsArrowBodyOnLine breakChain e

/-- What the body of an arrow function is the start of: an object literal
written there needs parentheses, unless the body is a sequence expression
or an assignment, which is parenthesised as a whole anyway. -/
def arrowBodyStart : MiniExpr → StartCtx
  | .seq _ _ | .assign .. => .none
  | _ => .arrowBody

/-- The same, for the body of an arrow function which is the argument of a
call written directly in a `{ }` of a JSX element: a JSX element there
stands on lines of its own, and an object literal needs parentheses
unless the body is parenthesised as a whole anyway. -/
def jsxArrowBodyStart : MiniExpr → StartCtx
  | .seq _ _ | .assign .. => .none
  | _ => .jsxArrowBody

/-- Whether the body of the arrow function is a chain of further arrow
functions, which prettier lays out as one unit. -/
def isArrowChainBody : MiniArrowBody → Bool
  | .expr (.arrow ..) => true
  | _ => false

/-- Whether the position is an argument of a call, or an operand of a
binary operator, where prettier indents the tail of a chain of arrow
functions. -/
def indentsArrowChainTail : Pos → Bool
  | .callArg | .hugArg .. => true
  | .binOperand .. => true
  | _ => false

/-- Whether the position is one where prettier lets a chain of arrow
functions start on a line of its own. -/
def breaksBeforeArrowChain : Pos → Bool
  | .callee .. | .assignRhs .. | .propValue .. => true
  | _ => false

/-- Whether the assignment the chain of arrow functions is the right hand
side of is the tail of a chain of assignments, which always breaks the
signatures of the chain. -/
def breaksArrowChainSignatures : Pos → Bool
  | .assignRhs _ _ _ b => b
  | _ => false

/-- The body of an arrow function that is an expression, with the space or
the line in front of it, given the document of the expression.  `chained`
says whether the arrow function is part of a chain of arrow functions,
whose body the chain lays out itself.  `hugged` says that the arrow
function is the argument of a call that the layout expands in place, where
a body that leaves the line of the `=>` takes the trailing comma of the
argument list with it and the closing parenthesis of the call keeps its
own line.  `jsxParent` says that the arrow function is written straight
inside a `{ }` of a JSX element, which likewise leaves the closing brace
its own line once the body leaves the line of the `=>`. -/
def arrowExprBodyOf (chained breakChain hugged jsxParent : Bool) (e : MiniExpr) (d : Doc) : Doc :=
  let trailer : Doc :=
    (if hugged && Options.hasTrailingComma .all then .ifBreak (t ",") .nil else .nil)
      ++ (if hugged || jsxParent then .softline else .nil)
  if !breakChain && isPlainConditional e then
    -- a conditional body keeps the line of the `=>`, in parentheses while
    -- it fits on it
    t " " ++ .group (.ifBreak .nil (t "(") ++ .nest indentWidth (.softline ++ d)
      ++ .ifBreak .nil (t ")") ++ trailer)
  else if keepsArrowBodyOnLine breakChain e then t " " ++ d
  else if chained then .nest indentWidth (.line ++ d) ++ trailer
  else .group (.nest indentWidth (.line ++ d) ++ trailer)

/-- The layout of an arrow function, or of a chain of them, given the
documents of its signatures and the document of its body, the space or the
line in front of the body included. -/
def arrowLayoutOf (pos : Pos) (breakChain bodyOnSameLine : Bool)
    (sigDocs : List Doc) (bodyPart : Doc) : Doc :=
  match sigDocs with
  | [] => bodyPart
  | [sig] => .group (sig ++ t " =>" ++ bodyPart)
  | sig :: rest =>
    let arrowSep : Doc := t " =>" ++ .line
    let grp (d : Doc) : Doc := if breakChain then .groupBreak d else .group d
    let sigsDoc : Doc :=
      if indentsArrowChainTail pos then
        grp (sig ++ t " =>" ++ .nest indentWidth (.line ++ Doc.joinWith arrowSep rest))
      else if breaksBeforeArrowChain pos then grp (Doc.joinWith arrowSep sigDocs)
      else grp (.nest indentWidth (Doc.joinWith arrowSep sigDocs))
    let isCallee := isCalleePos pos
    let head : Doc :=
      if breaksBeforeArrowChain pos then
        (if (isCallee && !bodyOnSameLine) || breaksArrowChainSignatures pos then
            Doc.breakParent
          else .nil)
          ++ .nest indentWidth (.softline ++ sigsDoc)
      else sigsDoc
    .group (.groupIndentIfBreak indentWidth (head ++ t " =>") bodyPart
      (if isCallee then .softline else .nil))

/-- Whether the node is part of the spine of a member chain. -/
def isChainNode : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. => true
  | .call f _ _ => isChainNode f
  | _ => false

/-- Whether the node is one whose elements a member chain is made of,
rather than the base the chain starts from.  A call belongs to the chain
only when its callee does: `f().a.b` starts from the whole `f()`, whereas
`a.b().c` starts from `a`. -/
def isChainSpine : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. | .chain .. => true
  | .call f _ _ => isChainNode f || (match f with | .call .. => true | _ => false)
  | _ => false

/-- Whether the chain reads through the node when it stands as the object
of an access, or as the base of an optional chain.  A `!` is an element of
the chain, so the chain goes on into the expression it is written on; a
call whose callee is a `!` is not, which is what makes the chain start
above such a call. -/
def isChainNodeObject : MiniExpr → Bool
  | .nonNull _ => true
  | e => isChainNode e

/-- Whether the chain reads through the node when it stands as the object
of an access: as `isChainNodeObject`, for the elements that carry their
documents. -/
def isChainSpineObject : MiniExpr → Bool
  | .nonNull _ => true
  | e => isChainSpine e

/-- Whether the node is read through by the member chain layout: a member
access is, and so is a call whose callee is a member access or a call
itself, which is how prettier takes a curried call, `f(a, b)(c)`, into the
chain that holds it. -/
def isChainSpineNode : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. => true
  | .call f _ _ => isMemberish f || isCallLikeExpr f
  | _ => false

/-- Whether the chain reads through the node when it stands as the object
of an access: as `isChainSpineNode`, and a `!` as well. -/
def isChainSpineNodeObject : MiniExpr → Bool
  | .nonNull _ => true
  | e => isChainSpineNode e

/-- Split the elements of a chain into the groups prettier lays out, one
per line when the chain breaks. -/
private def chainGroups (baseIsCall : Bool) : List ChainItem → List (List ChainItem)
  | [] => [[]]
  | items =>
    let (first, rest) := takeFirst items
    let (first, rest) :=
      if baseIsCall then (first, rest) else
        let (more, rest) := takeMembers rest
        (first ++ more, rest)
    first :: laterGroups false [] rest
where
  /-- As many calls, `!`s, and numeric index accesses, as there are. -/
  takeFirst : List ChainItem → List ChainItem × List ChainItem
    | [] => ([], [])
    | i :: rest =>
        if i.kind == .call || i.kind == .nonNull || (i.kind == .index && i.numericIndex) then
          let (taken, rest) := takeFirst rest
          (i :: taken, rest)
        else ([], i :: rest)
  /-- Then as many member accesses as there are, but not the last one. -/
  takeMembers : List ChainItem → List ChainItem × List ChainItem
    | i :: j :: rest =>
        if i.isMemberish && j.isMemberish then
          let (taken, rest) := takeMembers (j :: rest)
          (i :: taken, rest)
        else ([], i :: j :: rest)
    | items => ([], items)
  laterGroups (seenCall : Bool) (current : List ChainItem) :
      List ChainItem → List (List ChainItem)
    | [] => if current.isEmpty then [] else [current]
    | i :: rest =>
        if seenCall && i.isMemberish && !(i.kind == .index && i.numericIndex) then
          current :: laterGroups (i.kind == .call) [i] rest
        else
          laterGroups (seenCall || i.kind == .call) (current ++ [i]) rest

/-- Whether the group that follows the head of the chain stays on the line
of the head: prettier merges it when the head is `this`, a factory, or a
short identifier at the start of a statement, or when the group starts
with a computed access. -/
def chainShouldMerge (isStatement : Bool) (base : ChainItem)
    (groups : List (List ChainItem)) : Bool :=
  let laterGroups := groups.tail
  let hasComputed :=
    match laterGroups.head? with
    | some (i :: _) => i.kind == .index
    | _ => false
  let shouldNotWrap :=
    match groups.headD [] with
    | [] =>
        base.isThis ||
          (base.identName != "" &&
            (isFactoryName base.identName ||
              (isStatement && base.identName.length ≤ tabWidth) || hasComputed))
    | g =>
        match g.getLast? with
        | some i => i.kind == .dot && (isFactoryName i.name || hasComputed)
        | none => false
  !laterGroups.isEmpty && shouldNotWrap

/-- Whether prettier lays the elements out with the member chain layout,
rather than simply writing them one after the other: it does so when more
than one group is left once the head, and the group merged into it, are
taken away. -/
def chainItemsAreMemberChain (isStatement : Bool) (items : List ChainItem) : Bool :=
  match collapseNonNullHead items with
  | [] => false
  | base :: links =>
    let groups := chainGroups base.isCallBase links
    let laterGroups := groups.tail
    let cutoffGroups :=
      if chainShouldMerge isStatement base groups then laterGroups.tail else laterGroups
    cutoffGroups.length > 1

/-- Lay out a member chain.  `curried` says that the chain is a call which
is a link of a long curried chain, `a.f(x, y)(z)`: prettier then leaves a
chain short enough to be written on one line ungrouped, so that it breaks
with the call that holds it. -/
def memberChainDoc (isStatement curried : Bool) (items : List ChainItem) : Doc :=
  match collapseNonNullHead items with
  | [] => .nil
  | base :: links =>
    let groups := chainGroups base.isCallBase links
    let groupDoc (g : List ChainItem) : Doc := Doc.concat (g.map (·.doc))
    let firstDoc : Doc := base.doc ++ groupDoc (groups.headD [])
    let laterGroups := groups.tail
    let shouldMerge := chainShouldMerge isStatement base groups
    let oneLine : Doc := firstDoc ++ Doc.concat (laterGroups.map groupDoc)
    let cutoffGroups := if shouldMerge then laterGroups.tail else laterGroups
    let mergedDoc : Doc :=
      if shouldMerge then groupDoc (laterGroups.headD []) else .nil
    if cutoffGroups.length ≤ 1 then (if curried then oneLine else .group oneLine)
    else
      let expanded : Doc :=
        firstDoc ++ mergedDoc
          ++ .nest indentWidth
              (.hardline ++ Doc.joinWith .hardline (cutoffGroups.map groupDoc))
      let callCount := (if base.isCallBase then 1 else 0)
        + (links.filter (·.kind == .call)).length
      let anyComplexArgs := (base.isCallBase && !base.simpleArgs)
        || links.any (fun i => i.kind == .call && !i.simpleArgs)
      let allDocs := firstDoc :: laterGroups.map groupDoc
      let earlyBreak := (allDocs.dropLast).any Doc.hasForcedBreak
      let lastGroupBreaks :=
        match laterGroups.getLast? with
        | some g =>
            (match g.getLast? with | some i => i.kind == .call | none => false)
              && Doc.hasForcedBreak (groupDoc g)
              && ((base.isCallBase && base.functionArg)
                  || (links.dropLast).any (fun i => i.kind == .call && i.functionArg))
        | none => false
      if (callCount > 2 && anyComplexArgs) || earlyBreak || lastGroupBreaks then
        .group expanded
      else
        (if Doc.hasForcedBreak oneLine then .breakParent else .nil)
          ++ .condGroup oneLine expanded

/-- Whether the expression is a call with at least one argument; the call
at the end of an optional chain counts, and so does one under a non-null
assertion, which prettier reads through when it looks for what holds a
member access. -/
def isCallWithArgs : MiniExpr → Bool
  | .call _ _ args => !args.isEmpty
  | .nonNull e => isCallWithArgs e
  | .chain _ links =>
      match (links.hd :: links.tl).getLast? with
      | some (.call _ _ args) => !args.isEmpty
      | _ => false
  | _ => false

/-- Whether prettier keeps a member access on the line of its object,
rather than letting the line break in front of the access, as far as the
rules it reads off the access itself and off what stands immediately
around it go, given what the object of the access is.  `objIsChain` says
that the object is laid out as a member chain, which the access of an
assigned chain keeps its line for.  These are the rules that hold of an
access written inside an optional chain as well. -/
def memberInlinesInChain (pos : Pos)
    (objIsIdent objIsCallWithArgs objIsChain propIsIdent : Bool) : Bool :=
  (propIsIdent && objIsIdent && !isMemberObjectPos pos)
    || ((isAssignRhsPos pos || pos == .assignTarget) && (objIsCallWithArgs || objIsChain))

/-- Whether prettier keeps a member access on the line of its object,
rather than letting the line break in front of the access.  This is
`memberInlinesInChain` together with the rules prettier reads off what
holds the whole chain of accesses the access belongs to: those are the
ones an optional chain hides, since prettier reads such a chain into a
chain expression of its own, which stands between the accesses and what
holds them. -/
def memberInlines (pos : Pos) (objIsIdent objIsCallWithArgs objIsChain propIsIdent : Bool) :
    Bool :=
  pos == .newCallee
    -- the chain is assigned to something other than a plain identifier
    || inlineMemberRoot pos
    || memberInlinesInChain pos objIsIdent objIsCallWithArgs objIsChain propIsIdent

/-- A member access, given the documents of its object and of the access
itself. -/
def memberDocOf (inline : Bool) (objDoc lookup : Doc) : Doc :=
  objDoc ++ (if inline then lookup else .group (.nest indentWidth (.softline ++ lookup)))

/-- A computed member access, given the document of the index. -/
def indexLookupDoc (numeric : Bool) (d : Doc) : Doc :=
  if numeric then t "[" ++ d ++ t "]"
  else .group (t "[" ++ .nest indentWidth (.softline ++ d) ++ .softline ++ t "]")

/-- Whether the first link of a chain is a computed access: the parentheses
that a base may need then stay tight against the `[` that follows them,
whereas a `.` access is allowed to go on a line of its own. -/
def chainStartsComputed (links : NEList MiniChainLink) : Bool :=
  match links.hd with
  | .index .. => true
  | _ => false

/-- The position of the base of an optional chain that stands in `pos`:
the base is the callee of the first link when that link is a call, and
the object of a member access otherwise. -/
def chainBasePos (pos : Pos) (links : NEList MiniChainLink) : Pos :=
  match links.hd with
  | .call _ _ args => calleePos pos args.length
  | _ =>
      -- a call among the links stands between the base and whatever holds
      -- the chain: the accesses inside the base then take a line of their
      -- own, whatever the chain is written in.  An optional chain is read
      -- into a chain expression of its own, which stands between the
      -- accesses of the chain and whatever holds it, so those accesses do
      -- not keep the line of their object for the sake of an assignment
      -- outside the chain either.
      if links.toList.any chainLinkIsCall || chainIsOptional links then
        .memberObject (chainStartsComputed links) (extraIndentRoot pos) false
      else memberObjectPos (chainStartsComputed links) pos

/-- The base of a member chain.  A parenthesised optional chain stands
for the expression written inside the parentheses: when that ends with a
call, the base is a call of the chain that holds it. -/
def chainBaseItem (e : MiniExpr) (d : Doc) : ChainItem :=
  let baseArgs : Option (List MiniExpr) :=
    match e with
    | .call _ _ args => some args
    | .chain _ links =>
        (match links.toList.getLast? with
          | some (.call _ _ args) => some args
          | _ => none)
    | _ => none
  { kind := .base, doc := d,
    isThis := (match e with | .this => true | _ => false),
    identName := (match e with | .ident n => n.val | _ => ""),
    isCallBase := baseArgs.isSome,
    simpleArgs := (match baseArgs with
      | some args => args.all (isSimpleCallArgument 2)
      | none => true),
    functionArg := (match baseArgs with
      | some args => args.any isFunctionLike
      | none => false),
    hasArgs := (match baseArgs with | some args => !args.isEmpty | none => false) }

/-- One call of a member chain. -/
def chainCallItem (args : List MiniExpr) (d : Doc) : ChainItem :=
  { kind := .call, doc := d,
    simpleArgs := args.all (isSimpleCallArgument 2),
    functionArg := args.any isFunctionLike,
    hasArgs := !args.isEmpty }

/-- Split the elements of a chain after its last call: what comes before
is laid out as a member chain, and the member accesses that follow it are
laid out one by one, as prettier prints the member expressions that hold
the chain. -/
def splitAfterLastCall (items : List ChainItem) : List ChainItem × List ChainItem :=
  let rec lastCall (idx found : Nat) : List ChainItem → Nat
    | [] => found
    | i :: rest => lastCall (idx + 1) (if i.kind == .call then idx + 1 else found) rest
  let k := lastCall 0 1 items
  (items.take k, items.drop k)

/-- The elements of the links of an optional chain, without their
documents. -/
def chainLinkShapeItem : MiniChainLink → ChainItem
  | .dot _ n => { kind := .dot, name := n.val, doc := .nil }
  | .privateDot _ n => { kind := .dot, name := n.val, doc := .nil }
  | .index _ i => { kind := .index, numericIndex := isNumericLit i, doc := .nil }
  | .call _ _ args => chainCallItem args .nil
  | .nonNull => { kind := .nonNull, doc := .nil }

/-- The elements of a list of links, without their documents. -/
def chainLinkShapeItems : List MiniChainLink → List ChainItem
  | [] => []
  | l :: rest => chainLinkShapeItem l :: chainLinkShapeItems rest

/-- The elements of the member chain whose last node is `e`, without their
documents: what the layout heuristics need in order to tell whether the
chain is one prettier lays out as a member chain. -/
def chainShapeItems : MiniExpr → List ChainItem
  | .dot o n =>
      (if isChainNodeObject o then chainShapeItems o else [chainBaseItem o .nil])
        ++ [{ kind := .dot, name := n.val, doc := .nil }]
  | .privateDot o n =>
      (if isChainNodeObject o then chainShapeItems o else [chainBaseItem o .nil])
        ++ [{ kind := .dot, name := n.val, doc := .nil }]
  | .index o i =>
      (if isChainNodeObject o then chainShapeItems o else [chainBaseItem o .nil])
        ++ [{ kind := .index, numericIndex := isNumericLit i, doc := .nil }]
  | .call f _ args =>
      (if isChainNode f then chainShapeItems f else [chainBaseItem f .nil])
        ++ [chainCallItem args .nil]
  | .chain b links =>
      (if isChainSpineObject b then chainShapeItems b else [chainBaseItem b .nil])
        ++ chainLinkShapeItems (links.hd :: links.tl)
  -- a `!` is an element of the chain, which goes on into the expression
  -- it is written on
  | .nonNull e =>
      (if isChainNodeObject e then chainShapeItems e else [chainBaseItem e .nil])
        ++ [{ kind := .nonNull, doc := .nil }]
  | e => [chainBaseItem e .nil]

/-- Whether prettier lays the expression out with the member chain layout.
The right hand side of an assignment that it does lay out that way is not
one it breaks the line after the operator for: the chain breaks on its own
instead. -/
def printsAsMemberChain (e : MiniExpr) : Bool :=
  match e with
  | .call f _ _ =>
      isMemberish f
        && chainItemsAreMemberChain false (splitAfterLastCall (chainShapeItems e)).1
  | .chain _ _ =>
      chainItemsAreMemberChain false (splitAfterLastCall (chainShapeItems e)).1
  | _ => false

/-- Whether one of the calls along the spine of the expression is laid out
with the member chain layout. -/
def spineHasMemberChain : MiniExpr → Bool
  | .call f ta args => printsAsMemberChain (.call f ta args) || spineHasMemberChain f
  | .dot o _ | .privateDot o _ | .index o _ => spineHasMemberChain o
  -- the base of an optional chain may be a chain of its own, laid out
  -- with the member chain layout inside the parentheses it needs
  | .chain b links => printsAsMemberChain (.chain b links) || spineHasMemberChain b
  | _ => false

/-- Whether the document of the expression is a member chain: prettier
lays the expression out as one, or it is a member access whose object is,
which passes the member chain layout on.  -/
def docIsMemberChain : MiniExpr → Bool
  | .dot o _ | .privateDot o _ | .index o _ => docIsMemberChain o
  | e => printsAsMemberChain e

/-- Whether prettier keeps a member access on the line of its object,
rather than letting the line break in front of the access. -/
def memberAccessInlines (pos : Pos) (obj : MiniExpr) (propIsIdent : Bool) : Bool :=
  memberInlines pos (match obj with | .ident _ => true | _ => false)
    (isCallWithArgs obj) (docIsMemberChain obj) propIsIdent

/-! ## Assignments -/

/-- Whether prettier breaks the line after the `=` of an assignment whose
right hand side is `rhs`. -/
def shouldBreakAfterOperator (shortKey : Bool) (rhs : MiniExpr) : Bool :=
  match rhs with
  | .binary .. => !shouldInlineLogical rhs
  | .seq _ _ => true
  -- under `experimentalTernaries` it is a chain of conditionals, rather
  -- than an operator chain in the test, that breaks the line
  | .ternary test a b =>
      if Options.experimentalTernaries then
        (match a with | .ternary .. => true | _ => false)
          || (match b with | .ternary .. => true | _ => false)
      else isBinaryish test && !shouldInlineLogical test
  | .classExpr decorators _ _ _ _ _ => !decorators.isEmpty
  | _ =>
    if shortKey then false
    else
      let rec strip : MiniExpr → MiniExpr
        | .unary _ a => strip a
        | .await a => strip a
        | .yield (some a) => strip a
        -- prettier reads through a `!` here as it reads through a unary
        -- operator: `x = a?.b!.c!` breaks after the `=`
        | .nonNull a => strip a
        | e => e
      let node := strip rhs
      isStringLit node ||
        (isPoorlyBreakableChain false node && !spineHasMemberChain node)

/-- The expression whose shape decides the layout of `key: value` in an
object pattern: prettier chooses that layout as it chooses the layout of
an assignment, reading the pattern as the right hand side.  A pattern
which is not a plain name or an assignment target has no layout of its
own, and `null` stands for it, since the choice is the same for every
such shape. -/
def patternLayoutExpr : MiniPattern → MiniExpr
  | .ident n => .ident n
  | .target e => e
  | _ => .null

/-- Whether the right hand side is one prettier never breaks after the
operator for. -/
def neverBreakAfterOperator (shortKey : Bool) (rhs : MiniExpr) : Bool :=
  shortKey ||
    (match rhs with
      | .template _ _ _ _ => true
      | .true_ | .false_ => true
      -- a `BigInt` literal is not a numeric literal to prettier, and does
      -- not keep the line of the operator
      | .number (.bigint ..) => false
      | .number _ => true
      | .classExpr .. => true
      | _ => false)

/-- Whether the expression is an assignment. -/
def isAssignExpr : MiniExpr → Bool
  | .assign .. | .assignPattern .. => true
  | _ => false

/-- Whether the expression is an arrow function whose body is another
arrow function, which the tail of a chain of assignments keeps on the line
of its operator. -/
def isArrowChainExpr : MiniExpr → Bool
  | .arrow _ _ _ _ (.expr (.arrow ..)) => true
  | _ => false

/-- The layouts prettier chooses between for an assignment, a declarator,
a property or a field. -/
inductive AssignLayout where
  /-- Break after the operator; the two sides then break on their own. -/
  | breakAfterOperator
  /-- Never break after the operator. -/
  | neverBreakAfterOperator
  /-- Keep the right hand side on the line while its first line fits. -/
  | fluid
  /-- Break the left hand side first. -/
  | breakLhs
  /-- A link of a chain of assignments: once one of them breaks, they all
  do, and the links are not indented. -/
  | chain
  /-- The last link of a chain of assignments. -/
  | chainTail
  /-- The last link of a chain of assignments, a chain of arrow functions
  that keeps the line of the operator. -/
  | chainTailArrowChain
deriving BEq, Inhabited

/-- Prettier's choice of layout.  `nodeIsAssign` says that the node is an
assignment expression, rather than a declarator, a property or a field;
`parentIsAssign` that it stands on the right of an assignment or of a
declarator; `grandparentIsStatement` that that assignment is itself an
expression statement or a declaration, which keeps a chain of two
assignments out of the chain layout.  `complexLhs` asks for the left hand
side to be broken first, and `leftCanBreak` says that the left hand side
holds a line. -/
def chooseAssignLayout (nodeIsAssign parentIsAssign grandparentIsStatement
    complexLhs leftCanBreak shortKey : Bool) (rhs : MiniExpr) : AssignLayout :=
  let isTail := !isAssignExpr rhs
  if nodeIsAssign && parentIsAssign && (!isTail || !grandparentIsStatement) then
    if !isTail then .chain
    else if isArrowChainExpr rhs then .chainTailArrowChain
    else .chainTail
  else if !isTail && (match rhs with
      | .assign _ _ r => isAssignExpr r
      | .assignPattern _ r => isAssignExpr r
      | _ => false) then
    -- the head of a chain of more than two assignments
    .breakAfterOperator
  -- `const x = require("a/long/module/path");` keeps the line of the `=`
  else if (match rhs with | .call (.ident n) _ _ => n.val == "require" | _ => false) then
    .neverBreakAfterOperator
  else if complexLhs then .breakLhs
  else if shouldBreakAfterOperator shortKey rhs then .breakAfterOperator
  else if !leftCanBreak && neverBreakAfterOperator shortKey rhs then
    .neverBreakAfterOperator
  else .fluid

/-- An assignment, a declarator, a property or a field, given its layout
and the documents of its two sides. -/
def assignmentDocOf (layout : AssignLayout) (leftDoc : Doc) (op : String)
    (rightDoc : Doc) : Doc :=
  match layout with
  | .breakAfterOperator =>
      .group (.group leftDoc ++ t op ++ .group (.nest indentWidth (.line ++ rightDoc)))
  | .neverBreakAfterOperator => .group (.group leftDoc ++ t op ++ t " " ++ rightDoc)
  -- prettier's "fluid" layout: keep the right hand side on the line when
  -- its first line fits, and break after the operator otherwise
  | .fluid => .group (.group leftDoc ++ t op ++ .fluidLine indentWidth rightDoc)
  | .breakLhs => .group (leftDoc ++ t op ++ t " " ++ .group rightDoc)
  -- the links of a chain of assignments are not wrapped in groups of
  -- their own: once one of them breaks, the whole chain breaks
  | .chain => .group leftDoc ++ t op ++ .line ++ rightDoc
  | .chainTail => .group leftDoc ++ t op ++ .nest indentWidth (.line ++ rightDoc)
  | .chainTailArrowChain => .group leftDoc ++ t op ++ rightDoc

/-- An assignment, a declarator, a property or a field, given the
documents of its two sides. -/
def assignmentDoc (shortKey : Bool) (leftDoc : Doc) (op : String) (rhs : MiniExpr)
    (rightDoc : Doc) : Doc :=
  assignmentDocOf
    (chooseAssignLayout false false false false (Doc.canBreak leftDoc) shortKey rhs)
    leftDoc op rightDoc

/-- The member accesses that trail the last call of a chain, added to the
document of what comes before them.  `optional` says that the chain is an
optional one, which prettier reads into a chain expression of its own:
that expression stands between the accesses and whatever holds the chain,
so the rules read off what holds it do not reach them. -/
def chainTrailingAux (optional : Bool) (pos : Pos) (objIsIdent objIsCall objIsChain : Bool)
    (acc : Doc) : List ChainItem → Doc
  | [] => acc
  | i :: rest =>
      let p : Pos := if rest.isEmpty then pos else memberObjectPos false pos
      -- a `!` keeps the line of what it is written on: TypeScript does not
      -- read a `!` written at the start of a line as a non-null assertion
      let inline :=
        i.kind == .index || i.kind == .nonNull
          || (if optional then memberInlinesInChain else memberInlines)
              p objIsIdent objIsCall objIsChain (i.kind == .dot)
      -- the member chain layout of the object carries over to the accesses
      -- that trail it
      chainTrailingAux optional pos false false objIsChain
        (memberDocOf inline acc i.doc) rest

/-- Lay out an optional chain, given its elements.  A chain that holds no
call at all is not a member chain to prettier, which prints it as the
member accesses it is made of: the accesses are not grouped together, so
that the chain does not have to be laid out flat as a whole.  `optional`
says that the chain holds a link written `?.`, which is what makes
prettier read it into a chain expression of its own. -/
def chainAssemble (optional : Bool) (pos : Pos) (items : List ChainItem) : Doc :=
  let (head, trailing) := splitAfterLastCall items
  let noCalls := !items.any (fun i => i.kind == .call || i.isCallBase)
  let headDoc := memberChainDoc (pos == .statement && trailing.isEmpty) noCalls head
  if trailing.isEmpty then headDoc
  else
    let objIsIdent :=
      head.length == 1 && (match head.head? with | some i => i.identName != "" | none => false)
    let objIsCall :=
      match head.getLast? with
      | some i => (i.kind == .call || i.isCallBase) && i.hasArgs
      | none => false
    chainTrailingAux optional pos objIsIdent objIsCall
      (chainItemsAreMemberChain false head) headDoc trailing

/-- Whether the last link of an optional chain is a member access rather
than a call. -/
def chainEndsInMember (links : NEList MiniChainLink) : Bool :=
  match (links.hd :: links.tl).getLast? with
  | some (.call ..) => false
  | _ => true

/-- Whether prettier indents the substitution of a template literal that
it has to break. -/
def templateSubstIndents : MiniExpr → Bool
  | .ident _ | .dot .. | .privateDot .. | .index .. | .ternary .. | .seq _ _
  | .binary .. => true
  -- an `as` and a `satisfies` are indented too; a `!` is not
  | .asExpr .. | .satisfies .. => true
  | .chain _ links => chainEndsInMember links
  | _ => false

/-- One `${…}` substitution of a template literal.  Prettier lays the
substitution out on one line, however long it is; only one that breaks of
itself is broken, and then the kind of expression says whether it is
indented. -/
def templateSubstDoc (indents : Bool) (d : Doc) : Doc :=
  let flat := Doc.render 1000000 d
  if !flat.any (· == '\n') then t "${" ++ t flat ++ t "}"
  else if indents then
    .group (t "${" ++ .nest indentWidth (.softline ++ d) ++ .softline ++ t "}")
  else .group (t "${" ++ d ++ t "}")

/-! ## Arguments that may be hugged -/

/-- A tag that tells the kinds of expression apart. -/
def nodeTag : MiniExpr → Nat
  | .ident _ => 0 | .number _ => 1 | .string _ => 2 | .regex _ => 3
  | .null => 4 | .true_ => 5 | .false_ => 6 | .this => 7
  | .superDot _ => 8 | .superIndex _ => 9 | .superCall _ => 10
  | .newTarget => 11 | .array _ => 12 | .object _ => 13
  | .assign .. => 14 | .assignPattern .. => 15 | .await _ => 16
  | .call .. => 17 | .dot .. => 18 | .privateDot .. => 19
  | .privateName _ => 20 | .index .. => 21 | .chain .. => 22
  | .importMeta => 23 | .importCall .. => 24 | .classExpr .. => 25
  | .seq .. => 26 | .binary .. => 27 | .postfix .. => 28 | .ternary .. => 29
  | .arrow .. => 30 | .func .. => 31 | .new .. => 32 | .spread _ => 33
  | .template .. => 34 | .unary .. => 35 | .yield _ => 36 | .yieldFrom _ => 37
  | .jsx _ => 38
  | .asExpr .. => 39 | .satisfies .. => 40 | .nonNull _ => 41
  | .instantiation .. => 42

/-- Whether the argument is one prettier may expand in place, keeping the
rest of the call on one line.  `inChain` says that the argument is the
body of an arrow function that is itself such an argument, where a
conditional or a call does not count. -/
def couldExpandArg (inChain : Bool) : MiniExpr → Bool
  | .object (_ :: _) => true
  | .array (_ :: _) => true
  | .func .. => true
  -- prettier reads through an `as` or a `satisfies`: what it holds is
  -- what the layout expands
  | .asExpr e _ | .satisfies e _ => couldExpandArg inChain e
  | .arrow _ _ _ _ body =>
      match body with
      | .block _ => true
      | .expr e =>
        match e with
        | .object _ | .array _ | .jsx _ => true
        | .arrow .. => couldExpandArg true e
        | .ternary .. | .call .. => !inChain
        -- an optional chain that ends in a call is a call too
        | .chain _ links =>
            !inChain && (match (links.hd :: links.tl).getLast? with
              | some (.call ..) => true
              | _ => false)
        | _ => false
  | _ => false

/-- Whether the type is a simple one: a name with no type arguments (which
is what a predefined type such as `string` is too), a literal type, or
`this`. -/
def isSimpleTsType : MiniTsType → Bool
  | .ref _ [] => true
  | .strLit _ | .numLit _ | .negNumLit _ | .templateLit .. | .this => true
  | _ => false

/-- The type an `as` or a `satisfies` written as the second argument of a
call is judged by: prettier looks through as many as two `[]`, and then
through the one type argument of a name that takes exactly one. -/
def shortArgumentType : MiniTsType → MiniTsType
  | .array (.array ty) => throughOneArg ty
  | .array ty => throughOneArg ty
  | ty => throughOneArg ty
where
  /-- The one type argument of a name that takes exactly one. -/
  throughOneArg : MiniTsType → MiniTsType
    | .ref _ [arg] => arg
    | ty => ty

/-- Prettier's `isHopefullyShortCallArgument`, the test the second
argument of a call has to pass for its first argument to be hugged. -/
def isHopefullyShortCallArgument (e : MiniExpr) : Bool :=
  match e with
  -- `f(() => {…}, "" satisfies T)`: an `as` or a `satisfies` is short
  -- when its type is a simple one and what it holds is a simple argument
  | .asExpr inner ty | .satisfies inner ty =>
      isSimpleTsType (shortArgumentType ty) && isSimpleCallArgument 1 inner
  | .call _ _ args => args.length ≤ 1 && isSimpleCallArgument 2 e
  | .new _ _ args => args.length ≤ 1 && isSimpleCallArgument 2 e
  -- an optional chain is read as one expression, whatever its links:
  -- unlike a plain call, a call written as its last link does not have
  -- to take one argument at most
  | .chain .. => isSimpleCallArgument 2 e
  | .importCall _ options => options.isNone && isSimpleCallArgument 2 e
  | .binary l _ r => isSimpleCallArgument 1 l && isSimpleCallArgument 1 r
  | .regex _ => true
  | _ => isSimpleCallArgument 2 e

/-- Whether the first argument of a call may be hugged: the call takes a
function and one short second argument, as in `setTimeout(() => {…}, 0)`. -/
def canHugFirstArg (args : List MiniExpr) : Bool :=
  match args with
  | [first, second] =>
      (match first with
        | .func .. => true
        | .arrow _ _ _ _ (.block _) => true
        | _ => false)
      && (match second with
          | .func .. | .arrow .. | .ternary .. => false
          | _ => true)
      && isHopefullyShortCallArgument second
      && !couldExpandArg false second
  | _ => false

/-- The arguments of a call, of a `new` or of the call at the end of an
optional chain. -/
def callArgumentsOf : MiniExpr → Option (List MiniExpr)
  | .call _ _ args => some args
  | .chain _ links =>
      match (links.hd :: links.tl).getLast? with
      | some (.call _ _ args) => some args
      | _ => none
  | _ => none

/-- Whether the arguments are those of a composition of functions, as in
`pipe(map((x) => x), filter((x) => y))`: more than one of them is a
function, or one of them is a call that takes a function.  Prettier always
breaks such an argument list. -/
def isFunctionCompositionArguments (args : List MiniExpr) : Bool :=
  args.length > 1 && go 0 args
where
  go (count : Nat) : List MiniExpr → Bool
    | [] => false
    | a :: rest =>
        if isFunctionLike a then count ≥ 1 || go (count + 1) rest
        else
          match callArgumentsOf a with
          | some cargs => cargs.any isFunctionLike || go count rest
          | none => go count rest

/-- Whether the expression is a numeric literal which is not a `BigInt`
one; prettier treats the two as different kinds of literal. -/
def isPlainNumberLit : MiniExpr → Bool
  | .number (.bigint ..) => false
  | .number _ => true
  | _ => false

/-- Whether every element of the array is a number, possibly signed.  A
`BigInt` literal is not a number here, and neither is a hole. -/
def isNumberArray (els : List MiniArrayElement) : Bool :=
  !els.isEmpty && els.all (fun e =>
    match e with
    | .elem (.unary op e) => (op == .plus || op == .minus) && isPlainNumberLit e
    | .elem e => isPlainNumberLit e
    | _ => false)

/-- Whether prettier fills the lines with the elements of the array
instead of putting one element on each line: it does so when the array
holds more than one element and every one of them is a number, possibly
signed. -/
def isConciselyPrintedArray (els : List MiniArrayElement) : Bool :=
  els.length > 1 && isNumberArray els

/-- Whether the last argument of a call may be hugged. -/
def canHugLastArg (args : List MiniExpr) : Bool :=
  match args.reverse with
  | [] => false
  | last :: rest =>
      couldExpandArg false last
        && (match rest with
            | [] => true
            | p :: _ => nodeTag p != nodeTag last)
        && !(args.length == 2
              && (match rest with
                  | .arrow .. :: _ => true
                  | _ => false)
              && (match last with | .array _ => true | _ => false))
        -- `f(a, [1, 2, 3])`: an array of numbers, which the layout fills,
        -- is not hugged when it is not the only argument
        && !(args.length > 1
              && (match last with | .array els => isNumberArray els | _ => false))

/-- Whether the arguments are those of a call of a React hook with a
dependency array, as `useEffect(() => { ... }, [a, b])` and
`useImperativeHandle(ref, () => { ... }, [a, b])` are, which prettier
writes as it finds them. -/
def isHookCallWithDepsArray (args : List MiniExpr) : Bool :=
  let callbackAndDeps (fn deps : MiniExpr) : Bool :=
    (match fn with | .arrow _ _ [] _ (.block _) => true | _ => false)
      && (match deps with | .array _ => true | _ => false)
  match args with
  | [fn, deps] => callbackAndDeps fn deps
  | [first, fn, deps] =>
      (match first with | .ident _ => true | _ => false) && callbackAndDeps fn deps
  | _ => false

/-! ## The calls prettier keeps on one line -/

/-- The dotted name a callee is written with, as `require.resolve`;
`none` when the callee is not a chain of plain names. -/
def dottedCalleeName : MiniExpr → Option String
  | .ident n => some n.val
  | .importMeta => some "import.meta"
  | .dot o n => (dottedCalleeName o).map (fun s => s ++ "." ++ n.val)
  | _ => none

/-- The names a module is asked for with, whose one string argument
prettier writes on the line of the call, however long it is. -/
def requireLikeNames : List String :=
  ["require", "require.resolve", "require.resolve.paths", "import.meta.resolve"]

/-- The names of the calls of a test framework, whose arguments prettier
writes on the line of the call. -/
def testCallNames : List String :=
  ["it", "it.only", "it.skip", "describe", "describe.only", "describe.skip",
   "test", "test.only", "test.skip", "test.fixme", "test.step", "test.describe",
   "test.describe.only", "test.describe.skip", "test.describe.fixme",
   "test.describe.parallel", "test.describe.parallel.only", "test.describe.serial",
   "test.describe.serial.only", "skip", "xit", "xdescribe", "xtest", "fit",
   "fdescribe", "ftest"]

/-- Whether the callee is written with one of `names`. -/
def calleeNamed (names : List String) (callee : MiniExpr) : Bool :=
  match dottedCalleeName callee with
  | some s => names.contains s
  | none => false

/-- `require("mod")` and the other calls which ask for a module by name. -/
def isRequireLikeCall (callee : MiniExpr) (args : List MiniExpr) : Bool :=
  match args with
  | [a] => isStringLit a && calleeNamed requireLikeNames callee
  | _ => false

/-- A module definition of CommonJS or of AMD: `require` of several
arguments, and the `define` of a module, which only stands as a statement
of its own. -/
def isModuleDefinitionCall (parentIsStatement : Bool) (callee : MiniExpr)
    (args : List MiniExpr) : Bool :=
  match callee with
  | .ident n =>
      if n.val == "require" then
        (match args with | [a] => isStringLit a | _ => args.length > 1)
      else if n.val == "define" && parentIsStatement then
        (match args with
          | [_] => true
          | [.array _, _] => true
          | [a, .array _, _] => isStringLit a
          | _ => false)
      else false
  | _ => false

/-- One of the names an Angular test is wrapped in. -/
def isAngularWrapperName : MiniExpr → Bool
  | .ident n =>
      n.val == "async" || n.val == "inject" || n.val == "fakeAsync" || n.val == "waitForAsync"
  | _ => false

/-- A call of one of the wrappers an Angular test is written with. -/
def isAngularTestWrapper : MiniExpr → Bool
  | .call callee _ _ => isAngularWrapperName callee
  | _ => false

/-- `beforeEach` and the other names a test framework sets a test up
with. -/
def isUnitTestSetupName : MiniExpr → Bool
  | .ident n =>
      n.val == "beforeEach" || n.val == "beforeAll" || n.val == "afterEach"
        || n.val == "afterAll"
  | _ => false

/-- A function expression or an arrow function. -/
def isFunctionOrArrowExpr : MiniExpr → Bool
  | .func .. | .arrow .. => true
  | _ => false

/-- A function expression, or an arrow function whose body is a block. -/
def isFunctionOrArrowWithBlock : MiniExpr → Bool
  | .func .. => true
  | .arrow _ _ _ _ (.block _) => true
  | _ => false

/-- The number of parameters of a function expression or an arrow. -/
def exprParamCount : MiniExpr → Nat
  | .func _ _ _ _ ps _ _ => ps.length
  | .arrow _ _ ps _ _ => ps.length
  | _ => 0

/-- Whether the expression is the name a test is given: a string literal
or a template literal. -/
def isTestName : MiniExpr → Bool
  | .string _ => true
  | .template none _ _ _ => true
  | _ => false

/-- Whether the call is one of a test framework, as `it("name", () => {})`
and `beforeEach(inject(f))` are.  `parentIsTest` says that the call is an
argument of a test call, where the wrapper an Angular test is written with
is one as well. -/
def isTestCallOf (parentIsTest : Bool) (callee : MiniExpr) (args : List MiniExpr) : Bool :=
  match args with
  | [a] =>
      (isUnitTestSetupName callee && isAngularTestWrapper a)
        || (parentIsTest && isAngularWrapperName callee && isFunctionOrArrowExpr a)
  | [a, b] =>
      isTestName a && calleeNamed testCallNames callee
        && (isFunctionOrArrowExpr b || isAngularTestWrapper b)
  | [a, b, c] =>
      isTestName a && calleeNamed testCallNames callee && isNumericLit c
        && ((isFunctionOrArrowWithBlock b && exprParamCount b ≤ 1) || isAngularTestWrapper b)
  | _ => false

/-- Whether prettier writes the arguments of the call on the line of the
call, however long they are.  `parentIsStatement` says that the call is an
expression statement of its own, which only the `define` of an AMD module
asks about. -/
def callArgsStayOnLine (parentIsStatement parentIsTest : Bool) (callee : MiniExpr)
    (args : List MiniExpr) : Bool :=
  isRequireLikeCall callee args || isModuleDefinitionCall parentIsStatement callee args
    || isTestCallOf parentIsTest callee args

/-- Can this expression stand inside the callee of a `new`, as the object
a property is read off, without parentheses around the whole callee?  It
has to be a member expression that does not itself contain a call; a JSX
element standing there takes parentheses of its own. -/
def newCalleeObjOk : MiniExpr → Bool
  -- a call inside the callee would be read as the call of the `new`
  | .call .. | .superCall .. | .importCall .. | .chain .. => false
  | .dot o _ => newCalleeObjOk o
  | .privateDot o _ => newCalleeObjOk o
  | .index o _ => newCalleeObjOk o
  | .template (some tag) _ _ _ => newCalleeObjOk tag
  -- an operator binds less tightly than `new`, so it keeps its parentheses
  | .postfix .. | .unary .. | .await _ | .yield _ | .yieldFrom _ | .spread _
  | .arrow .. | .func .. | .classExpr .. | .assign .. | .assignPattern ..
  | .seq _ _ | .binary .. | .ternary .. => false
  | _ => true

/-- Can this expression be the callee of a `new` without parentheses? -/
def newCalleeOk : MiniExpr → Bool
  -- `new (<div />)()`: an element written as the callee itself is
  -- parenthesised, as prettier parenthesises it everywhere a tag may not
  -- stand alone
  | .jsx _ => false
  -- `new (C as any)()`: an `as` or a `satisfies` binds less tightly than
  -- `new`, so the callee is parenthesised.  Written deeper inside the
  -- callee, as the object a property is read off, it takes parentheses of
  -- its own instead, `new (C as any).Inner()`
  | .asExpr .. | .satisfies .. => false
  | e => newCalleeObjOk e

/-- Would printing `op` directly in front of `e` run the two operators
together, as `-` in front of `-1` would give `--1`? -/
def unaryClash (op : UnaryOp) (e : MiniExpr) : Bool :=
  match e with
  | .unary op' _ =>
      let plusLike (o : UnaryOp) := o == .plus || o == .preIncr
      let minusLike (o : UnaryOp) := o == .minus || o == .preDecr
      (plusLike op && plusLike op') || (minusLike op && minusLike op')
  | _ => false

/-- Whether an expression needs parentheses around the whole of it when it
is printed as a statement.  An object literal, a function or a class
expression at the start of the statement is parenthesised on its own, by
`inPosStart`. -/
def needsStatementParens : MiniExpr → Bool
  | .call f _ _ => needsStatementParens f
  | .dot o _ | .privateDot o _ | .index o _ | .postfix o _ | .chain o _ =>
      needsStatementParens o
  | .binary l _ _ | .assign l _ _ => needsStatementParens l
  | .ternary c _ _ => needsStatementParens c
  | .template (some tag) _ _ _ => needsStatementParens tag
  | _ => false

/-! ## TypeScript helpers -/

/-- The name of a type, or of a namespace: `A`, `A.B.C`. -/
def tsEntityDoc : TsEntityName → Doc
  | .ident n => t n.val
  | .qualified o n => tsEntityDoc o ++ t ("." ++ n.val)

/-- The precedence of a type expression, from 0 for the types that bind
least (a conditional, a function and a constructor type) to 5 for a
primary type.  A type written where a tighter one is expected takes
parentheses. -/
def tsTypePrec : MiniTsType → Nat
  | .conditional .. | .fn .. | .ctor .. | .predicate .. => 0
  | .union _ => 1
  | .intersection _ => 2
  | .keyof _ | .readonlyOp _ | .uniqueSymbol | .infer_ .. | .typeQuery .. => 3
  | .importType true .. => 3
  | .array _ | .indexed .. => 4
  | _ => 5

/-- The modifiers of a class member, in the order prettier writes them. -/
def tsMemberModsDoc (m : TsMemberMods) : Doc :=
  (if m.isDeclare then t "declare " else Doc.nil)
    ++ (match m.accessibility with | none => Doc.nil | some a => t (a.text ++ " "))
    ++ (if m.isStatic then t "static " else Doc.nil)
    ++ (if m.isAbstract then t "abstract " else Doc.nil)
    ++ (if m.isOverride then t "override " else Doc.nil)
    ++ (if m.isReadonly then t "readonly " else Doc.nil)

/-- The modifiers of a parameter property. -/
def tsParamModsDoc (m : TsParamMods) : Doc :=
  (match m.accessibility with | none => Doc.nil | some a => t (a.text ++ " "))
    ++ (if m.isOverride then t "override " else Doc.nil)
    ++ (if m.isReadonly then t "readonly " else Doc.nil)

/-- Whether the parameter is a parameter property, which declares a
member of the class as well.  Prettier writes the parameter list of a
constructor that has one on lines of its own. -/
def paramIsProperty : MiniParam → Bool
  | .plain _ mods _ _ _ => !mods.isEmpty
  | .rest .. => false

/-- Whether the parameter list is one prettier always breaks: a list of
more than one parameter, one of which is a parameter property. -/
def paramsForceBreak (params : List MiniParam) : Bool :=
  1 < params.length && params.any paramIsProperty

/-- Whether the last parameter is a rest parameter, which forbids the
trailing comma. -/
def restLast (params : List MiniParam) : Bool :=
  match params.getLast? with
  | some (.rest ..) => true
  | _ => false

/-- The parameter list of a function, a method or a function type, given
the documents of its parameters.  A list one of whose parameters is a
parameter property stands on lines of its own. -/
def paramListDocOf (params : List MiniParam) (items : List Doc) : Doc :=
  if paramsForceBreak params then sepListBroken "(" ")" false (if restLast params then .never else .all) items
  else paramsDocOf (shouldHugTheOnlyParameter params) (restLast params) items

/-- The parameter list of a function, not wrapped in a group of its own:
prettier lays it out together with the return type, so that the two break
as one. -/
def paramListDocOpenOf (params : List MiniParam) (items : List Doc) : Doc :=
  if paramsForceBreak params then sepListBroken "(" ")" false (if restLast params then .never else .all) items
  else if shouldHugTheOnlyParameter params then t "(" ++ Doc.concat items ++ t ")"
  else sepListOpen "(" ")" false (if restLast params then .never else .all) items

/-- Whether the return type is an object type, which prettier lets break
without breaking the parameter list in front of it. -/
def retIsObjectType : Option MiniTsType → Bool
  | some (.objectType _) | some (.mapped ..) => true
  | _ => false

/-- Whether prettier puts the parameter list of a function in a group of
its own, so that the return type may break while the parameters stay on
their line: it does so for a function of one parameter whose return type
is an object type or one that has to break, and only when the type
parameters are simple enough to stay on the line as well. -/
def shouldGroupParams (typeParams : List MiniTsTypeParam) (params : List MiniParam)
    (retIsObject : Bool) (retDoc : Doc) : Bool :=
  let typeParamsFit :=
    match typeParams with
    | [] => true
    | [tp] => tp.constraint.isNone && tp.default_.isNone
    | _ => false
  typeParamsFit && params.length == 1 && (retIsObject || Doc.hasForcedBreak retDoc)

/-- The parameter list of a function or of a method together with its
return type, which prettier lays out as one group: the parameter list
writes no group of its own, so that the two break as one, unless the
function is one whose parameters prettier keeps on their line.  `head`
stands inside that group; it holds the type parameters of the signatures
prettier breaks together with their parameter list, and is empty for the
declarations whose type parameters break on their own. -/
def signatureDocOf (head : Doc) (typeParams : List MiniTsTypeParam) (params : List MiniParam)
    (retIsObject : Bool) (paramsDoc retDoc : Doc) : Doc :=
  .group (head
    ++ (if shouldGroupParams typeParams params retIsObject retDoc then .group paramsDoc
        else paramsDoc)
    ++ retDoc)

/-- The signature of an arrow function: prettier writes the type
parameters of an arrow, its parameters and its return type as one group,
never keeping the parameters on their line while the return type breaks,
and breaking them together with type parameters that break. -/
def arrowSignatureOf (typeParams : List MiniTsTypeParam) (typeParamsDoc : Doc)
    (params : List MiniParam) (paramItems : List Doc) (retType : Option MiniTsType)
    (retDoc : Doc) : Doc :=
  if arrowParensAvoided typeParams params retType then .group (Doc.concat paramItems)
  else .group (typeParamsDoc ++ paramListDocOpenOf params paramItems ++ retDoc)

/-- The signature of a function, given its parameters and its return
type.  `head` holds the type parameters when they stand inside the group
the parameter list is laid out by. -/
def signatureOf (head : Doc) (typeParams : List MiniTsTypeParam) (params : List MiniParam)
    (ret : Option MiniTsType) (paramItems : List Doc) (retDoc : Doc) : Doc :=
  signatureDocOf head typeParams params (retIsObjectType ret)
    (paramListDocOpenOf params paramItems) retDoc

/-- Whether the statement is a block. -/
def isBlockStmt : MiniStatement → Bool
  | .block _ => true
  | _ => false

/-- Whether the statement is a string literal on its own, which is a
directive where a program or a function body starts. -/
def isStringStmt : MiniStatement → Bool
  | .expr (.string _) => true
  | _ => false

/-- Whether the statement is the empty statement, `;`. -/
def isEmptyStmt : MiniStatement → Bool
  | .empty => true
  | _ => false

/-- Whether the statement is an `if`. -/
def isIfStmt : MiniStatement → Bool
  | .if_ .. => true
  | _ => false

/-- Whether the body holds no statement but `;`, which prettier drops. -/
def bodyIsEmpty (body : List MiniStatement) : Bool := body.all isEmptyStmt

/-- The width of a property key, when it prints as plain text. -/
def keyTextWidth : MiniPropertyName → Option Nat
  | .ident n => some (Doc.stringWidth n.val)
  | .private_ n => some (Doc.stringWidth n.val + 1)
  | .number n => some (Doc.stringWidth n.render)
  | .string v =>
      if isIdentifierName v then some (Doc.stringWidth v)
      else some (Doc.stringWidth (strLit v))
  | .computed _ => none

/-- A logical expression whose right operand is a non-empty object or
array literal is kept on one line. -/
def shouldInlineLogicalOf (op : BinOp) (r : MiniExpr) : Bool :=
  isLogicalOp op &&
    (match r with
      | .object (_ :: _) => true
      | .array (_ :: _) => true
      | .jsx _ => true
      | _ => false)

/-- Whether the element is an array or an object literal of more than one
item, and which of the two it is. -/
def arrayElemKind : MiniArrayElement → Option (Bool × Nat)
  | .elem (.array xs) => some (true, xs.length)
  | .elem (.object ps) => some (false, ps.length)
  | _ => none

/-- Whether every element is an array, or every element is an object, each
of more than one item; prettier then breaks the array. -/
def allElemsAreMultiItem : Option Bool → List MiniArrayElement → Bool
  | _, [] => true
  | k, e :: rest =>
      match arrayElemKind e with
      | none => false
      | some (isArr, n) =>
          n > 1 && (match k with | none => true | some k' => k' == isArr)
            && allElemsAreMultiItem (some isArr) rest

/-- The parts of a `fill`: the elements, with their commas, separated by
line breaks.  The comma of an element belongs to the element itself, so
that the width the layout measures counts it; `trailer` is what follows
the last element, which is the trailing comma when the array breaks. -/
def fillParts (trailer : Doc) : List Doc → List Doc
  | [] => []
  | [d] => [d ++ trailer]
  | d :: rest => (d ++ t ",") :: .line :: fillParts trailer rest

/-- An array literal, given the documents of its elements. -/
def arrayDocOf (els : List MiniArrayElement) (items : List Doc) : Doc :=
  if els.isEmpty then t "[]"
  else
    let lastIsHole := match els.getLast? with
      | some .hole => true
      | _ => false
    -- an elision at the end needs its comma in both layouts
    let trailer : Doc :=
      if lastIsHole then t ","
      else if Options.hasTrailingComma .es5 then .ifBreak (t ",") .nil else .nil
    let body : Doc :=
      if isConciselyPrintedArray els then
        -- the trailing comma is part of the last element, and it is
        -- written exactly when the array itself breaks
        if lastIsHole then .fill (fillParts (t ",") items)
        else if Options.hasTrailingComma .es5 then
          .ifBreak (.fill (fillParts (t ",") items)) (.fill (fillParts .nil items))
        else .fill (fillParts .nil items)
      else Doc.joinWith (t "," ++ .line) items ++ trailer
    let contents := t "[" ++ .nest indentWidth (.softline ++ body) ++ .softline ++ t "]"
    if els.length > 1 && allElemsAreMultiItem none els then .groupBreak contents
    else .group contents

/-- An array pattern, given the documents of its elements. -/
def arrayPatternDocOf (els : List MiniArrayPatternElem) (items : List Doc) : Doc :=
  if els.isEmpty then t "[]"
  else
    let trailer : Doc := match els.getLast? with
      | some .hole => t ","
      | some (.rest _) => Doc.nil
      | _ => if Options.hasTrailingComma .es5 then .ifBreak (t ",") .nil else .nil
    .group (t "[" ++ .nest indentWidth
      (.softline ++ Doc.joinWith (t "," ++ .line) items ++ trailer) ++ .softline ++ t "]")

/-- Whether prettier forces an object pattern to break: one of its
properties destructures into a pattern of its own. -/
def objectPatternForcesBreak : List MiniObjectPatternProp → Bool
  | [] => false
  | ⟨_, value⟩ :: rest =>
      (match value with
        | .object .. | .array .. => true
        | _ => false)
      || objectPatternForcesBreak rest

/-- May the property `key: value` of an object pattern be written in the
short form, as `{ a }` or `{ a = 1 }`? -/
def patternShorthand (key : MiniPropertyName) (value : MiniPattern) : Bool :=
  match key, value with
  | .ident k, .ident v => k == v
  | .ident k, .withDefault (.ident v) _ => k == v
  | _, _ => false

/-- Whether prettier breaks the left hand side of a declarator or of a
destructuring assignment first: it destructures more than two properties
and one of them is written out, or has a default value. -/
def patternIsComplexDestructuring : MiniPattern → Bool
  | .object props _ =>
      props.length > 2 && props.any (fun p =>
        !patternShorthand p.key p.value
          || (match p.value with | .withDefault .. => true | _ => false))
  | _ => false

/-- Whether the type annotation of a declarator is a complex one, which
prettier breaks the left hand side of the declarator for: a type read by
name with more than one type argument, one of which is itself written
with type arguments or is a conditional type. -/
def tsAnnotationIsComplex : Option MiniTsType → Bool
  | some (.ref _ args) =>
      1 < args.length
        && args.any fun arg =>
          match arg with
          | .ref _ (_ :: _) => true
          | .conditional .. => true
          | _ => false
  | _ => false

/-- The decorators in front of a class or of a class member, given their
documents. -/
def decoratorsPrefix (items : List Doc) : Doc :=
  if items.isEmpty then Doc.nil
  else .group (Doc.joinWith .line items ++ .line)

/-- A parameter written with decorators, `@Inject() x: T`.  Prettier
lays the decorators out together with the parameter they stand in front
of: they keep the line of the parameter where the whole of it fits, and
stand on lines of their own where it does not. -/
def paramDecoratorsDoc (items : List Doc) (param : Doc) : Doc :=
  if items.isEmpty then param
  else .group (Doc.joinWith .line items ++ .line ++ param)

/-- The decorators of a class.  Prettier writes each of them on a line of
its own: they break every group they stand in.  The lines themselves are
ordinary ones, so that a class written where the whole line is laid out
flat, as a `{...expr}` child of a JSX element may be, keeps its
decorators on the line of the `class`. -/
def classDecoratorsPrefix (items : List Doc) : Doc :=
  if items.isEmpty then Doc.nil
  else .breakParent ++ Doc.joinWith .line items ++ .line

/-- A class body, given the documents of its members. -/
def classBodyOf (body : List MiniClassElement) (items : List Doc) : Doc :=
  if body.isEmpty then t "{}"
  else
    t "{" ++ .nest indentWidth (.hardline ++ Doc.joinWith .hardline items)
      ++ .hardline ++ t "}"

/-- The superclass of a class expression, given its document.  Prettier
puts the superclass of a class assigned to something in parentheses of
its own when it does not fit on the line of the `extends`. -/
def superClassDoc (ofAssign : Bool) (d : Doc) : Doc :=
  if ofAssign then
    .group (.ifBreak (t "(" ++ .nest indentWidth (.softline ++ d) ++ .softline ++ t ")") d)
  else d

/-- Whether the superclass of a class is a property read.  Prettier writes
the `extends` of such a class on a line of its own when the header does
not fit; the `extends` of a call, or of a plain name, stays where it is. -/
def heritageIsMember : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. => true
  | .chain _ links =>
      match links.toList.getLast? with
      | some (.dot ..) | some (.privateDot ..) | some (.index ..) => true
      | _ => false
  | _ => false

/-- Whether prettier lays the heritage clauses of a class out as a group
of their own, where they may stand on lines below the class name.  It
does so when the class has more than one of them; when its one superclass
is a property read written with no type arguments, unless the class is
what an assignment writes; and when its one `implements` entry is a
qualified name written with no type arguments. -/
def classHeritageGroupMode (ofAssign : Bool) (heritage : Option MiniClassHeritage)
    (implements_ : List MiniTsHeritage) : Bool :=
  if 1 < (if heritage.isSome then 1 else 0) + implements_.length then true
  else
    match heritage, implements_ with
    | some ⟨he, hargs⟩, _ => !ofAssign && hargs.isEmpty && heritageIsMember he
    | none, [⟨.qualified .., []⟩] => true
    | _, _ => false

/-- A class, given the documents of its decorators, of its heritage clause
and of its members.  `groupMode` says that prettier lays the heritage
clauses out as a group of their own, which is what lets them stand on
lines below the class name once the header does not fit; the brace of a
non-empty body then stands on a line of its own too.  A class laid out
the other way keeps its one clause on the line of the name, however long
that line is: the type parameters break instead. -/
def classDocOf (decorators : List Doc) (isAbstract : Bool) (name : Option NEString)
    (typeParamsDoc : Doc) (groupMode : Bool) (heritage : Doc) (implementsDocs : List Doc)
    (body : List MiniClassElement) (items : List Doc) : Doc :=
  let nameDoc := (match name with | none => Doc.nil | some n => t (" " ++ n.val)) ++ typeParamsDoc
  let bodyDoc := classBodyOf body items
  let clauses : List Doc :=
    (match heritage with | .nil => [] | h => [t "extends " ++ .group h])
      ++ (if implementsDocs.isEmpty then []
          else
            [.group (t "implements"
              ++ .nest indentWidth (.line ++ Doc.joinWith (t "," ++ .line) implementsDocs))])
  -- the clauses of a class laid out the other way keep their line: their
  -- one entry is written where it stands, with no line to break at
  let keptClauses : List Doc :=
    (match heritage with | .nil => [] | h => [t "extends " ++ .group h])
      ++ (if implementsDocs.isEmpty then []
          else [t "implements " ++ Doc.joinWith (t ", ") implementsDocs])
  let headDoc :=
    match clauses with
    | [] => nameDoc ++ t " "
    | _ =>
      if groupMode then
        let flat := nameDoc ++ t " " ++ Doc.joinWith (t " ") clauses ++ t " "
        let broken :=
          nameDoc ++ .nest indentWidth (.hardline ++ Doc.joinWith .hardline clauses)
            ++ (if body.isEmpty then t " " else .hardline)
        if heritage.hasForcedBreak then broken else .condGroup flat broken
      else nameDoc ++ t " " ++ Doc.joinWith (t " ") keptClauses ++ t " "
  classDecoratorsPrefix decorators
    ++ t (if isAbstract then "abstract class" else "class")
    ++ headDoc
    ++ bodyDoc

/-- A function, given the documents of its parameters and of its body.
`hugParams` says that the function is an argument the layout expands in
place, where prettier puts the whole parameter list on one line. -/
def functionDocOf (hugParams isAsync isGen : Bool) (name : Option NEString)
    (typeParams : List MiniTsTypeParam) (typeParamsDoc : Doc) (params : List MiniParam)
    (paramItems : List Doc) (ret : Option MiniTsType) (retDoc : Doc)
    (body : Option (List MiniStatement)) (bodyInner : Doc) : Doc :=
  let paramsDoc :=
    let d := paramListDocOpenOf params paramItems
    if hugParams then Doc.removeLines d else d
  t (if isAsync then "async function" else "function")
    ++ t (if isGen then "*" else "")
    ++ (match name with | none => t " " | some n => t (" " ++ n.val))
    ++ typeParamsDoc ++ signatureDocOf .nil typeParams params (retIsObjectType ret) paramsDoc retDoc
    ++ (match body with
        | none => semiDoc
        | some body => t " " ++ blockDocOf true (bodyIsEmpty body) bodyInner)

/-- A method, given the documents of its name, its parameters and its
body. -/
def methodDocOf (kind : MethodKind) (key : Doc) (optionalDoc typeParamsDoc : Doc)
    (typeParams : List MiniTsTypeParam) (params : List MiniParam) (paramItems : List Doc)
    (ret : Option MiniTsType) (retDoc : Doc)
    (body : Option (List MiniStatement)) (bodyInner : Doc) : Doc :=
  let prefix_ := match kind with
    | .normal => ""
    | .generator => "*"
    | .async => "async "
    | .asyncGenerator => "async *"
    | .get => "get "
    | .set => "set "
  t prefix_ ++ key ++ optionalDoc ++ typeParamsDoc
    ++ signatureOf .nil typeParams params ret paramItems retDoc
    ++ (match body with
        | none => semiDoc
        | some body => t " " ++ blockDocOf true (bodyIsEmpty body) bodyInner)

/-- A declaration written with `keyword`, given the documents of its
declarators.  A declaration of several names, one of which is given a
value, always writes them on lines of their own. -/
def declarationDocOf (keyword : String) (isForInit hasValue : Bool) (docs : List Doc) : Doc :=
  let sep : Doc := if hasValue && !isForInit then .hardline else .line
  match docs with
  | [] => t keyword ++ (if isForInit then .nil else semiDoc)
  | first :: rest =>
    let firstDoc := if rest.isEmpty then first else .nest indentWidth first
    .group (t keyword ++ t " " ++ firstDoc
      ++ .nest indentWidth (Doc.concat (rest.map (fun d => t "," ++ sep ++ d)))
      ++ (if isForInit then .nil else semiDoc))

/-- A `var`, `let` or `const` declaration, given the documents of its
declarators. -/
def declarationDoc (kind : VarKind) (isForInit hasValue : Bool) (docs : List Doc) : Doc :=
  declarationDocOf (varKindText kind) isForInit hasValue docs

/-- Whether the right operand continues a chain of the same logical
operator.  Prettier rebalances `a && (b && c)` into `(a && b) && c` before
it lays it out, so that the operands of such a chain are laid out
together. -/
def rightContinuesLogicalChain (op : BinOp) : MiniExpr → Bool
  | .binary _ rop _ => isLogicalOp op && rop == op
  | _ => false

/-- The first operand of a chain of the same logical operator that leans
to the right: the operand that follows the operator of the chain once it
is rebalanced, and whose shape says whether the line may break in front of
it. -/
def logicalFirstOperand (op : BinOp) : MiniExpr → MiniExpr
  | .binary l rop r =>
      if isLogicalOp op && rop == op then logicalFirstOperand op l else .binary l rop r
  | e => e

/-- Whether the left operand is a chain of the same precedence, to be
flattened into the operator chain of its parent. -/
def shouldFlattenLeft (op : BinOp) : MiniExpr → Bool
  | .binary _ lop _ => shouldFlatten op lop
  | _ => false

/-- What stands in front of the operator of a link of an operator chain: a
space, or, under `experimentalOperatorPosition: "start"`, nothing, since
the line that may break is written after it, in front of the operator
itself.  `inline` says that this is a link prettier never breaks in front
of. -/
def binOpLead (inline : Bool) : Doc :=
  if Options.operatorAtStart && !inline then .nil else t " "

/-- The operator of a link of an operator chain together with the operand
that follows it.  The line the chain breaks at stands after the operator,
or, under `experimentalOperatorPosition: "start"`, in front of it. -/
def binOpTail (op : BinOp) (inline : Bool) (operandDoc : Doc) : Doc :=
  if inline then t (binOpText op) ++ t " " ++ operandDoc
  else if Options.operatorAtStart then .line ++ t (binOpText op) ++ t " " ++ operandDoc
  else t (binOpText op) ++ .line ++ operandDoc

/-- The operator and the right operand of a binary expression, given the
document of the operand. -/
def binaryTailWith (parentKind : BinKind) (insideParens : Bool)
    (l : MiniExpr) (op : BinOp) (r : MiniExpr) (rightDoc : Doc) : List Doc :=
  let nodeKind : BinKind := if isLogicalOp op then .logical else .arith
  -- the operand the line would break in front of is the first one of
  -- the right hand chain, since prettier rebalances the chain
  let inline := shouldInlineLogicalOf op (logicalFirstOperand op r)
  let right : Doc := binOpTail op inline rightDoc
  let shouldGroup :=
    !(insideParens && nodeKind == .logical)
      && parentKind != nodeKind
      && binKind l != nodeKind
      && binKind r != nodeKind
  [binOpLead inline, if shouldGroup then .group right else right]

/-- The kind of the parent of a binary expression in this position. -/
def parentBinKind : Pos → BinKind
  | .binOperand pop _ => if isLogicalOp pop then .logical else .arith
  | _ => .other

/-- A binary expression, laid out according to its position, given the
documents of its operator chain. -/
def binaryLayoutWith (pos : Pos) (l : MiniExpr) (op : BinOp) (r : MiniExpr)
    (parts : List Doc) : Doc :=
  if pos == .ifTest then Doc.concat parts
  -- the operands of a chain of the same logical operator that leans to
  -- the right belong to the chain of the parent: prettier rebalances the
  -- chain, which leaves them neither grouped nor indented again
  else if (match pos with
      | .binOperand pop false => isLogicalOp op && pop == op
      | _ => false) then
    Doc.concat parts
  else
    match pos with
    -- `(\n  a &&\n  b\n).call()`: a binary expression breaks between the
    -- parentheses in the callee of a call, in the operand of a unary
    -- operator and in the object of a `.` access, but not in the object of
    -- a `[ ]` access
    | .callee .. | .unaryArg | .memberObject false .. =>
        .group (.nest indentWidth (.softline ++ Doc.concat parts) ++ .softline)
    | _ =>
      let shouldNotIndent :=
        pos == .returnThrow || pos == .arrowBody || pos == .forHeadPart
          || pos == .forTest
          || (isTernaryPos pos && !ternaryOuterIndents pos)
          || pos == .templateSubst
          -- the `{ }` of an attribute of a JSX element indents already
          || pos == .jsxAttrExpr
      let shouldIndentIfInlining :=
        isAssignRhsPos pos || (match pos with | .propValue false _ => true | _ => false)
      -- the checks are those of the rebalanced chain, whose right hand
      -- operand is the last one of the chain and whose left hand operand
      -- is the rest of it
      let inline := shouldInlineLogicalOf op (logicalLastOperand op r)
      let samePrecedenceSub :=
        rightContinuesLogicalChain op r ||
          match l with
          | .binary _ lop _ => shouldFlatten op lop
          | _ => false
      if shouldNotIndent || (inline && !samePrecedenceSub)
          || (!inline && shouldIndentIfInlining) then
        .group (Doc.concat parts)
      -- a JSX element written as the last operand stands outside the
      -- chain, which lets the operands before it hold one line while the
      -- element is written over several, and is indented again only where
      -- that chain does break
      else if isJsxExpr (logicalLastOperand op r) && parts.length > 1 then
        let init := parts.dropLast
        let chain :=
          Doc.concat (init.take 1) ++ .nest indentWidth (Doc.concat (init.drop 1))
        .group (.groupIndentIfBreak indentWidth chain (parts.getLastD .nil) .nil)
      else
        .group (Doc.concat (parts.take 1) ++ .nest indentWidth (Doc.concat (parts.drop 1)))

/-! ## Modules -/

/-- Whether the item is a string literal statement, which is a directive
where a program starts. -/
def isStringItem : MiniModuleItem → Bool
  | .stmt s => isStringStmt s
  | _ => false

/-- Whether the item is an empty statement, which prettier drops. -/
def isEmptyItem : MiniModuleItem → Bool
  | .stmt s => isEmptyStmt s
  | _ => false

/-- One `name`, `name as alias` or `type name` of an import or export
clause. -/
def specifierDoc (sp : TsSpecifier) : Doc :=
  (if sp.isType then t "type " else Doc.nil) ++ t sp.name.val
    ++ (match sp.alias_ with | none => Doc.nil | some a => t (" as " ++ a.val))

/-- The `{ a, b as c }` of an import or export clause.  A clause of
exactly one named specifier which stands alone -- with no default and no
namespace specifier beside it -- is never broken, however long the line
becomes; every other clause is a list which breaks one specifier to a
line.  `withStandalone` says whether a default or namespace specifier
stands beside these. -/
def specifiersDoc (specs : List TsSpecifier) (withStandalone : Bool := false) : Doc :=
  match specs with
  | [sp] => if withStandalone then sepList "{" "}" true .es5 [specifierDoc sp]
            else
              let pad := if Options.bracketSpacing then " " else ""
              t ("{" ++ pad) ++ specifierDoc sp ++ t (pad ++ "}")
  | _ => sepList "{" "}" true .es5 (specs.map specifierDoc)

/-- One attribute of an `import("mod", { with: … })` type, written as the
property of an object literal it is there.  A key whose printed text is
short keeps its value on the line of the colon however long the line
becomes; a longer key breaks after the colon, the way any property whose
value is a string does.  (The attributes of an `import` *declaration* are
not written this way: prettier prints those flat, and they are built by
`importAttrsDoc` below.) -/
def importAttrItemDoc (quoteAll : Bool) (a : ImportAttr) : Doc :=
  let keyText := if !quoteAll && isIdentifierName a.key then a.key else strLit a.key
  let short := Doc.stringWidth keyText < tabWidth + 3
  assignmentDocOf (if short then .neverBreakAfterOperator else .breakAfterOperator)
    (t keyText) ":" (t (strLit a.value))

/-- The `with { type: "json" }` of an import; nothing when there is no
attribute.  The one attribute `type`, whose value is a string, is the one
every engine knows, and prettier keeps it on the line of the import
however long that line becomes; any other list of attributes is laid out
as an object literal is. -/
def importAttrsDoc (attrs : List ImportAttr) : Doc :=
  if attrs.isEmpty then Doc.nil
  else
    -- the attributes are names of an object as far as `quoteProps` is
    -- concerned: one of them that cannot lose its quotes quotes them all
    let quoteAll := Options.quoteProps == .consistent
      && attrs.any fun a => !isIdentifierName a.key && !isSimpleNumberString a.key
    let items := attrs.map fun a =>
      t ((if !quoteAll && isIdentifierName a.key then a.key else strLit a.key)
        ++ ": " ++ strLit a.value)
    let listDoc := sepList "{" "}" true .es5 items
    let isTypeOnly := match attrs with | [a] => a.key == "type" | _ => false
    t " with " ++ (if isTypeOnly then Doc.removeLines listDoc else listDoc)

/-- The arguments of an `import("mod", { with: { type: "json" } })` type:
the module, and the import attributes written as the object they are.  An
empty list of attributes is no second argument at all.  The two arguments
are laid out the way the arguments of a call are — the object hugs the
line of the import, and stands on lines of its own once it no longer fits
there — except that they take no trailing comma. -/
def importTypeArgsDoc (mod : String) (attrs : List ImportAttr) : Doc :=
  let modDoc := t (strLit mod)
  if attrs.isEmpty then t "(" ++ modDoc ++ t ")"
  else
    -- the attributes are names of an object as far as `quoteProps` is
    -- concerned: one of them that cannot lose its quotes quotes them all
    let quoteAll := Options.quoteProps == .consistent
      && attrs.any fun a => !isIdentifierName a.key && !isSimpleNumberString a.key
    let items := attrs.map (importAttrItemDoc quoteAll)
    let objDoc := sepList "{" "}" true .es5 [t "with: " ++ sepList "{" "}" true .es5 items]
    argumentsDocOf .never false false false false true [modDoc, objDoc] [] [modDoc, objDoc]

/-- An `import` declaration. -/
def importDoc : MiniImportDeclaration → Doc
  | .bare mod attrs =>
      t ("import " ++ strLit mod.val) ++ importAttrsDoc attrs ++ semiDoc
  | .equals isExport name rhs =>
      t (if isExport then "export import " else "import ") ++ t (name.val ++ " = ")
        ++ (match rhs with
            | .require mod => t ("require(" ++ strLit mod ++ ")")
            | .entity e => tsEntityDoc e)
        ++ semiDoc
  | .clause c =>
      let standalone : List Doc :=
        (match c.default_ with | none => [] | some d => [t d.val])
        ++ (match c.namespace_ with | none => [] | some n => [t ("* as " ++ n.val)])
      let parts : List Doc :=
        standalone
        -- an empty list of named imports is written out only when it is
        -- the whole clause: `import d, {} from "m"` binds `d` alone
        ++ (match c.named with
            | none => []
            | some [] => if standalone.isEmpty then [specifiersDoc []] else []
            | some specs => [specifiersDoc specs !standalone.isEmpty])
      t "import " ++ (if c.isType then t "type " else Doc.nil) ++ Doc.joinWith (t ", ") parts
        ++ t (" from " ++ strLit c.mod.val) ++ importAttrsDoc c.attrs ++ semiDoc

/-! ## The shapes of types prettier's printers look at -/

/-- The place a type stands in, as far as a conditional type there is
concerned: prettier writes the conditional types of a chain, which stand
in the `:` branch of the one before them, as one group, and parenthesises
one which stands in a `?` branch. -/
inductive TsTypeMode where
  /-- Anywhere but in a branch of a conditional type. -/
  | normal
  /-- The `?` branch of a conditional type. -/
  | condBranch
  /-- The `:` branch of a conditional type. -/
  | condAlt
  /-- The `extends` clause of a conditional type, where a function type
  and a constructor type need no parentheses of their own. -/
  | condExtends
  /-- The type a conditional type checks. -/
  | condCheck
deriving BEq, Inhabited

/-- The names TypeScript reads as a keyword type rather than as the name
of a type declared elsewhere. -/
def tsKeywordTypeNames : List String :=
  ["any", "bigint", "boolean", "false", "never", "null", "number", "object",
    "string", "symbol", "true", "undefined", "unknown", "void"]

/-- Whether the type is one prettier counts as an object type, which its
intersection printer keeps on the line of the `&` before it. -/
def tsIsObjectType : MiniTsType → Bool
  | .objectType _ | .mapped .. => true
  | _ => false

/-- Whether the type names a type declared elsewhere, rather than being
one of the keyword types. -/
def tsIsTypeRef : MiniTsType → Bool
  | .ref (.ident n) _ => !tsKeywordTypeNames.contains n.val
  | .ref (.qualified ..) _ => true
  | _ => false

/-- Whether the type is `void` or `null`. -/
def tsIsVoidOrNull : MiniTsType → Bool
  | .ref (.ident n) [] => n.val == "void" || n.val == "null"
  | _ => false

/-- Whether the members seen so far are ones prettier keeps on one line:
one object type or one named type, and `void` or `null` everywhere else.
`seen` records that the one object or named type has been met. -/
def tsUnionHugAux (seen : Bool) : List MiniTsType → Bool
  | [] => seen
  | ty :: rest =>
      if tsIsObjectType ty || tsIsTypeRef ty then
        (!seen && tsUnionHugAux true rest)
      else if tsIsVoidOrNull ty then tsUnionHugAux seen rest
      else false

/-- Whether prettier writes the union on one line however long it is, as
it does with `{ a: string } | null`. -/
def tsUnionShouldHug (types : List MiniTsType) : Bool := tsUnionHugAux false types

/-- The members of an intersection after the first, following prettier:
two object types stand on one line, `{ … } & { … }`; two other types are
written with the `&` at the end of the line and the member after it
indented; and where the two kinds meet, every member after the second is
indented too.  `prevObject` says that the member before this one is an
object type, `indented` that a member of the first kind is indented, and
`idx` counts the members. -/
def tsIntersectionAux (prevObject indented : Bool) (idx : Nat) :
    List (Bool × Doc) → Doc
  | [] => Doc.nil
  | (cur, d) :: rest =>
      if idx == 0 then d ++ tsIntersectionAux cur indented 1 rest
      else if prevObject && cur then
        t " & " ++ (if indented then .nest indentWidth d else d)
          ++ tsIntersectionAux cur indented (idx + 1) rest
      else if !prevObject && !cur then
        .nest indentWidth
            (if Options.operatorAtStart then .line ++ t "& " ++ d else t " &" ++ .line ++ d)
          ++ tsIntersectionAux cur indented (idx + 1) rest
      else
        t " & " ++ (if 1 < idx then .nest indentWidth d else d)
          ++ tsIntersectionAux cur (indented || 1 < idx) (idx + 1) rest

/-- The members of an intersection, `A & B`. -/
def tsIntersectionAssemble (parts : List (Bool × Doc)) : Doc :=
  tsIntersectionAux false false 0 parts

/-- The members of a union, `A | B`, each on a line of its own with a
leading `|` when they break. -/
def tsUnionInnerDoc (items : List Doc) : Doc :=
  .group (Doc.ifBreak (t "| ") .nil ++ Doc.joinWith (.line ++ t "| ") items)

/-! ## The printing context -/

/-- Whether the expression applies the `in` operator. -/
def isInOperator : MiniExpr → Bool
  | .binary _ .inOp _ => true
  | _ => false

/-- Whether the type is a simple one in prettier's sense: a name written
without type arguments, a predefined type, or a literal type. -/
def tsTypeIsSimple : MiniTsType → Bool
  | .ref _ [] => true
  | .this => true
  | .strLit _ | .numLit _ | .negNumLit _ => true
  | .templateLit .. => true
  | _ => false

/-- Whether prettier hugs the type when it stands alone between the angle
brackets of a list of type arguments, writing `Foo<{` and `}>` rather than
breaking the brackets around it: it does so for a simple type, for an
object type, and for a union of an object type with `void` or `null`. -/
def tsShouldHugType : MiniTsType → Bool
  | .objectType _ | .mapped .. => true
  | .union types => tsUnionShouldHug types
  | ty => tsTypeIsSimple ty

/-- What the printer has to know about the place the tree it walks stands
in.  The head of a `for (;;)` is read with the `in` operator ruled out, so
prettier parenthesises every `in` written anywhere inside it, however deep;
`inForInit` says that this is such a place.  Since the printer of a head is
the very printer being defined, it is passed here as `forInit`. -/
structure PrintCtx where
  /-- Whether this stands inside the first clause of a `for (;;)`. -/
  inForInit : Bool
  /-- Whether to write the parentheses which say what the text means
  where TypeScript would otherwise read it back as another tree: around
  an instantiation expression, `f<T>`, which is read as a pair of
  comparisons wherever the token after it does not rule that out, and
  around the test of a `case`, whose `:` the parser may take for the one
  of the clause.  Prettier writes none of them, and neither does the
  printer in its ordinary mode: the mode is there so that a text holding
  the tree the printer means can be handed to prettier and its answer
  compared with the ordinary output. -/
  guarded : Bool := false
  /-- How the first clause of a `for (;;)` is printed. -/
  forInit : MiniForInit → Doc

section

variable (ctx : PrintCtx)

-- the printer is one large mutual block; elaborating it takes more than
-- the default budget
set_option maxHeartbeats 4000000 in
mutual

/-- Whether the expression has to be parenthesised in this position.  An
`in` operator in the head of a `for (;;)` always is. -/
def needsParensC (pos : Pos) (e : MiniExpr) : Bool :=
  needsParens pos e || (ctx.inForInit && isInOperator e)

/-- An expression in position `pos`, given the document it prints as. -/
def inPosC (pos : Pos) (e : MiniExpr) (d : Doc) : Doc := parenIfExpr (needsParensC pos e) e d

/-- An expression in position `pos`, where `atStart` says what it is the
leftmost part of, so that an object literal, a function or a class
expression there needs parentheses. -/
def inPosStartC (atStart : StartCtx) (pos : Pos) (e : MiniExpr) (d : Doc) : Doc :=
  parenIfExpr (needsParensC pos e || cannotStartWith atStart pos e) e d

/-- The statements of one `case` of a `switch`, given their documents. -/
def caseBodyWith (body : List MiniStatement) (docs : List Doc) : Doc :=
  match body.filter (fun s => !isEmptyStmt s) with
  | [] => Doc.nil
  | [.block _] => t " " ++ Doc.joinWith .hardline docs
  | _ => .nest indentWidth (.hardline ++ Doc.joinWith .hardline docs)

/-- The condition of an `if`, a `while` or a `do ... while`, given the
document of the condition itself. -/
def conditionWith (e : MiniExpr) (d : Doc) : Doc :=
  let inline :=
    match e with
    -- `if (!(a || b))` is kept as it is
    | .unary .not (.binary _ op _) => isLogicalOp op
    | .unary .not (.unary .not (.binary _ op _)) => isLogicalOp op
    | _ => false
  if inline then d else .group (.nest indentWidth (.softline ++ d) ++ .softline)

/-- The body attached to the head of a statement, given its document. -/
def bodyClauseWith (s : MiniStatement) (d : Doc) : Doc :=
  clauseDoc (isBlockStmt s) (isEmptyStmt s) d

/-- The argument of a `return` or a `throw`, given its document. -/
def returnArgWith (e : MiniExpr) (d : Doc) : Doc :=
  match e with
  -- under `experimentalTernaries` a chain of conditionals keeps the
  -- parentheses of a broken operator chain
  | .ternary _ a b =>
      if Options.experimentalTernaries
          && ((match a with | .ternary .. => true | _ => false)
              || (match b with | .ternary .. => true | _ => false)) then
        .group (.ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d)
          ++ .softline ++ .ifBreak (t ")") .nil)
      else d
  | .binary .. =>
      .group (.ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d)
        ++ .softline ++ .ifBreak (t ")") .nil)
  | _ => d

-- ### Types

/-- The documents of a list of types, each binding at least as tight as
`minPrec`. -/
def tsTypeDocs (mode : TsTypeMode) (indentUnion : Bool) (minPrec : Nat) :
    List MiniTsType → List Doc
  | [] => []
  | ty :: rest =>
      tsTypeDoc mode indentUnion minPrec ty :: tsTypeDocs mode indentUnion minPrec rest

/-- The members of a union, each indented by two columns of its own, the
way prettier aligns them under the `|` that introduces them. -/
def tsUnionMemberDocs : List MiniTsType → List Doc
  | [] => []
  -- an intersection written as a member of a union keeps parentheses of
  -- its own, which is why the members are written as if they bound
  -- tighter than an intersection does
  | ty :: rest => .align 2 (tsTypeDoc .normal false 3 ty) :: tsUnionMemberDocs rest

/-- The type arguments of a name, `<A, B>`; they take no trailing comma
when they break. -/
def tsTypeArgsDoc : List MiniTsType → Doc
  | [] => Doc.nil
  -- a lone argument that prettier hugs is written between the brackets
  -- themselves, so that it may break while they stay where they are
  | [ty] =>
      if tsShouldHugType ty then t "<" ++ tsTypeDoc .normal false 0 ty ++ t ">"
      else sepList "<" ">" false .never [tsTypeDoc .normal false 0 ty]
  | ty :: rest => sepList "<" ">" false .never (tsTypeDoc .normal false 0 ty :: tsTypeDocs .normal false 0 rest)

/-- One type parameter, `const in out T extends C = D`.  The constraint
and the default are laid out the way prettier lays the right hand side of
an assignment out: each of them keeps the line of its operator while its
first line fits there, and stands indented below it otherwise. -/
def tsTypeParamDoc : MiniTsTypeParam → Doc
  | ⟨isConst, variance, name, constraint, default_⟩ =>
    .group ((if isConst then t "const " else Doc.nil)
      ++ (match variance with | none => Doc.nil | some v => t (v.text ++ " "))
      ++ t name.val
      ++ (match constraint with
          | none => Doc.nil
          -- a conditional type written as the constraint of a type
          -- parameter keeps parentheses of its own
          | some c =>
            t " extends"
              ++ .fluidLine indentWidth
                  (tsTypeDoc .normal true (match c with | .conditional .. => 1 | _ => 0) c))
      ++ (match default_ with
          | none => Doc.nil
          | some d => t " =" ++ .fluidLine indentWidth (tsTypeDoc .normal true 0 d)))

def tsTypeParamDocs : List MiniTsTypeParam → List Doc
  | [] => []
  | tp :: rest => tsTypeParamDoc tp :: tsTypeParamDocs rest

/-- The type parameters of a declaration, `<T extends C>`; they take a
trailing comma when they break.  `tsxComma` writes the trailing comma
that the one type parameter of an arrow function keeps, since `<T>` alone
would open an element in a file read with JSX enabled. -/
def tsTypeParamsDocOf (tsxComma : Bool) : List MiniTsTypeParam → Doc
  | [] => Doc.nil
  | tp :: rest =>
      let items := tsTypeParamDoc tp :: tsTypeParamDocs rest
      -- in a file read with JSX enabled, `<T>` alone opens an element, so
      -- the one type parameter of an arrow function keeps a comma of its
      -- own, written whether the list breaks or not.  A constraint is
      -- enough to tell the two apart, so a constrained parameter takes
      -- the ordinary layout; a default is not.
      let bare := match tp with | ⟨_, _, _, none, _⟩ => true | _ => false
      if tsxComma && rest.isEmpty && bare then
        .group (t "<" ++ .nest indentWidth (.softline ++ tsTypeParamDoc tp ++ t ",")
          ++ .softline ++ t ">")
      else sepList "<" ">" false .es5 items

/-- A type annotation, `: T`; nothing when there is none. -/
def tsAnnotation : Option MiniTsType → Doc
  | none => Doc.nil
  | some ty => t ": " ++ tsTypeDoc .normal true 0 ty

/-- The return type of an arrow function.  A function type written there
keeps parentheses of its own: without them the `=>` of the type would be
read as the one of the arrow.  A constructor type, which starts with
`new`, needs none. -/
def tsArrowAnnotation : Option MiniTsType → Doc
  | none => Doc.nil
  | some ty =>
      let d := tsTypeDoc .normal true 0 ty
      match ty with
      | .fn .. => t ": (" ++ d ++ t ")"
      | _ => t ": " ++ d

/-- The members of an object type, `{ a: A; b(): B }`, without the group
that lays them out: it is what prettier writes for the object type of the
one parameter of a function it hugs, where the parameter list itself is
the group that decides whether the members break. -/
def tsObjectTypeContent (items : List Doc) : Doc :=
  t "{" ++ .nest indentWidth
      (braceLine ++ Doc.joinWith (tsMemberSep ++ .line) items ++ tsMemberTrailer)
    ++ braceLine ++ t "}"

/-- The members of an object type, `{ a: A; b(): B }`. -/
def tsObjectTypeDoc (items : List Doc) : Doc :=
  if items.isEmpty then t "{}"
  else .group (tsObjectTypeContent items)

/-- The members of an interface, which always stand on lines of their
own. -/
def tsInterfaceBodyDoc (items : List Doc) : Doc :=
  if items.isEmpty then t "{}"
  else
    t "{" ++ .nest indentWidth
        (.hardline ++ Doc.joinWith (tsBrokenMemberSep ++ .hardline) items ++ tsBrokenMemberSep)
      ++ .hardline ++ t "}"

/-- The members of an intersection, each with whether it is an object
type. -/
def tsIntersectionParts : List MiniTsType → List (Bool × Doc)
  | [] => []
  | ty :: rest => (tsIsObjectType ty, tsTypeDoc .normal false 3 ty) :: tsIntersectionParts rest

/-- A type expression, parenthesised when it binds less tight than the
place it stands in asks for. -/
def tsTypeDoc (mode : TsTypeMode) (indentUnion : Bool) (minPrec : Nat) : MiniTsType → Doc
  | .ref name args => tsEntityDoc name ++ tsTypeArgsDoc args
  | .this => t "this"
  | .strLit v => t (strLit v)
  | .numLit n => t n.render
  | .negNumLit n => t ("-" ++ n.render)
  | .array elem => parenIf (4 < minPrec) (tsTypeDoc .normal false 4 elem ++ t "[]")
  | .indexed obj idx =>
      parenIf (4 < minPrec) (tsTypeDoc .normal false 4 obj ++ t "[" ++ tsTypeDoc .normal true 0 idx ++ t "]")
  | .union types =>
      if tsUnionShouldHug types then
        parenIf (1 < minPrec) (Doc.joinWith (t " | ") (tsTypeDocs .normal false 2 types))
      else
        let inner := tsUnionInnerDoc (tsUnionMemberDocs types)
        -- a union in parentheses puts them on lines of their own when it
        -- breaks, as in `(\n  | A\n  | B\n)[]`
        if 1 < minPrec then
          t "(" ++ .group (.nest indentWidth (.softline ++ inner) ++ .softline) ++ t ")"
        else if indentUnion then .group (.nest indentWidth (.softline ++ inner))
        else inner
  | .intersection types =>
      parenIf (2 < minPrec) (.group (tsIntersectionAssemble (tsIntersectionParts types)))
  | .fn tps params ret =>
      parenIf (0 < minPrec && mode != .condExtends)
        (signatureOf (tsTypeParamsDocOf false tps) tps params (some ret) (paramDocs params)
          (t " => " ++ tsTypeDoc .normal true 0 ret))
  | .ctor isAbstract tps params ret =>
      parenIf (0 < minPrec && mode != .condExtends)
        (t (if isAbstract then "abstract new " else "new ")
          ++ signatureOf (tsTypeParamsDocOf false tps) tps params (some ret) (paramDocs params)
              (t " => " ++ tsTypeDoc .normal true 0 ret))
  | .typeQuery name args =>
      parenIf (3 < minPrec) (t "typeof " ++ tsEntityDoc name ++ tsTypeArgsDoc args)
  -- `keyof (readonly A[])`: a `readonly` operand of a `keyof` keeps
  -- parentheses of its own
  | .keyof ty =>
      parenIf (3 < minPrec)
        (t "keyof "
          ++ tsTypeDoc .normal false
              (match ty with
                -- a type operator written as the operand of a `keyof`
                -- keeps parentheses of its own
                | .readonlyOp _ | .keyof _ | .uniqueSymbol => 4
                | _ => 3) ty)
  | .readonlyOp ty => parenIf (3 < minPrec) (t "readonly " ++ tsTypeDoc .normal false 3 ty)
  | .uniqueSymbol => parenIf (3 < minPrec) (t "unique symbol")
  | .infer_ n none => parenIf (3 < minPrec) (t ("infer " ++ n.val))
  -- the constraint of an `infer` is laid out the way the constraint of a
  -- type parameter is: it keeps the line of the `extends` while its first
  -- line fits there, and stands indented below it otherwise
  | .infer_ n (some c) =>
      parenIf (3 < minPrec)
        (.group (t ("infer " ++ n.val ++ " extends")
          ++ .fluidLine indentWidth (tsTypeDoc .normal false 1 c)))
  | .conditional check ext trueType falseType =>
      if Options.experimentalTernaries then
        -- prettier lays a conditional type out the way it lays a
        -- conditional expression out under the option: the `?` stands at
        -- the end of the line of the `extends`, and the chain reads as a
        -- list of cases
        let consIsCond := match trueType with | .conditional .. => true | _ => false
        let altIsCond := match falseType with | .conditional .. => true | _ => false
        let parentIsCond := mode != .normal
        let inTest := mode == .condCheck || mode == .condExtends
        let chainTail := altIsCond || mode == .condAlt
        let bigTabs := 2 < tabWidth || Options.useTabs
        -- the test of a conditional type is grouped unless the type
        -- stands in a branch of a conditional type of its own
        let groupTest := chainTail || !parentIsCond
        let wrapParens (d : Doc) : Doc :=
          .ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d) ++ .softline
            ++ .ifBreak (t ")") .nil
        -- the `extends` type stands between parentheses of its own once
        -- it no longer holds the line; a conditional type and a mapped
        -- type are written there as they are
        let extDoc := tsTypeDoc .condExtends true 1 ext
        let extPart : Doc :=
          match ext with
          | .conditional .. | .mapped .. => extDoc
          | _ => .group (wrapParens extDoc)
        let testPart : Doc :=
          .groupId 0 (tsTypeDoc .condCheck true 1 check ++ t " extends " ++ extPart ++ t " ?")
        let consPart : Doc :=
          .nest indentWidth
            ((if consIsCond then Doc.hardline else Doc.line)
              ++ tsTypeDoc .condBranch false 0 trueType)
        let head : Doc :=
          if groupTest then
            .groupId 1 (testPart
              ++ (if chainTail then consPart else .ifBreakOf 0 consPart (.group consPart)))
          else testPart ++ consPart
        let altDoc := tsTypeDoc .condAlt false 0 falseType
        let sep : Doc := if altIsCond then .hardline else .line
        let pad : Doc :=
          if altIsCond || !bigTabs then t " "
          else
            let filler := t (if Options.useTabs then "\t" else String.pushn "" ' ' (tabWidth - 1))
            if groupTest then
              .ifBreakOf 1 filler (.ifBreak (if chainTail then t " " else filler) (t " "))
            else .ifBreak filler (t " ")
        let altPart : Doc := if altIsCond then altDoc else .group (.nest indentWidth altDoc)
        -- a chain of conditional types always breaks
        let forced := consIsCond || altIsCond
        let body : Doc :=
          head ++ sep ++ t ":" ++ pad ++ altPart ++ (if forced then Doc.breakParent else .nil)
        Doc.scopeIds
          (if inTest then
            -- a conditional type written as the check or as the `extends`
            -- type of another one stands on lines of its own inside the
            -- parentheses it takes there
            if 0 < minPrec then
              t "(" ++ .group (.nest indentWidth (.softline ++ body) ++ .softline) ++ t ")"
            else .group (.nest indentWidth (.softline ++ body))
          else if !parentIsCond then parenIf (0 < minPrec) (.group body)
          else body)
      else
      -- the conditional types of a chain, each of which stands in the `:`
      -- branch of the one before it, are laid out as one group, with each
      -- link two columns further in than the one before it; a conditional
      -- type in a `?` branch is parenthesised and starts a chain of its own
      -- a union written as the type the conditional checks stands on
      -- lines of its own, indented, the way a union on the right of an
      -- `=` does
      let head := tsTypeDoc .condCheck true 1 check ++ t " extends "
        ++ tsTypeDoc .condExtends true 1 ext
      -- a branch stands two columns further in, written as a step of its
      -- own where the indentation is tabs
      let branch (d : Doc) : Doc := if Options.useTabs then Doc.nest indentWidth d else Doc.align 2 d
      -- the branches of a conditional written in the `?` branch of one
      -- stand `tabWidth - 2` columns further in; with tabs they stand
      -- where they are
      let chainAlign (d : Doc) : Doc :=
        if mode == .condBranch && !Options.useTabs && 2 < tabWidth then Doc.align (tabWidth - 2) d
        else d
      let branches := chainAlign (.line ++ t "? "
        ++ branch (tsTypeDoc .condBranch false 0 trueType)
        ++ .line ++ t ": " ++ branch (tsTypeDoc .condAlt false 0 falseType))
      match mode with
      | .condAlt => Doc.align 2 head ++ branches
      -- a conditional type in a `?` branch is written as part of the
      -- chain around it, and takes parentheses only while that chain
      -- stands on one line
      -- the branches stand two columns in from the `?` of the chain
      -- around it, which the `?` itself is already indented by
      | .condBranch =>
          .ifBreak .nil (t "(") ++ head ++ branches ++ .ifBreak .nil (t ")")
      | .normal | .condExtends | .condCheck =>
          let inner := .group (head ++ .nest indentWidth branches)
          -- a conditional type written as the check or as the `extends`
          -- type of another one stands on lines of its own inside the
          -- parentheses it takes there
          if 0 < minPrec then
            if mode == .condExtends || mode == .condCheck then
              t "(" ++ .group (.nest indentWidth (.softline ++ inner) ++ .softline) ++ t ")"
            else parens inner
          else inner
  | .objectType members => tsObjectTypeDoc (tsTypeMemberDocsOf (quoteAllTypeMembers members) members)
  | .mapped readonlyMod key constraint as_ optionalMod value =>
      let modDoc (m : Option TsMappedMod) (text : String) : Doc :=
        match m with
        | none => Doc.nil
        | some .keep => t text
        | some .add => t ("+" ++ text)
        | some .remove => t ("-" ++ text)
      let inner :=
        modDoc readonlyMod "readonly "
          -- the key of a mapped type takes lines of its own when it is
          -- too long to stand between the brackets on one line
          ++ .group (t "[" ++ .nest indentWidth (.softline
                ++ t (key.val ++ " in ") ++ tsTypeDoc .normal true 0 constraint
                ++ (match as_ with
                    | none => Doc.nil
                    | some a => t " as " ++ tsTypeDoc .normal true 0 a))
              ++ .softline ++ t "]")
          ++ modDoc optionalMod "?"
          ++ (match value with | none => Doc.nil | some v => t ": " ++ tsTypeDoc .normal true 0 v)
      .group (t "{" ++ .nest indentWidth (braceLine ++ inner ++ tsMemberTrailer)
        ++ braceLine ++ t "}")
  | .tuple elems =>
      sepList "[" "]" false .es5 (tsTupleElemDocs (1 < elems.length) elems)
  | .templateLit head parts =>
      t "`" ++ t (encodeTemplateText head) ++ tsTemplatePartsDoc parts ++ t "`"
  | .importType isTypeof mod attrs qualifier args =>
      parenIf (isTypeof && 3 < minPrec)
        ((if isTypeof then t "typeof " else Doc.nil)
          ++ t "import" ++ importTypeArgsDoc mod attrs
          ++ (match qualifier with | none => Doc.nil | some q => t "." ++ tsEntityDoc q)
          ++ tsTypeArgsDoc args)
  | .predicate asserts param type =>
      parenIf (0 < minPrec)
        ((if asserts then t "asserts " else Doc.nil) ++ t param.val
          ++ (match type with | none => Doc.nil | some ty => t " is " ++ tsTypeDoc .normal true 0 ty))

/-- The `${…}` substitutions of a template literal type, and the text
between them.  Prettier writes what stands between the braces on one
line, however long it is, so every line inside it is written flat. -/
def tsTemplatePartsDoc : List MiniTsTemplatePart → Doc
  | [] => Doc.nil
  | ⟨ty, suffix⟩ :: rest =>
      t "${" ++ Doc.removeLines (tsTypeDoc .normal true 0 ty) ++ t "}"
        ++ t (encodeTemplateText suffix) ++ tsTemplatePartsDoc rest

/-- One element of a tuple type.  `multi` says that the tuple holds more
than one element, where prettier parenthesises a union that breaks. -/
def tsTupleElemDoc (multi : Bool) : MiniTsTupleElem → Doc
  | .elem (.union types) =>
      if tsUnionShouldHug types then
        Doc.joinWith (t " | ") (tsTypeDocs .normal false 2 types)
      else
        let inner := tsUnionInnerDoc (tsUnionMemberDocs types)
        -- a union that breaks inside a tuple of more than one element is
        -- parenthesised
        if multi then
          .group (.nest indentWidth (.ifBreak (t "(" ++ .softline) .nil ++ inner)
            ++ .softline ++ .ifBreak (t ")") .nil)
        else inner
  | .elem ty => tsTypeDoc .normal false 0 ty
  -- prettier writes the `?` of an optional element after the type as it
  -- stands, with no parentheses of its own: `[typeof a?]`, `[a | b?]`.
  -- A union takes the layout it takes as an element, with the `?` after
  -- its last member, inside the parentheses a broken union is given.
  | .optional (.union types) =>
      if tsUnionShouldHug types then
        Doc.joinWith (t " | ") (tsTypeDocs .normal false 2 types) ++ t "?"
      else
        let inner := tsUnionInnerDoc (tsUnionMemberDocs types) ++ t "?"
        if multi then
          .group (.nest indentWidth (.ifBreak (t "(" ++ .softline) .nil ++ inner)
            ++ .softline ++ .ifBreak (t ")") .nil)
        else inner
  | .optional ty => tsTypeDoc .normal false 0 ty ++ t "?"
  | .rest ty => t "..." ++ tsTypeDoc .normal true 0 ty
  | .named name isOptional isRest ty =>
      (if isRest then t "..." else Doc.nil) ++ t name.val
        ++ (if isOptional then t "?" else Doc.nil) ++ t ": " ++ tsTypeDoc .normal true 0 ty

def tsTupleElemDocs (multi : Bool) : List MiniTsTupleElem → List Doc
  | [] => []
  | e :: rest => tsTupleElemDoc multi e :: tsTupleElemDocs multi rest

/-- One member of an interface, or of an object type. -/
def tsTypeMemberDoc (quoteAll : Bool) : MiniTsTypeMember → Doc
  | .property isReadonly key isOptional type =>
      (if isReadonly then t "readonly " else Doc.nil) ++ propertyKeyDoc quoteAll key
        ++ (if isOptional then t "?" else Doc.nil) ++ tsAnnotation type
  | .method kind key isOptional tps params ret =>
      t (match kind with | .normal => "" | .get => "get " | .set => "set ")
        ++ propertyKeyDoc quoteAll key ++ (if isOptional then t "?" else Doc.nil)
        ++ signatureOf (tsTypeParamsDocOf false tps) tps params ret (paramDocs params)
            (tsAnnotation ret)
  | .callSig tps params ret =>
      signatureOf (tsTypeParamsDocOf false tps) tps params ret (paramDocs params)
        (tsAnnotation ret)
  | .ctorSig tps params ret =>
      t "new " ++ signatureOf (tsTypeParamsDocOf false tps) tps params ret (paramDocs params)
        (tsAnnotation ret)
  | .indexSig isReadonly name keyType valueType =>
      (if isReadonly then t "readonly " else Doc.nil)
        -- the brackets of an index signature break around what they hold
        ++ t "[" ++ .group (.nest indentWidth
              (.softline ++ t (name.val ++ ": ") ++ tsTypeDoc .normal true 0 keyType)
            ++ .softline)
        ++ t "]" ++ t ": " ++ tsTypeDoc .normal true 0 valueType

def tsTypeMemberDocsOf (quoteAll : Bool) : List MiniTsTypeMember → List Doc
  | [] => []
  | m :: rest => tsTypeMemberDoc quoteAll m :: tsTypeMemberDocsOf quoteAll rest

/-- One entry of an `extends` clause of an interface, or of the
`implements` clause of a class. -/
def tsHeritageDoc : MiniTsHeritage → Doc
  | ⟨name, args⟩ => tsEntityDoc name ++ tsTypeArgsDoc args

def tsHeritageDocs : List MiniTsHeritage → List Doc
  | [] => []
  | h :: rest => tsHeritageDoc h :: tsHeritageDocs rest

/-- One member of an `enum`. -/
def tsEnumMemberDoc (quoteAll : Bool) : MiniTsEnumMember → Doc
  | ⟨key, init⟩ =>
    propertyKeyDoc quoteAll key
      ++ (match init with
          | none => Doc.nil
          | some e => t " = " ++ inPosC .arg e (exprCore .none .arg e))

def tsEnumMemberDocsOf (quoteAll : Bool) : List MiniTsEnumMember → List Doc
  | [] => []
  | m :: rest => tsEnumMemberDoc quoteAll m :: tsEnumMemberDocsOf quoteAll rest

/-- An expression, without the parentheses its position may require. -/
def exprCore (atStart : StartCtx) (pos : Pos) : MiniExpr → Doc
  | .ident n => t n.val
  | .number n => t n.render
  | .string v => t (strLit v)
  | .regex r => t r.render
  | .null => t "null"
  | .true_ => t "true"
  | .false_ => t "false"
  | .this => t "this"
  | .newTarget => t "new.target"
  | .importMeta => t "import.meta"
  | .privateName n => t ("#" ++ n.val)
  | .superDot n => t ("super." ++ n.val)
  | .superIndex i =>
      t "super"
        ++ indexLookupDoc (isNumericLit i) (inPosC .computed i (exprCore .none .computed i))
  | .superCall args =>
      t "super" ++ argumentsDocMaybeOpen (isLongCurriedCall pos args.length)
        (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
        (canHugLastArg args) (argDocs .none args) (argHugFirstDocs .none false args) (argHugDocs .none false args)
  | .array els => arrayDocOf els (arrayItemDocs els)
  | .object props => sepList "{" "}" true .es5 (propertyDocsOf (quoteAllProps props) props)
  | .assign l op r =>
      -- the right hand side of an assignment that is not a statement of
      -- its own is a link of a chain of assignments; one of an assignment
      -- whose left hand side is not a plain identifier keeps its member
      -- accesses on the line of their object
      let leftIsIdent := match l with | .ident _ => true | _ => false
      let grandparentIsStatement := match pos with | .assignRhs n _ _ _ => !n | _ => false
      let leftDoc := inPosStartC atStart .assignTarget l (exprCore atStart .assignTarget l)
      let layout :=
        chooseAssignLayout true (isAssignRhsPos pos) grandparentIsStatement false
          (Doc.canBreak leftDoc) false r
      let rhsPos : Pos :=
        .assignRhs (pos != .statement) (!leftIsIdent) true (layout == .chainTailArrowChain)
      assignmentDocOf layout
        leftDoc (" " ++ assignOpText op) (inPosC rhsPos r (exprCore .none rhsPos r))
  | .assignPattern l r =>
      let leftDoc := assignTargetPatternDoc l
      let grandparentIsStatement := match pos with | .assignRhs n _ _ _ => !n | _ => false
      let layout :=
        chooseAssignLayout true (isAssignRhsPos pos) grandparentIsStatement
          (patternIsComplexDestructuring l) (Doc.canBreak leftDoc) false r
      let rhsPos : Pos :=
        .assignRhs (pos != .statement) true true (layout == .chainTailArrowChain)
      assignmentDocOf layout leftDoc " =" (inPosC rhsPos r (exprCore .none rhsPos r))
  | .await e =>
      let inner := t "await " ++ inPosC .awaitArg e (exprCore .awaitArgument .awaitArg e)
      if awaitBreaksInParens pos then
        -- the parentheses break with the line the `await` stands on; when
        -- the `await` itself opens the operand of another one, prettier
        -- leaves the decision to the line that holds them both
        let parts := Doc.nest indentWidth (.softline ++ inner) ++ .softline
        if atStart == .awaitArgument then parts else .group parts
      else inner
  | .call f typeArgs args =>
      -- a `require` of a module, a module definition and a call of a test
      -- framework keep their arguments on the line of the call
      let parentIsTest := pos == .testCallArg
      let stay := callArgsStayOnLine (pos == .statement) parentIsTest f args
      -- an argument of a call written directly in a `{ }` of a JSX
      -- element is marked, so that a JSX element which is the body of an
      -- arrow function written here keeps its own lines
      let ast : StartCtx := if pos == .jsxChildExpr || pos == .jsxAttrExpr then .jsxCallArg else .none
      -- prettier asks whether the call is a test call without looking at
      -- the call that holds it when it decides that the parameters of a
      -- function argument stay on one line, so the function written
      -- inside an Angular wrapper keeps an ordinary parameter list
      let docs :=
        if isTestCallOf false f args then testArgDocs ast args else argDocs ast args
      let argsDoc := tsTypeArgsDoc typeArgs
        ++ argumentsDocMaybeOpen (isLongCurriedCall pos args.length)
        (stay || isHookCallWithDepsArray args) (isFunctionCompositionArguments args)
        (canHugFirstArg args)
        (canHugLastArg args) docs (argHugFirstDocs ast false args) (argHugDocs ast false args)
      if isMemberish f && !stay then
        memberChainDoc (pos == .statement) (isLongCurriedCall pos args.length)
          (chainItemsOf (calleePos pos args.length) atStart false true f
            ++ [chainCallItem args argsDoc])
      else
        let cpos := calleePos pos args.length
        let whole := inPosStartC atStart cpos f (exprCore atStart cpos f) ++ argsDoc
        -- a call of a call is grouped as a whole, so that the argument
        -- list of the callee, which is left ungrouped when the call is a
        -- link of a curried chain, breaks with the line they share
        if isCallLikeExpr f then .group whole else whole
  | .dot o n =>
      let opos := memberObjectPos false pos
      memberDocOf (memberAccessInlines pos o true)
        (inPosStartC atStart opos o (exprCore atStart opos o))
        (t ("." ++ n.val))
  | .privateDot o n =>
      let opos := memberObjectPos false pos
      memberDocOf (memberAccessInlines pos o false)
        (inPosStartC atStart opos o (exprCore atStart opos o))
        (t (".#" ++ n.val))
  | .index o i =>
      let opos := memberObjectPos true pos
      inPosStartC atStart opos o (exprCore atStart opos o)
        ++ indexLookupDoc (isNumericLit i) (inPosC .computed i (exprCore .none .computed i))
  | .chain base links =>
      let bpos := chainBasePos pos links
      chainAssemble (chainIsOptional links) pos
        ((if isChainSpine base then
            chainItemsOf bpos atStart (chainMergesBase links)
              (links.toList.any chainLinkIsCall) base
          else [chainBaseItem base (inPosStartC atStart bpos base
                  (exprCore atStart bpos base))])
          ++ chainLinkItemsNE
              -- the call at the end of a chain written directly in a `{ }`
              -- of a JSX element marks its arguments, as a plain call does
              (if pos == .jsxChildExpr || pos == .jsxAttrExpr then .jsxCallArg else .none)
              links)
  | .importCall spec none =>
      -- a plain `import("module")` is never broken, however long the name
      if (match spec with | .string _ => true | _ => false) then
        t "import(" ++ inPosC .callArg spec (exprCore .none .callArg spec) ++ t ")"
      else
        -- otherwise the arguments are laid out like those of any other
        -- call, except that a dynamic import takes no trailing comma
        let args := [spec]
        let pOnly : Pos := .hugArg true false false
        let pFirst : Pos := .hugArg false false true
        .group (t "import"
          ++ argumentsDocOf .never false (isHookCallWithDepsArray args)
              (isFunctionCompositionArguments args) (canHugFirstArg args)
              (canHugLastArg args)
              [inPosC .callArg spec (exprCore .none .callArg spec)]
              [inPosC pFirst spec (exprCore .none pFirst spec)]
              [inPosC pOnly spec (exprCore .none pOnly spec)])
  | .importCall spec (some o) =>
      let args := [spec, o]
      let pLast : Pos := .hugArg false false false
      let pFirst : Pos := .hugArg false false true
      let specDoc := inPosC .callArg spec (exprCore .none .callArg spec)
      let oDoc := inPosC .callArg o (exprCore .none .callArg o)
      .group (t "import"
        ++ argumentsDocOf .never false (isHookCallWithDepsArray args)
            (isFunctionCompositionArguments args) (canHugFirstArg args)
            (canHugLastArg args) [specDoc, oDoc]
            [inPosC pFirst spec (exprCore .none pFirst spec), oDoc]
            [specDoc, inPosC pLast o (exprCore .none pLast o)])
  | .classExpr decorators name typeParams heritage implements_ body =>
      let ofAssign := match pos with | .assignRhs _ _ a _ => a | _ => false
      classDocOf (decoratorDocs decorators) false name (tsTypeParamsDocOf false typeParams)
        (classHeritageGroupMode ofAssign heritage implements_)
        (match heritage with
          | none => Doc.nil
          | some ⟨he, hargs⟩ =>
            superClassDoc ofAssign
              (inPosC .classHeritage he (exprCore .none .classHeritage he)
                ++ tsTypeArgsDoc hargs))
        (tsHeritageDocs implements_)
        body (classElemDocsOf (quoteAllMembers body) body)
  | .seq l r =>
      -- the operands after the first of a comma operator that is an
      -- expression statement, or the head of a `for (;;)`, are indented
      let inFor :=
        match pos with
        | .forHeadPart | .forTest | .forSeqTail _ => true
        | _ => false
      let indented :=
        match pos with
        | .statement | .forHeadPart | .forTest | .forSeqTail _ => true
        | .seqTail ind _ => ind
        | _ => false
      -- a comma operator inside another one is one chain with it: it is
      -- not grouped again, and only the outermost one indents
      let inChain :=
        match pos with
        | .seqTail .. | .forSeqTail .. => true
        | _ => false
      let isTail :=
        match pos with
        | .seqTail _ tl => tl
        | .forSeqTail tl => tl
        | _ => false
      let leftPos : Pos := if inFor then .forSeqTail isTail else .seqTail indented isTail
      let rightPos : Pos := if inFor then .forSeqTail true else .seqTail indented true
      -- the operands of a comma operator that is the expression of a
      -- `return` or of a `throw`, or the body of an arrow function, stand
      -- between the parentheses of their own when they break
      let wrapped :=
        match pos with
        | .returnThrow | .arrowBody | .hugArrowBody => true
        | _ => false
      let tail := t "," ++ .line ++ inPosC rightPos r (exprCore .none rightPos r)
      let body := inPosStartC atStart leftPos l (exprCore atStart leftPos l)
        ++ (if indented && !isTail then Doc.nest indentWidth tail else tail)
      if inChain then body
      else if wrapped then
        .group (.ifBreak (.nest indentWidth (.softline ++ body) ++ .softline) body)
      else .group body
  | .binary l op r =>
      let nodeKind : BinKind := if isLogicalOp op then .logical else .arith
      let insideParens := pos == .ifTest
      let leftParts : List Doc :=
        if shouldFlattenLeft op l then binaryParts atStart nodeKind insideParens l
        else
          [Doc.group (inPosStartC atStart (.binOperand op true) l
            (exprCore atStart (.binOperand op true) l))]
      binaryLayoutWith pos l op r
        (leftParts
          ++ (if rightContinuesLogicalChain op r then logicalRightParts op r
              else binaryTailWith (parentBinKind pos) insideParens l op r
                (inPosC (.binOperand op false) r (exprCore .none (.binOperand op false) r))))
  | .postfix e op =>
      inPosStartC atStart .unaryArg e (exprCore atStart .unaryArg e) ++ t (postfixOpText op)
  | .ternary c a b =>
      if Options.experimentalTernaries then
        -- prettier's experimental layout: the `?` stands at the end of the
        -- line of the test and the `:` in front of the alternate, and a
        -- chain of conditionals reads as a list of cases
        let consIsTernary := match a with | .ternary .. => true | _ => false
        let altIsTernary := match b with | .ternary .. => true | _ => false
        let parentIsTernary := isTernaryPos pos
        let inTest := match pos with | .ternaryTest .. => true | _ => false
        let inAlternate := match pos with | .ternaryAlternate .. => true | _ => false
        -- the conditional continues a chain: its alternate is one, or it
        -- is written as the alternate of one
        let chainTail := altIsTernary || inAlternate
        let bigTabs := 2 < tabWidth || Options.useTabs
        let inChain := parentIsTernary && !inTest
        let inheritedJsx :=
          match pos with
          | .ternaryBranch _ j | .ternaryAlternate _ j => j
          | _ => false
        let jsxRoot := if inChain then inheritedJsx else pos == .jsxChildExpr
        -- what the branches of this conditional inherit: a conditional
        -- written in the `{ }` of an attribute passes the flag on, since
        -- what stands inside it is no longer straight inside the `{ }`
        let jsxInner :=
          if inChain then inheritedJsx else pos == .jsxChildExpr || pos == .jsxAttrExpr
        let gp := ternaryParentIndents pos
        let testPos : Pos := .ternaryTest gp
        let consPos : Pos := .ternaryBranch gp jsxInner
        let altPos : Pos := .ternaryAlternate gp jsxInner
        let testDoc := inPosStartC atStart testPos c (exprCore atStart testPos c)
        let consDoc := inPosC consPos a (exprCore .none consPos a)
        let altDoc := inPosC altPos b (exprCore .none altPos b)
        -- a conditional whose consequent is short is written as a case:
        -- the test and the consequent hold one line, and the alternate
        -- stands under them
        let shortCons :=
          !chainTail && !parentIsTernary
            && (if jsxRoot then (match a with | .null => true | _ => false)
                else isShortExpr a && isSmallNode 3 c)
        let groupTest :=
          chainTail || (parentIsTernary && isSmallNode 1 c) || shortCons
        let parens (d : Doc) : Doc :=
          .ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d) ++ .softline
            ++ .ifBreak (t ")") .nil
        let testPart : Doc :=
          .groupId 0 (parens testDoc
            ++ (match c with | .ternary .. => Doc.breakParent | _ => .nil) ++ t " ?")
        let consPart : Doc :=
          .nest indentWidth
            ((if consIsTernary || (jsxRoot && (isJsxExpr a || parentIsTernary || chainTail))
                then .hardline else .line)
              ++ consDoc)
        let head : Doc :=
          if groupTest then
            .groupId 1 (testPart
              ++ (if chainTail then consPart else .ifBreakOf 0 consPart (.group consPart)))
          else testPart ++ consPart
        let altBody : Doc :=
          if shortCons then .ifBreakOf 1 altDoc (.dedent (parens altDoc)) else altDoc
        let sep : Doc :=
          if altIsTernary then .hardline
          else if shortCons then .ifBreakOf 1 .line (t " ")
          else .line
        let pad : Doc :=
          if altIsTernary || !bigTabs then t " "
          else
            let filler := t (if Options.useTabs then "\t" else String.pushn "" ' ' (tabWidth - 1))
            if groupTest then
              .ifBreakOf 1 filler
                (.ifBreak (if chainTail || shortCons then t " " else filler) (t " "))
            else .ifBreak filler (t " ")
        let altPart : Doc :=
          if altIsTernary then altBody
          else
            .group (.nest indentWidth altBody
              ++ (if jsxRoot && !shortCons then .softline else .nil))
        let memberParent := match pos with | .memberObject false _ _ => true | _ => false
        let chainRootAssign :=
          (extraIndentRoot pos && (isMemberObjectPos pos || isCalleePos pos))
            || (match pos with
                | .tsTypeOperand extra | .tsNonNullArg extra => extra
                | _ => false)
        -- a chain of conditionals always breaks
        let forced := consIsTernary || altIsTernary
        let body : Doc :=
          head ++ sep ++ t ":" ++ pad ++ altPart
            ++ (if memberParent && !chainRootAssign then .softline else .nil)
            ++ (if forced then Doc.breakParent else .nil)
        -- the right hand side of an assignment that is not one prettier
        -- breaks the line after the operator for
        -- a field written with the `accessor` keyword is not one of the
        -- nodes prettier reads an assignment layout from
        let assignNoBreak :=
          (isAssignRhsPos pos
            || (match pos with | .propValue accessor _ => !accessor | _ => false))
            && !forced
        Doc.scopeIds
          (if assignNoBreak then .group (.nest indentWidth (.softline ++ .group body))
            else if pos == .returnThrow && !forced then .group (.nest indentWidth body)
            else if chainRootAssign then .group (.nest indentWidth (.softline ++ body))
            else if !inChain then .group body
            else body)
      else
      -- a chain of conditionals is laid out as one unit: the branches of a
      -- conditional inside a conditional are neither grouped nor indented
      -- again, and each level is aligned two columns further
      let consIsTernary := match a with | .ternary .. => true | _ => false
      -- a binary expression in the conditional is indented when the
      -- conditional itself is an argument of a call or of a `new`, or the
      -- expression of a `return` or of a `throw`
      let gp := ternaryParentIndents pos
      let inChain :=
        match pos with | .ternaryBranch .. | .ternaryAlternate .. => true | _ => false
      -- a chain of conditionals that holds a JSX element anywhere is laid
      -- out the way prettier lays JSX out
      let jsxMode :=
        match pos with
        | .ternaryBranch _ j | .ternaryAlternate _ j => j
        | _ => ternaryChainHasJsx (.ternary c a b)
      let testPos : Pos := .ternaryTest gp
      let consPos : Pos := .ternaryBranch gp jsxMode
      let altPos : Pos := .ternaryAlternate gp jsxMode
      let testDoc := inPosStartC atStart testPos c (exprCore atStart testPos c)
      let test :=
        if (match pos with | .ternaryAlternate .. => true | _ => false) then Doc.align 2 testDoc
        else testDoc
      -- the chain that holds the conditional stands where prettier
      -- indents the whole of it inside the parentheses it needs
      let extraIndent :=
        (extraIndentRoot pos && (isMemberObjectPos pos || isCalleePos pos))
          -- a conditional written as the expression of an `as`, or of a
          -- `!`, stands on lines of its own inside the parentheses it
          -- needs there
          || (match pos with
              | .tsTypeOperand extra | .tsNonNullArg extra => extra
              | _ => false)
      let atRoot := (match pos with | .ternaryTest .. => true | _ => false) || extraIndent
      if jsxMode then
        -- each branch which is neither `null` nor a further conditional
        -- stands between parentheses of its own where the chain breaks
        let wrap (d : Doc) : Doc :=
          .ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d) ++ .softline
            ++ .ifBreak (t ")") .nil
        let consDoc := inPosC consPos a (exprCore .none consPos a)
        let altDoc := inPosC altPos b (exprCore .none altPos b)
        let parts := t " ? " ++ (if isNilExpr a then consDoc else wrap consDoc)
          ++ t " : " ++ (if consIsTernaryOf b || isNilExpr b then altDoc else wrap altDoc)
        let body := test ++ parts
        let result := if inChain then body else Doc.group body
        if atRoot then .group (.nest indentWidth (.softline ++ result) ++ .softline) else result
      else
      -- a branch stands two columns further in, written as a step of its
      -- own where the indentation is tabs
      let branch (d : Doc) : Doc := if Options.useTabs then Doc.nest indentWidth d else Doc.align 2 d
      let consDoc := branch (inPosC consPos a (exprCore .none consPos a))
      let altDoc := branch (inPosC altPos b (exprCore .none altPos b))
      -- the branches of a conditional which is itself the consequent of
      -- one stand `tabWidth - 2` columns further in; with tabs they stand
      -- where they are, prettier writing the step it removes back again
      let chainAlign (d : Doc) : Doc :=
        match pos with
        | .ternaryBranch .. =>
            if Options.useTabs || tabWidth ≤ 2 then d else Doc.align (tabWidth - 2) d
        | _ => d
      let parts := chainAlign (Doc.line ++ t "? "
        ++ (if consIsTernary then Doc.ifBreak .nil (t "(") else .nil)
        ++ consDoc
        ++ (if consIsTernary then Doc.ifBreak .nil (t ")") else .nil)
        ++ .line ++ t ": " ++ altDoc)
      -- `(a\n  ? b\n  : c\n).call()`: the closing parenthesis of a
      -- conditional in the object of a `.` access keeps its own line
      let closing : Doc :=
        if !extraIndent && (match pos with | .memberObject false .. => true | _ => false) then
          .softline
        else .nil
      let body := test ++ (if inChain then parts else Doc.nest indentWidth parts) ++ closing
      let result := if inChain then body else Doc.group body
      if atRoot then .group (.nest indentWidth (.softline ++ result) ++ .softline)
      else result
  | .arrow isAsync typeParams params retType body =>
      -- an arrow function expanded in place as the argument of a call is
      -- not laid out as a chain, and its parameter list keeps its line
      let expanded := (match pos with | .hugArg .. => true | _ => false) || pos == .hugArrowBody
      let sig :=
        let d := t (if isAsync then "async " else "")
          ++ arrowSignatureOf typeParams (tsTypeParamsDocOf true typeParams) params
              (paramDocs params) retType (tsArrowAnnotation retType)
        -- the parameters of an arrow written as the argument of a call of
        -- a test framework stay on the line of the call.  An arrow that
        -- takes no parameter at all keeps its layout: there is no
        -- parameter list to write on one line, and its type parameters
        -- break as they do anywhere else
        if (expanded || pos == .testCallArg) && !params.isEmpty then Doc.removeLines d else d
      -- an arrow function written straight inside a `{ }` of a JSX
      -- element leaves the closing brace its own line once it breaks
      let jsxParent := pos == .jsxAttrExpr || pos == .jsxChildExpr
      if !expanded && isArrowChainBody body then
        let (paramss, tail) := arrowChainParts params body
        let breakChain := paramss.any (fun ps => !ps.all paramIsPlainIdent)
        let (sigs, bodyPart) := arrowChainDocs breakChain jsxParent body
        arrowLayoutOf pos breakChain (arrowBodyStaysOnLine breakChain tail)
          (sig :: sigs) bodyPart
      else
        arrowLayoutOf pos false true [sig]
          (arrowBodyDoc false false (atStart == .jsxCallArg) jsxParent
            (if expanded then .hugArrowBody else .arrowBody) body)
  | .func isAsync isGen name typeParams params retType body =>
      functionDocOf
        (pos == .testCallArg ||
          match pos with
          | .hugArg sole newExpr first =>
              !newExpr && !first && (!sole || params.all paramIsPlainIdent)
          | _ => false)
        isAsync isGen name typeParams (tsTypeParamsDocOf false typeParams) params
        (paramDocs params) retType (tsAnnotation retType) (some body)
        (Doc.joinWith .hardline (statementDocs true true body))
  | .new callee typeArgs args =>
      t "new "
        ++ parenIfExpr (!newCalleeOk callee) callee (exprCore .none .newCallee callee)
        ++ tsTypeArgsDoc typeArgs
        ++ argumentsDoc (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
        (canHugLastArg args) (argDocs .none args) (argHugFirstDocs .none true args) (argHugDocs .none true args)
  | .spread e => t "..." ++ inPosC .spreadArg e (exprCore .none .spreadArg e)
  | .template tag typeArgs head parts =>
      (match tag with
        | none => Doc.nil
        | some tg => inPosStartC atStart .templateTag tg (exprCore atStart .templateTag tg))
        ++ (match tag with | none => Doc.nil | some _ => tsTypeArgsDoc typeArgs)
        ++ t "`" ++ t (encodeTemplateText head) ++ templatePartsAux .nil parts ++ t "`"
  | .unary op e =>
      t (unaryOpText op)
        ++ (if unaryClash op e then parens (exprCore .none .unaryArg e)
            else inPosC .unaryArg e (exprCore .none .unaryArg e))
  | .jsx n =>
      -- a JSX element that stands where a line break would leave it
      -- beside other text is written between parentheses of its own when
      -- it does not fit on the line it starts on
      let d := jsxNodeDoc n
      if jsxNoWrapPos pos then d
      else jsxWrapInParens (atStart == .jsxArrowBody) (jsxNeedsParens pos) d
  | .yield none => t "yield"
  | .yield (some e) => t "yield " ++ inPosC .yieldArg e (exprCore .none .yieldArg e)
  | .yieldFrom e => t "yield* " ++ inPosC .yieldArg e (exprCore .none .yieldArg e)
  | .asExpr e ty =>
      -- where the `as` itself takes the parentheses that break, what it
      -- holds is written inside them as it is written anywhere else: only
      -- one of the two takes lines of its own
      let operandPos : Pos :=
        .tsTypeOperand (extraIndentRoot pos && !tsTypeExprBreaksInParens pos)
      let d := inPosStartC atStart operandPos e (exprCore atStart operandPos e)
        ++ t " as " ++ tsTypeDoc .normal true 0 ty
      if tsTypeExprBreaksInParens pos then
        .group (.nest indentWidth (.softline ++ d) ++ .softline)
      else d
  | .satisfies e ty =>
      let operandPos : Pos :=
        .tsTypeOperand (extraIndentRoot pos && !tsTypeExprBreaksInParens pos)
      let d := inPosStartC atStart operandPos e (exprCore atStart operandPos e)
        ++ t " satisfies " ++ tsTypeDoc .normal true 0 ty
      if tsTypeExprBreaksInParens pos then
        .group (.nest indentWidth (.softline ++ d) ++ .softline)
      else d
  | .nonNull e =>
      let operandPos : Pos := .tsNonNullArg (extraIndentRoot pos)
      inPosStartC atStart operandPos e (exprCore atStart operandPos e) ++ t "!"
  | .instantiation e typeArgs =>
      let operandPos : Pos := .tsNonNullArg false
      let d := inPosStartC atStart operandPos e (exprCore atStart operandPos e)
        ++ tsTypeArgsDoc typeArgs
      if ctx.guarded then t "(" ++ d ++ t ")" else d

/-- The operands and operators of a chain of binary operators of the same
precedence, as the list prettier lays out together. -/
def binaryParts (atStart : StartCtx) (parentKind : BinKind) (insideParens : Bool) :
    MiniExpr → List Doc
  | .binary l op r =>
      let nodeKind : BinKind := if isLogicalOp op then .logical else .arith
      let leftParts : List Doc :=
        if shouldFlattenLeft op l then binaryParts atStart nodeKind insideParens l
        else
          [Doc.group (inPosStartC atStart (.binOperand op true) l
            (exprCore atStart (.binOperand op true) l))]
      leftParts
        ++ (if rightContinuesLogicalChain op r then logicalRightParts op r
            else binaryTailWith parentKind insideParens l op r
              (inPosC (.binOperand op false) r (exprCore .none (.binOperand op false) r)))
  | _ => []

/-- The parts of the operands of a chain of the same logical operator that
leans to the right, which is called on such a chain alone.  Prettier
rebalances the chain, so its operands belong to the chain around it: each
of them is written after the operator, on a line of its own, unless it is
one prettier keeps on the line of the operator, that is, a JSX element or
a non-empty object or array literal. -/
def logicalRightParts (op : BinOp) : MiniExpr → List Doc
  | .binary rl _ rr =>
      (if rightContinuesLogicalChain op rl then logicalRightParts op rl
        else
          [binOpLead (shouldInlineLogicalOf op rl),
            binOpTail op (shouldInlineLogicalOf op rl)
              (inPosC (.binOperand op false) rl (exprCore .none (.binOperand op false) rl))])
      ++ (if rightContinuesLogicalChain op rr then logicalRightParts op rr
        else
          [binOpLead (shouldInlineLogicalOf op rr),
            binOpTail op (shouldInlineLogicalOf op rr)
              (inPosC (.binOperand op false) rr (exprCore .none (.binOperand op false) rr))])
  | _ => []

/-- The elements of a member chain whose last node is `e`, followed by the
elements of the links of an optional chain that continues it.  `pos` is
the position of `e` itself, which the objects and the callees inside it
inherit.  `underCall` says that a call of the chain is written around `e`,
which is what takes the calls written inside it into the chain: prettier
reads a chain out from the outermost call whose callee is a member
access, so a call which stands above every call of the chain is printed
on its own instead. -/
def chainItemsOf (pos : Pos) (atStart : StartCtx) (merge underCall : Bool) :
    MiniExpr → List ChainItem
  | .dot o n =>
      let opos := memberObjectPos false pos
      (if isChainSpineNodeObject o then chainItemsOf opos atStart false underCall o
        else [chainBaseItem o (inPosStartC atStart opos o
                (exprCore atStart opos o))])
        ++ [{ kind := .dot, doc := t ("." ++ n.val), name := n.val }]
  | .privateDot o n =>
      let opos := memberObjectPos false pos
      (if isChainSpineNodeObject o then chainItemsOf opos atStart false underCall o
        else [chainBaseItem o (inPosStartC atStart opos o
                (exprCore atStart opos o))])
        ++ [{ kind := .dot, doc := t (".#" ++ n.val), name := n.val }]
  -- a `!` is an element of the chain, which goes on into the expression
  -- it is written on
  | .nonNull e =>
      let operandPos : Pos := .tsNonNullArg (extraIndentRoot pos)
      (if isChainSpineNodeObject e then chainItemsOf operandPos atStart false underCall e
        else [chainBaseItem e (inPosStartC atStart operandPos e
                (exprCore atStart operandPos e))])
        ++ [nonNullItem]
  | .index o i =>
      let opos := memberObjectPos true pos
      (if isChainSpineNodeObject o then chainItemsOf opos atStart false underCall o
        else [chainBaseItem o (inPosStartC atStart opos o
                (exprCore atStart opos o))])
        ++ [{ kind := .index, numericIndex := isNumericLit i,
              doc := indexLookupDoc (isNumericLit i)
                (inPosC .computed i (exprCore .none .computed i)) }]
  | .call f typeArgs args =>
      let cpos := calleePos pos args.length
      let argsDoc := tsTypeArgsDoc typeArgs
        ++ argumentsDocMaybeOpen (isLongCurriedCall pos args.length)
        (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
        (canHugLastArg args) (argDocs .none args) (argHugFirstDocs .none false args) (argHugDocs .none false args)
      -- a call whose arguments stay on its line is one element of the
      -- chain, printed as it is anywhere else
      if !underCall && callArgsStayOnLine false false f args then
        [chainBaseItem (.call f typeArgs args)
          (inPosStartC atStart cpos f (exprCore atStart cpos f) ++ tsTypeArgsDoc typeArgs
            ++ argumentsDoc true false false false
                (if isTestCallOf false f args then testArgDocs .none args else argDocs .none args) [] [])]
      else if !underCall && !isMemberish f then
        -- the chain starts below this call: it is printed as it is
        -- anywhere else, and the chain of its callee stands inside it
        [chainBaseItem (.call f typeArgs args)
          (let whole := inPosStartC atStart cpos f (exprCore atStart cpos f) ++ argsDoc
            if isCallLikeExpr f then .group whole else whole)]
      else
      (if isChainSpineNode f then chainItemsOf cpos atStart false true f
        else [chainBaseItem f (inPosStartC atStart cpos f (exprCore atStart cpos f))])
        ++ [chainCallItem args argsDoc]
  | .chain b links =>
      -- the chain merges into the one that holds it when the link that
      -- follows it is optional; otherwise it is a parenthesised base
      let bpos := chainBasePos pos links
      let hasCallLink := links.toList.any chainLinkIsCall
      let inner :=
        let innerStart : StartCtx := if merge then atStart else .none
        let innerUnder := hasCallLink || (merge && underCall)
        (if isChainSpineObject b then
            chainItemsOf bpos innerStart (chainMergesBase links) innerUnder b
          else [chainBaseItem b (inPosStartC innerStart bpos b
                  (exprCore innerStart bpos b))])
          ++ chainLinkItemsNE .none links
      if merge then inner
      else
        [chainBaseItem (.chain b links)
          (t "(" ++ chainAssemble (chainIsOptional links) .arg inner ++ t ")")]
  | e => [chainBaseItem e .nil]

/-- The elements of the links of an optional chain. -/
def chainLinkItemsNE (lastCtx : StartCtx) (links : NEList MiniChainLink) : List ChainItem :=
  match links with
  | ⟨hd, tl⟩ =>
      chainLinkItem (if linksAllNonNull tl then lastCtx else .none) hd
        :: chainLinkItems lastCtx tl

/-- The elements of the links of an optional chain. -/
def chainLinkItems (lastCtx : StartCtx) : List MiniChainLink → List ChainItem
  | [] => []
  | l :: rest =>
      chainLinkItem (if linksAllNonNull rest then lastCtx else .none) l
        :: chainLinkItems lastCtx rest

/-- The element of one link of an optional chain. -/
def chainLinkItem (lastCtx : StartCtx) : MiniChainLink → ChainItem
  | .dot optional n =>
      { kind := .dot, name := n.val,
        doc := t ((if optional then "?." else ".") ++ n.val) }
  | .privateDot optional n =>
      { kind := .dot, name := n.val,
        doc := t ((if optional then "?.#" else ".#") ++ n.val) }
  | .index optional i =>
      { kind := .index, numericIndex := isNumericLit i,
        doc := t (if optional then "?." else "")
          ++ indexLookupDoc (isNumericLit i) (inPosC .computed i (exprCore .none .computed i)) }
  | .nonNull => nonNullItem
  | .call optional typeArgs args =>
      chainCallItem args (t (if optional then "?." else "") ++ tsTypeArgsDoc typeArgs
          ++ argumentsDoc (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
        (canHugLastArg args) (argDocs lastCtx args) (argHugFirstDocs lastCtx false args)
          (argHugDocs lastCtx false args))

/-- The arguments of a call or of a `new`. -/
def argDocs (st : StartCtx) : List MiniExpr → List Doc
  | [] => []
  | a :: rest =>
      inPosC .callArg a (exprCore (argStartCtx st a) .callArg a) :: argDocs st rest

/-- The arguments of a call of a test framework. -/
def testArgDocs (st : StartCtx) : List MiniExpr → List Doc
  | [] => []
  | a :: rest =>
      inPosC .testCallArg a (exprCore (argStartCtx st a) .testCallArg a) :: testArgDocs st rest

/-- The arguments of a call, with the last one printed as the layout
prints an argument it expands in place.  `newExpr` says that the call is a
`new`. -/
def argHugDocs (st : StartCtx) (newExpr : Bool) : List MiniExpr → List Doc
  | [] => []
  | [a] =>
      let p : Pos := .hugArg true newExpr false
      [inPosC p a (exprCore (argStartCtx st a) p a)]
  | a :: rest =>
      inPosC .callArg a (exprCore (argStartCtx st a) .callArg a)
        :: argHugTailDocs st newExpr rest

/-- The arguments that follow the first one of a call of more than one
argument, with the last one printed as the layout prints an argument it
expands in place. -/
def argHugTailDocs (st : StartCtx) (newExpr : Bool) : List MiniExpr → List Doc
  | [] => []
  | [a] =>
      let p : Pos := .hugArg false newExpr false
      [inPosC p a (exprCore (argStartCtx st a) p a)]
  | a :: rest =>
      inPosC .callArg a (exprCore (argStartCtx st a) .callArg a)
        :: argHugTailDocs st newExpr rest

/-- The arguments of a call, with the first one printed as the layout
prints an argument it expands in place.  `newExpr` says that the call is a
`new`. -/
def argHugFirstDocs (st : StartCtx) (newExpr : Bool) : List MiniExpr → List Doc
  | [] => []
  | a :: rest =>
      let p : Pos := .hugArg false newExpr true
      inPosC p a (exprCore (argStartCtx st a) p a) :: argDocs st rest



-- ### JSX

/-- One attribute of a JSX element. -/
def jsxAttrDoc : MiniJSXAttribute → Doc
  | .spread e => t "{..." ++ inPosC .spreadArg e (exprCore .none .spreadArg e) ++ t "}"
  | .attr name none => t name.render
  | .attr name (some (.string v)) => t (name.render ++ "=" ++ jsxAttrLit v)
  | .attr name (some (.expr e)) =>
      t (name.render ++ "=")
        ++ jsxContainerOf false e (inPosC .jsxAttrExpr e (exprCore .none .jsxAttrExpr e))
  -- `name=<x />`, an element written as the value with no braces
  | .attr name (some (.node n)) => t (name.render ++ "=") ++ jsxNodeDoc n

/-- The attributes of a JSX element. -/
def jsxAttrDocs : List MiniJSXAttribute → List Doc
  | [] => []
  | a :: rest => jsxAttrDoc a :: jsxAttrDocs rest

/-- The children of an element, each with the document it prints as; a
text child prints as its words, which `jsxChildPartsOf` lays out, so it
carries none. -/
def jsxChildDocs : List MiniJSXChild → List JSXChildDoc
  | [] => []
  | c :: rest =>
    let d : Doc :=
      match c with
      -- `{...children}`, whose operand stands between the braces as it is
      | .expr (.spread e) =>
          t "{..." ++ inPosC .jsxSpreadChildArg e (exprCore .none .jsxSpreadChildArg e) ++ t "}"
      | .expr e => jsxContainerOf true e (inPosC .jsxChildExpr e (exprCore .none .jsxChildExpr e))
      | .node n => jsxNodeDoc n
      -- `{}`, which holds nothing at all
      | .emptyExpr => t "{}"
      | .text _ => .nil
    (c, d) :: jsxChildDocs rest

/-- A JSX element or fragment, without the parentheses its position may
ask for. -/
def jsxNodeDoc : MiniJSXNode → Doc
  | .element name typeArgs attrs children =>
    let opening := jsxOpeningDocOf name.render (tsTypeArgsDoc typeArgs) children.isNone
      (jsxOneStringAttr attrs) (jsxAttrsBreak attrs) (jsxAttrDocs attrs)
    match children with
    | none => opening
    | some kids0 =>
      -- two texts written next to one another are one text to a parser
      let pairs := jsxMergeChildDocs (jsxChildDocs kids0)
      let kids := pairs.map Prod.fst
      let closing := t ("</" ++ name.render ++ ">")
      if kids.all jsxChildIsEmpty then opening ++ closing
      else
        jsxAssemble opening closing (attrs.length > 1) kids (jsxChildPartsOf [] pairs)
          (match kids0 with
            | [.expr e] =>
              if jsxIsTemplateExpr e then
                some (jsxContainerOf true e
                  (inPosC .jsxChildExpr e (exprCore .none .jsxChildExpr e)))
              else none
            | _ => none)
  | .fragment kids0 =>
      let pairs := jsxMergeChildDocs (jsxChildDocs kids0)
      let kids := pairs.map Prod.fst
      jsxAssemble (t "<>") (t "</>") false kids (jsxChildPartsOf [] pairs)
        (match kids0 with
          | [.expr e] =>
            if jsxIsTemplateExpr e then
              some (jsxContainerOf true e
                (inPosC .jsxChildExpr e (exprCore .none .jsxChildExpr e)))
            else none
          | _ => none)

/-- The decorators of a class or of a class member, each written `@expr`. -/
def decoratorDocs : List MiniExpr → List Doc
  | [] => []
  | d :: rest =>
      (t "@" ++ inPosC .decorator d (exprCore .none .decorator d)) :: decoratorDocs rest

/-- A binding pattern.  `exempt` says whether the pattern stands in one of
the positions where prettier does not force an object pattern that
destructures further to break: a parameter list, a default value or the
parameter of a `catch`. -/
def patternDoc (exempt : Bool) : MiniPattern → Doc
  | .ident n => t n.val
  | .array els => arrayPatternDocOf els (arrayPatternElemDocs els)
  | .object props none =>
      let items := objectPatternPropDocsOf (quoteAllPatternKeys props) props
      if !exempt && objectPatternForcesBreak props then sepListBroken "{" "}" true .es5 items
      else sepList "{" "}" true .es5 items
  | .object props (some r) =>
      let items := objectPatternPropDocsOf (quoteAllPatternKeys props) props ++ [t "..." ++ patternDoc false r]
      if !exempt && objectPatternForcesBreak props then sepListBroken "{" "}" true .never items
      else sepList "{" "}" true .never items
  | .withDefault p v => patternDoc true p ++ t " = " ++ inPosC .arg v (exprCore .none .arg v)
  | .target e => inPosC .arg e (exprCore .none .arg e)

/-- The left hand side of a declarator or of a destructuring assignment.
Prettier leaves an object pattern that stands there ungrouped -- the
assignment layout is what groups it -- so that the pattern breaks along
with the assignment. -/
def assignTargetPatternDoc : MiniPattern → Doc
  | .object props none =>
      let items := objectPatternPropDocsOf (quoteAllPatternKeys props) props
      if objectPatternForcesBreak props then sepListBroken "{" "}" true .es5 items
      else sepListOpen "{" "}" true .es5 items
  | .object props (some r) =>
      let items := objectPatternPropDocsOf (quoteAllPatternKeys props) props ++ [t "..." ++ patternDoc false r]
      if objectPatternForcesBreak props then sepListBroken "{" "}" true .never items
      else sepListOpen "{" "}" true .never items
  | .ident n => t n.val
  | .array els => arrayPatternDocOf els (arrayPatternElemDocs els)
  | .withDefault p v => patternDoc true p ++ t " = " ++ inPosC .arg v (exprCore .none .arg v)
  | .target e => inPosC .arg e (exprCore .none .arg e)

def arrayPatternElemDocs : List MiniArrayPatternElem → List Doc
  | [] => []
  | .hole :: rest => Doc.nil :: arrayPatternElemDocs rest
  | .elem p :: rest => patternDoc false p :: arrayPatternElemDocs rest
  | .rest p :: rest => (t "..." ++ patternDoc false p) :: arrayPatternElemDocs rest

def objectPatternPropDocsOf (quoteAll : Bool) : List MiniObjectPatternProp → List Doc
  | [] => []
  | ⟨key, value⟩ :: rest =>
      (if patternShorthand key value then patternDoc false value
        else
          -- prettier lays `key: value` out as it lays an assignment out,
          -- so that the line may break after the colon
          let short := match keyTextWidth key with
            | some w => w < tabWidth + 3
            | none => false
          assignmentDoc short (propertyKeyDoc quoteAll key) ":" (patternLayoutExpr value)
            (patternDoc false value))
        :: objectPatternPropDocsOf quoteAll rest

/-- The elements of an array literal; an elision prints as nothing. -/
def arrayItemDocs : List MiniArrayElement → List Doc
  | [] => []
  | .elem e :: rest => inPosC .arrayElement e (exprCore .none .arrayElement e) :: arrayItemDocs rest
  | .hole :: rest => Doc.nil :: arrayItemDocs rest

/-- The `${…}` substitutions of a template literal, and the text between
them. -/
def templatePartsAux (acc : Doc) : List MiniTemplatePart → Doc
  | [] => acc
  | ⟨e, suffix⟩ :: rest =>
      templatePartsAux
        (acc ++ templateSubstDoc (templateSubstIndents e)
            (inPosC .templateSubst e (exprCore .none .templateSubst e))
          ++ t (encodeTemplateText suffix)) rest

/-- The name of a property or of a method.  Under `quoteProps:
"as-needed"`, prettier's default, a quoted name that is a valid
identifier -- or the plain spelling of a number -- loses its quotes;
under `"preserve"` it keeps them; and `quoteAll`, which
`quoteProps: "consistent"` sets when a sibling name cannot lose its
quotes, quotes every name that can be written quoted.  A name written as
a number is never quoted: prettier leaves it alone where it reads
TypeScript. -/
def propertyKeyDoc (quoteAll : Bool) : MiniPropertyName → Doc
  | .ident n => if quoteAll then t (strLit n.val) else t n.val
  | .private_ n => t ("#" ++ n.val)
  | .string v =>
      if Options.quoteProps == .preserve || quoteAll then t (strLit v)
      else if isIdentifierName v then t v
      else if isSimpleNumberString v then t v
      else t (strLit v)
  | .number n => t n.render
  | .computed e => t "[" ++ inPosC .arg e (exprCore .none .arg e) ++ t "]"

def propertyDoc (quoteAll : Bool) : MiniProperty → Doc
  | .keyValue k v =>
      let short := match keyTextWidth k with
        | some w => w < tabWidth + 3
        | none => false
      assignmentDoc short (propertyKeyDoc quoteAll k) ":" v
        (inPosC (.propValue false false) v (exprCore .none (.propValue false false) v))
  | .shorthand n => t n.val
  | .spread e => t "..." ++ inPosC .spreadArg e (exprCore .none .spreadArg e)
  | .method kind key typeParams params retType body =>
      methodDocOf kind (propertyKeyDoc quoteAll key) Doc.nil (tsTypeParamsDocOf false typeParams)
        typeParams params (paramDocs params) retType (tsAnnotation retType) (some body)
        (Doc.joinWith .hardline (statementDocs true true body))

def propertyDocsOf (quoteAll : Bool) : List MiniProperty → List Doc
  | [] => []
  | p :: rest => propertyDoc quoteAll p :: propertyDocsOf quoteAll rest

/-- One parameter, with its modifiers, its `?` and its type annotation.
A parameter written with a default value carries its annotation in front
of the `=`.  Prettier lays an object pattern out together with the `?`
and the annotation, as one group: the pattern is then what breaks when
the parameter does not fit, and the annotation may keep its line. -/
def paramDoc : MiniParam → Doc
  | .plain decorators mods (.withDefault (.object props rest) v) _ type =>
      paramDecoratorsDoc (decoratorDocs decorators)
        (tsParamModsDoc mods
          ++ .group (sepListOpen "{" "}" true (if rest.isNone then .es5 else .never)
                (objectPatternPropDocsOf (quoteAllPatternKeys props) props
                  ++ (match rest with
                      | none => []
                      | some r => [t "..." ++ patternDoc false r]))
              ++ tsAnnotation type)
          ++ t " = " ++ inPosC .arg v (exprCore .none .arg v))
  | .plain decorators mods (.withDefault q v) _ type =>
      paramDecoratorsDoc (decoratorDocs decorators)
        (tsParamModsDoc mods ++ patternDoc true q ++ tsAnnotation type
          ++ t " = " ++ inPosC .arg v (exprCore .none .arg v))
  | .plain decorators mods (.object props rest) isOptional type =>
      paramDecoratorsDoc (decoratorDocs decorators)
        (tsParamModsDoc mods
          ++ .group (sepListOpen "{" "}" true (if rest.isNone then .es5 else .never)
                (objectPatternPropDocsOf (quoteAllPatternKeys props) props
                  ++ (match rest with
                      | none => []
                      | some r => [t "..." ++ patternDoc false r]))
              ++ (if isOptional then t "?" else Doc.nil) ++ tsAnnotation type))
  | .plain decorators mods p isOptional type =>
      paramDecoratorsDoc (decoratorDocs decorators)
        (tsParamModsDoc mods ++ patternDoc true p
          ++ (if isOptional then t "?" else Doc.nil) ++ tsAnnotation type)
  | .rest decorators (.object props rest) type =>
      paramDecoratorsDoc (decoratorDocs decorators)
        (t "..."
          ++ .group (sepListOpen "{" "}" true (if rest.isNone then .es5 else .never)
                (objectPatternPropDocsOf (quoteAllPatternKeys props) props
                  ++ (match rest with
                      | none => []
                      | some r => [t "..." ++ patternDoc false r]))
              ++ tsAnnotation type))
  | .rest decorators p type =>
      paramDecoratorsDoc (decoratorDocs decorators)
        (t "..." ++ patternDoc true p ++ tsAnnotation type)

def paramDocs : List MiniParam → List Doc
  | [] => []
  -- the one parameter of a function, written with decorators of its own:
  -- the parameter list is not hugged then, but the object type of the
  -- annotation still has no group of its own, so that it breaks together
  -- with the decorators
  | [.plain (d :: ds) mods (.ident n) isOptional (some (.objectType members))] =>
      let items := tsTypeMemberDocsOf (quoteAllTypeMembers members) members
      let annotation :=
        t ": " ++ (if items.isEmpty then t "{}"
          else if mods.isEmpty then tsObjectTypeContent items
          else .group (tsObjectTypeContent items))
      [paramDecoratorsDoc (decoratorDocs (d :: ds))
        (tsParamModsDoc mods ++ patternDoc true (.ident n)
          ++ (if isOptional then t "?" else Doc.nil) ++ annotation)]
  -- the one parameter of a function prettier hugs is written without a
  -- group of its own, and so is its type annotation when that is an
  -- object type: the two then break together with the parameter list
  -- rather than on their own
  | [.plain [] mods p isOptional type] =>
      let hugged := mods.isEmpty && shouldHugParameter p type
      let annotation :=
        match type with
        | none => Doc.nil
        | some (.objectType members) =>
            let items := tsTypeMemberDocsOf (quoteAllTypeMembers members) members
            t ": " ++ (if items.isEmpty then t "{}"
              else if hugged then tsObjectTypeContent items
              else .group (tsObjectTypeContent items))
        | some ty => t ": " ++ tsTypeDoc .normal true 0 ty
      match p with
      | .withDefault q v =>
          [tsParamModsDoc mods
            ++ (if hugged then assignTargetPatternDoc q else patternDoc true q)
            ++ annotation ++ t " = " ++ inPosC .arg v (exprCore .none .arg v)]
      | q =>
          [tsParamModsDoc mods
            ++ (if hugged then assignTargetPatternDoc q else patternDoc true q)
            ++ (if isOptional then t "?" else Doc.nil) ++ annotation]
  | p :: rest => paramDoc p :: paramDocsTail rest

/-- The parameters that follow the first one, none of which is hugged:
prettier only hugs the parameter of a function that takes one. -/
def paramDocsTail : List MiniParam → List Doc
  | [] => []
  | p :: rest => paramDoc p :: paramDocsTail rest

def classElemDoc (quoteAll : Bool) (next : Option MiniClassElement) : MiniClassElement → Doc
  | .method decorators mods kind key isOptional typeParams params retType body =>
      decoratorsPrefix (decoratorDocs decorators)
        ++ tsMemberModsDoc mods
        ++ methodDocOf kind (propertyKeyDoc quoteAll key) (if isOptional then t "?" else Doc.nil)
            (tsTypeParamsDocOf false typeParams) typeParams params (paramDocs params) retType
            (tsAnnotation retType) body
            (match body with
              | none => Doc.nil
              | some body => Doc.joinWith .hardline (statementDocs true true body))
  | .field decorators mods isAccessor key isOptional isDefinite type init =>
      let keyDoc := propertyKeyDoc quoteAll key
        ++ (if isOptional then t "?" else Doc.nil)
        ++ (if isDefinite then t "!" else Doc.nil)
        ++ tsAnnotation type
      -- the decorators stand inside the left hand side of the assignment,
      -- as prettier writes them: a field which has one is a field whose
      -- left hand side holds a line, and so is never one whose value
      -- keeps the line of the `=` whatever it is
      let headDoc := decoratorsPrefix (decoratorDocs decorators)
        ++ tsMemberModsDoc mods
        ++ (if isAccessor then t "accessor " else Doc.nil)
      (match init with
        | none => headDoc ++ keyDoc
        | some e =>
            let valuePos : Pos := .propValue isAccessor true
            assignmentDoc false (headDoc ++ keyDoc) " =" e
              (inPosC valuePos e (exprCore .none valuePos e)))
        ++ fieldSemiDoc key type init next
  | .indexSig mods name keyType valueType =>
      tsMemberModsDoc mods
        -- the brackets of an index signature break around what they hold
        ++ t "[" ++ .group (.nest indentWidth
              (.softline ++ t (name.val ++ ": ") ++ tsTypeDoc .normal true 0 keyType)
            ++ .softline)
        ++ t "]: " ++ tsTypeDoc .normal true 0 valueType ++ semiDoc
  | .staticBlock body =>
      -- a string literal statement of a static block cannot be read as a
      -- directive, and so is never parenthesised
      t "static " ++ blockDocOf true (bodyIsEmpty body)
        (Doc.joinWith .hardline (statementDocs false false body))

def classElemDocsOf (quoteAll : Bool) : List MiniClassElement → List Doc
  | [] => []
  | el :: rest => classElemDoc quoteAll rest.head? el :: classElemDocsOf quoteAll rest

/-- The body of an arrow function, with the space or the line in front. -/
def arrowBodyDoc (chained breakChain jsxArg jsxParent : Bool) (bodyPos : Pos) :
    MiniArrowBody → Doc
  | .block body =>
      t " " ++ blockDocOf true (bodyIsEmpty body) (Doc.joinWith .hardline (statementDocs true true body))
  | .expr e =>
      let st : StartCtx := if jsxArg then jsxArrowBodyStart e else arrowBodyStart e
      arrowExprBodyOf chained breakChain (bodyPos == .hugArrowBody) jsxParent e
        (inPosStartC st bodyPos e (exprCore st bodyPos e))

/-- The signatures of the arrow functions that follow the first one of a
chain, and the document of the body at the end of the chain. -/
def arrowChainDocs (breakChain jsxParent : Bool) : MiniArrowBody → List Doc × Doc
  | .expr (.arrow isAsync tps ps retType b) =>
      let (sigs, bodyPart) := arrowChainDocs breakChain jsxParent b
      ((t (if isAsync then "async " else "")
          ++ arrowSignatureOf tps (tsTypeParamsDocOf true tps) ps (paramDocs ps) retType
              (tsArrowAnnotation retType)) :: sigs,
        bodyPart)
  | .expr e =>
      ([], arrowExprBodyOf true breakChain false jsxParent e
            (inPosStartC (arrowBodyStart e) .arrowBody e
              (exprCore (arrowBodyStart e) .arrowBody e)))
  | .block body =>
      ([], t " " ++ blockDocOf true (bodyIsEmpty body)
            (Doc.joinWith .hardline (statementDocs true true body)))

def declaratorDoc : MiniDeclarator → Doc
  | ⟨lhs, definite, type, init⟩ =>
      let annotation := (if definite then t "!" else Doc.nil) ++ tsAnnotation type
      match init with
      | none => patternDoc false lhs ++ annotation
      | some e =>
          -- `const x = (a = 1);`: an assignment used as an initialiser is
          -- parenthesised, which the position it stands in asks for
          let init :=
            inPosC (.assignRhs false false false false) e
              (exprCore .none (.assignRhs false false false false) e)
          let leftDoc := assignTargetPatternDoc lhs ++ annotation
          let leftCanBreak := Doc.canBreak leftDoc
          let complexLhs :=
            patternIsComplexDestructuring lhs
              || tsAnnotationIsComplex type
              || (leftCanBreak && (match e with | .arrow .. => true | _ => false))
          assignmentDocOf
            (chooseAssignLayout false false false complexLhs leftCanBreak false e)
            leftDoc " =" init

def declaratorDocs : List MiniDeclarator → List Doc
  | [] => []
  | d :: rest => declaratorDoc d :: declaratorDocs rest

def forInitDoc : MiniForInit → Doc
  | .none => Doc.nil
  | .expr e => inPosStartC .forInit .forHeadPart e (exprCore .forInit .forHeadPart e)
  | .decl kind ⟨hd, tl⟩ =>
      declarationDoc kind true
        (hd.init.isSome || tl.any (fun d => d.init.isSome))
        (declaratorDoc hd :: declaratorDocs tl)

/-- The binder of a `for (... in ...)` or of a `for (... of ...)`.  It may
not start with the identifier `let`, which is parenthesised there. -/
def forHeadDoc : MiniForHead → Doc
  | .pattern (.ident n) => if n.val == "let" then t "(let)" else t n.val
  | .pattern (.target e) => inPosStartC .forInHead .arg e (exprCore .forInHead .arg e)
  | .pattern p => patternDoc false p
  | .decl kind lhs => t (varKindText kind ++ " ") ++ patternDoc false lhs
  | .usingDecl isAwait lhs =>
      t (if isAwait then "await using " else "using ") ++ patternDoc false lhs

def switchCaseDoc : MiniSwitchCase → Doc
  | .case test body =>
      -- the test of a `case` is one more place TypeScript may read back
      -- differently than it was meant (a conditional type inside it ends
      -- in a `:`, which the parser may take for the one of the `case`),
      -- so the guarding mode writes parentheses of its own around it.
      -- They come in pairs: one pair alone is read as the parameters of
      -- an arrow function whose return type the `:` of the clause opens,
      -- which is the reading they are there to rule out.
      let testDoc := inPosC .caseTest test (exprCore .none .caseTest test)
      t "case "
        ++ (if ctx.guarded then t "((" ++ testDoc ++ t "))" else testDoc)
        ++ t ":" ++ caseBodyWith body (statementDocs false false body)
  | .default body => t "default:" ++ caseBodyWith body (statementDocs false false body)

def switchCaseDocs : List MiniSwitchCase → List Doc
  | [] => []
  | c :: rest => switchCaseDoc c :: switchCaseDocs rest

def catchDoc (collapseEmpty : Bool) : MiniCatchClause → Doc
  | ⟨param, type, guard, body⟩ =>
      t " catch (" ++ patternDoc true param ++ tsAnnotation type
        ++ (match guard with
            | none => Doc.nil
            | some g => t " if " ++ inPosC .ifTest g (exprCore .none .ifTest g))
        ++ t ") " ++ blockDocOf collapseEmpty (bodyIsEmpty body)
            (Doc.joinWith .hardline (statementDocs true false body))

def catchDocsAux (collapseEmpty : Bool) (acc : Doc) : List MiniCatchClause → Doc
  | [] => acc
  | c :: rest => catchDocsAux collapseEmpty (acc ++ catchDoc collapseEmpty c) rest

def tryTailDoc : MiniTryTail → Doc
  | .finallyOnly body =>
      t " finally " ++ blockDocOf false (bodyIsEmpty body)
        (Doc.joinWith .hardline (statementDocs true false body))
  | .catches ⟨hd, tl⟩ fin =>
      let hasFinally := match fin with | .none => false | .some _ => true
      catchDocsAux (!hasFinally) (catchDoc (!hasFinally) hd) tl
        ++ (match fin with
            | .none => Doc.nil
            | .some body =>
                t " finally " ++ blockDocOf false (bodyIsEmpty body)
                  (Doc.joinWith .hardline (statementDocs true false body)))

/-- A statement.  `collapseEmpty` says whether an empty block body is
written `{}`, which prettier does for the body of a loop and of a
function, but not for the body of an `if` or of a `for ... of`. -/
def statementDoc (collapseEmpty inList : Bool) : MiniStatement → Doc
  | .block body =>
      blockDocOf collapseEmpty (bodyIsEmpty body) (Doc.joinWith .hardline (statementDocs true false body))
  | .break_ none => t "break" ++ semiDoc
  | .break_ (some l) => t ("break " ++ l.val) ++ semiDoc
  | .continue_ none => t "continue" ++ semiDoc
  | .continue_ (some l) => t ("continue " ++ l.val) ++ semiDoc
  | .classDecl decorators isAbstract name typeParams heritage implements_ body =>
      -- prettier puts a decorated declaration and its decorators in a
      -- group of their own, which the decorators then break; a decorated
      -- class *expression* is left ungrouped, and so keeps its decorators
      -- on its line where the line around it is laid out flat
      (if decorators.isEmpty then id else Doc.group)
        (classDocOf (decoratorDocs decorators) isAbstract (some name)
          (tsTypeParamsDocOf false typeParams)
          (classHeritageGroupMode false heritage implements_)
          (match heritage with
            | none => Doc.nil
            | some ⟨he, hargs⟩ => inPosC .classHeritage he (exprCore .none .classHeritage he)
                ++ tsTypeArgsDoc hargs)
          (tsHeritageDocs implements_)
          body (classElemDocsOf (quoteAllMembers body) body))
  | .decl kind ⟨hd, tl⟩ =>
      declarationDoc kind false (hd.init.isSome || tl.any (fun d => d.init.isSome))
        (declaratorDoc hd :: declaratorDocs tl)
  | .using_ isAwait ⟨hd, tl⟩ =>
      declarationDocOf (if isAwait then "await using" else "using") false
        (hd.init.isSome || tl.any (fun d => d.init.isSome))
        (declaratorDoc hd :: declaratorDocs tl)
  | .debugger => t "debugger" ++ semiDoc
  | .doWhile body cond =>
      .group (t "do" ++ bodyClauseWith body (statementDoc true false body))
        ++ (if isBlockStmt body then t " " else .hardline)
        ++ t "while (" ++ conditionWith cond (inPosC .ifTest cond (exprCore .none .ifTest cond))
        ++ t ")" ++ semiDoc
  | .for_ init cond step body =>
      let noHead := (match init with | .none => true | _ => false)
        && cond.isNone && step.isNone
      if noHead then .group (t "for (;;)" ++ bodyClauseWith body (statementDoc true false body))
      else
        .group (t "for ("
          ++ .group (.nest indentWidth
              (.softline ++ ctx.forInit init ++ t ";" ++ .line
                ++ (match cond with
                    | none => Doc.nil
                    | some c => inPosC .forTest c (exprCore .none .forTest c))
                ++ t ";"
                ++ (match step with
                    | none => Doc.nil
                    | some s => .line ++ inPosC .forHeadPart s (exprCore .none .forHeadPart s)))
              ++ .softline)
          ++ t ")" ++ bodyClauseWith body (statementDoc true false body))
  | .forIn head obj body =>
      .group (t "for (" ++ forHeadDoc head ++ t " in "
        ++ inPosC .forInObject obj (exprCore .none .forInObject obj) ++ t ")"
          ++ bodyClauseWith body (statementDoc false false body))
  | .forOf isAwait head obj body =>
      .group (t (if isAwait then "for await (" else "for (") ++ forHeadDoc head ++ t " of "
        ++ inPosC .forInObject obj (exprCore .none .forInObject obj) ++ t ")"
          ++ bodyClauseWith body (statementDoc false false body))
  | .funcDecl isAsync isGen name typeParams params retType body =>
      functionDocOf false isAsync isGen (some name) typeParams
        (tsTypeParamsDocOf false typeParams) params (paramDocs params) retType
        (tsAnnotation retType) body
        (match body with
          | none => Doc.nil
          | some b => Doc.joinWith .hardline (statementDocs true true b))
  | .if_ cond thenS elseS =>
      -- `if (a) { if (b) c; } else d`: the consequent is written in a
      -- block when it could swallow the `else`
      let braced := elseS.isSome && !isBlockStmt thenS && endsWithDanglingIf thenS
      let thenDoc :=
        if braced then blockDocOf false false (statementDoc true false thenS)
        else statementDoc false false thenS
      let thenClause :=
        if braced then clauseDoc true false thenDoc else bodyClauseWith thenS thenDoc
      let opening :=
        .group (t "if (" ++ conditionWith cond (inPosC .ifTest cond (exprCore .none .ifTest cond)) ++ t ")" ++ thenClause)
      match elseS with
      | none => opening
      | some e =>
          opening
            ++ (if braced || isBlockStmt thenS then t " " else .hardline)
            ++ t "else"
            ++ .group
                (if isEmptyStmt e then t ";"
                  else if isBlockStmt e || isIfStmt e then t " " ++ statementDoc false false e
                  else .nest indentWidth (.line ++ statementDoc false false e))
  | .labelled l s =>
      if isEmptyStmt s then t (l.val ++ ":;") else t (l.val ++ ": ") ++ statementDoc false false s
  | .empty => t ";"
  | .expr e =>
      let outer := needsParensC .statement e || cannotStartStatement e
      -- the parentheses an object literal, a function or a class
      -- expression takes at the start of a statement belong to it, and are
      -- written even when the statement takes parentheses of its own
      let inner : StartCtx := if cannotStartStatement e then .none else .statement
      let d := parenIfExpr outer e (exprCore inner .statement e)
      -- a string literal statement of a program or of a block is
      -- parenthesised, so that it is not read as a directive
      let directiveLike := inList && (match e with | .string _ => true | _ => false)
      if !outer && (needsStatementParens e || directiveLike) then parens d ++ semiDoc
      else d ++ semiDoc
  | .return_ none => t "return" ++ semiDoc
  | .return_ (some e) => t "return " ++ returnArgWith e (inPosC .returnThrow e (exprCore .none .returnThrow e)) ++ semiDoc
  | .throw e => t "throw " ++ returnArgWith e (inPosC .returnThrow e (exprCore .none .returnThrow e)) ++ semiDoc
  | .switch disc cases =>
      .group (t "switch ("
          ++ .nest indentWidth (.softline ++ inPosC .ifTest disc (exprCore .none .ifTest disc))
          ++ .softline ++ t ")")
        ++ t " {"
        ++ (if cases.isEmpty then Doc.nil
            else .nest indentWidth (.hardline ++ Doc.joinWith .hardline (switchCaseDocs cases)))
        ++ .hardline ++ t "}"
  | .try_ body tail =>
      t "try " ++ blockDocOf false (bodyIsEmpty body)
          (Doc.joinWith .hardline (statementDocs true false body))
        ++ tryTailDoc tail
  | .while_ cond body =>
      .group (t "while (" ++ conditionWith cond (inPosC .ifTest cond (exprCore .none .ifTest cond)) ++ t ")" ++ bodyClauseWith body (statementDoc true false body))
  | .with_ obj body =>
      .group (t "with ("
        ++ conditionWith obj (inPosC .withObject obj (exprCore .none .withObject obj))
        ++ t ")" ++ bodyClauseWith body (statementDoc false false body))
  | .typeAlias name typeParams type =>
      -- a union on the right of the `=` is laid out the way prettier lays
      -- out an assignment it breaks after the operator: the members of the
      -- union are not indented again
      let breakAfter :=
        match type with
        | .union types => !tsUnionShouldHug types
        -- a conditional type whose check or `extends` type is written
        -- with type arguments stands below the `=`; under
        -- `experimentalTernaries` every conditional type does
        | .conditional check ext _ _ =>
            Options.experimentalTernaries ||
              let parameterised : MiniTsType → Bool
                | .ref _ (_ :: _) => true
                | .fn (_ :: _) _ _ => true
                | _ => false
              parameterised check || parameterised ext
        | _ => false
      -- several type parameters of which one is written with a constraint
      -- or with a default break before the `=` does
      let complexParams :=
        1 < typeParams.length
          && typeParams.any (fun tp => tp.constraint.isSome || tp.default_.isSome)
      assignmentDocOf
          (if breakAfter then .breakAfterOperator
            else if complexParams then .breakLhs else .fluid)
          (t ("type " ++ name.val) ++ tsTypeParamsDocOf false typeParams) " ="
          (tsTypeDoc .normal (!breakAfter) 0 type)
        ++ semiDoc
  | .interface_ name typeParams extends_ members =>
      let head := t ("interface " ++ name.val) ++ tsTypeParamsDocOf false typeParams
      let bodyDoc := tsInterfaceBodyDoc (tsTypeMemberDocsOf (quoteAllTypeMembers members) members)
      if extends_.isEmpty then head ++ t " " ++ bodyDoc
      else
        let clause :=
          .group (t "extends"
            ++ .nest indentWidth
                (.line ++ Doc.joinWith (t "," ++ .line) (tsHeritageDocs extends_)))
        -- an interface which extends one thing keeps `extends` on the
        -- line of its name, however long the name that follows it is;
        -- one which extends several writes the clause on a line of its
        -- own once the line is too long
        if extends_.length == 1 then
          head ++ t " extends "
            ++ Doc.concat (tsHeritageDocs extends_) ++ t " " ++ bodyDoc
        else
          .condGroup (head ++ t " " ++ clause ++ t " " ++ bodyDoc)
            (head ++ .nest indentWidth (.hardline ++ clause) ++ t " " ++ bodyDoc)
  | .enum_ isConst name members =>
      t ((if isConst then "const enum " else "enum ") ++ name.val ++ " ")
        ++ (if members.isEmpty then t "{}"
            else
              t "{" ++ .nest indentWidth
                  (.hardline
                    ++ Doc.joinWith (t "," ++ .hardline)
                        (tsEnumMemberDocsOf (quoteAllEnumMembers members) members)
                    ++ (if Options.hasTrailingComma .es5 then t "," else .nil))
                ++ .hardline ++ t "}")
  | .namespaceDecl isModuleKeyword name body =>
      let headDoc :=
        match name with
        | .qualified names =>
            t ((if isModuleKeyword then "module " else "namespace ")
              ++ String.intercalate "." (names.toList.map (fun n => n.val)))
        | .str v => t ("module " ++ strLit v)
        | .global => t "global"
      match body with
      -- `declare module "foo";`, an ambient module with no body at all
      | none => headDoc ++ semiDoc
      | some body =>
        headDoc ++ t " "
          ++ (if body.all isEmptyItem then t "{}"
              else
                t "{" ++ .nest indentWidth
                    (.hardline ++ Doc.joinWith .hardline (namespaceItemDocs body))
                  ++ .hardline ++ t "}")
  | .declare_ s => t "declare " ++ statementDoc false false s

/-- The statements of a body; the empty statement is dropped.  `inList`
says whether the statements are those of a program or of a block, where a
string literal statement that is not a directive is parenthesised;
`prologue` says whether a string literal statement here would still be one
of the directives of a program or of a function body. -/
def statementDocs (inList prologue : Bool) : List MiniStatement → List Doc
  | [] => []
  | .empty :: rest => statementDocs inList prologue rest
  | s :: rest =>
      let directive := prologue && isStringStmt s
      asiGuard s (statementDoc false (inList && !directive) s)
        :: statementDocs inList directive rest

/-- An `export` declaration. -/
def exportDoc : MiniExportDeclaration → Doc
  | .fromClause isType specs mod attrs =>
      t "export " ++ (if isType then t "type " else Doc.nil) ++ specifiersDoc specs
        ++ t (" from " ++ strLit mod.val) ++ importAttrsDoc attrs ++ semiDoc
  | .locals isType specs =>
      t "export " ++ (if isType then t "type " else Doc.nil) ++ specifiersDoc specs ++ semiDoc
  | .all isType alias_ mod attrs =>
      t "export " ++ (if isType then t "type " else Doc.nil) ++ t "*"
        ++ (match alias_ with | none => Doc.nil | some n => t (" as " ++ n.val))
        ++ t (" from " ++ strLit mod.val) ++ importAttrsDoc attrs ++ semiDoc
  -- `export default function () {}` and `export default class {}` are
  -- declarations, which take no semicolon; anything whose leftmost token
  -- opens a function or a class is parenthesised, so that it is not read
  -- as one of them
  | .defaultExpr (.func isAsync isGen name typeParams params retType body) =>
      t "export default "
        ++ functionDocOf false isAsync isGen name typeParams
            (tsTypeParamsDocOf false typeParams) params (paramDocs params) retType
            (tsAnnotation retType) (some body)
            (Doc.joinWith .hardline (statementDocs true true body))
  -- the decorators of an exported class stand on their own line, below
  -- the `export` keyword
  | .defaultExpr (.classExpr decorators name typeParams heritage implements_ body) =>
      t "export default" ++ (if decorators.isEmpty then t " " else Doc.hardline)
        ++ classDocOf (decoratorDocs decorators) false name (tsTypeParamsDocOf false typeParams)
            (classHeritageGroupMode false heritage implements_)
            (match heritage with
              | none => Doc.nil
              | some ⟨he, hargs⟩ => inPosC .classHeritage he (exprCore .none .classHeritage he)
                  ++ tsTypeArgsDoc hargs)
            (tsHeritageDocs implements_) body (classElemDocsOf (quoteAllMembers body) body)
  | .defaultExpr e =>
      t "export default "
        ++ parenIfExpr (needsParens .generic e || startsWithFunctionOrClass e) e
            (exprCore .none .generic e)
        ++ semiDoc
  -- `export default abstract class A {}` and `export default interface I {}`,
  -- the declarations that are no expression
  | .defaultDecl (.classDecl decorators isAbstract name typeParams heritage implements_ body) =>
      t "export default" ++ (if decorators.isEmpty then t " " else Doc.hardline)
        ++ classDocOf (decoratorDocs decorators) isAbstract (some name)
            (tsTypeParamsDocOf false typeParams)
            (classHeritageGroupMode false heritage implements_)
            (match heritage with
              | none => Doc.nil
              | some ⟨he, hargs⟩ => inPosC .classHeritage he (exprCore .none .classHeritage he)
                  ++ tsTypeArgsDoc hargs)
            (tsHeritageDocs implements_) body (classElemDocsOf (quoteAllMembers body) body)
  | .defaultDecl s => t "export default " ++ statementDoc false false s
  | .decl (.classDecl decorators isAbstract name typeParams heritage implements_ body) =>
      t "export" ++ (if decorators.isEmpty then t " " else Doc.hardline)
        ++ classDocOf (decoratorDocs decorators) isAbstract (some name)
            (tsTypeParamsDocOf false typeParams)
            (classHeritageGroupMode false heritage implements_)
            (match heritage with
              | none => Doc.nil
              | some ⟨he, hargs⟩ => inPosC .classHeritage he (exprCore .none .classHeritage he)
                  ++ tsTypeArgsDoc hargs)
            (tsHeritageDocs implements_) body (classElemDocsOf (quoteAllMembers body) body)
  | .decl s => t "export " ++ statementDoc false false s
  | .assign e =>
      t "export = " ++ inPosC .tsExportAssign e (exprCore .none .tsExportAssign e) ++ semiDoc
  | .asNamespace n => t ("export as namespace " ++ n.val) ++ semiDoc

/-- One item of a program.  `inList` says that a string literal statement
here is no longer one of the directives of the program, and so is
parenthesised. -/
def moduleItemDoc (inList : Bool) : MiniModuleItem → Doc
  | .stmt s => asiGuard s (statementDoc false inList s)
  | .importDecl d => importDoc d
  | .exportDecl d => exportDoc d

/-- The documents of the items of a program.  `prologue` says whether a
string literal statement here is still one of the directives of the
program. -/
def moduleItemDocs (prologue : Bool) : List MiniModuleItem → List Doc
  | [] => []
  | i :: rest =>
      if isEmptyItem i then moduleItemDocs prologue rest
      else
        let directive := prologue && isStringItem i
        moduleItemDoc (!directive) i :: moduleItemDocs directive rest

/-- The documents of the items of the body of a namespace or of a module
declaration.  A string literal statement there is no directive, and is
not read back as one either, so prettier writes it with no parentheses
of its own wherever it stands. -/
def namespaceItemDocs : List MiniModuleItem → List Doc
  | [] => []
  | i :: rest =>
      if isEmptyItem i then namespaceItemDocs rest
      else moduleItemDoc false i :: namespaceItemDocs rest

end
end

/-- The head of a `for (;;)`: the place where prettier parenthesises every
`in` operator written in it. -/
partial def forInitHeadDocOf (guard : Bool) (init : MiniForInit) : Doc :=
  forInitDoc
    { inForInit := true, guarded := guard, forInit := forInitHeadDocOf guard }
    init

/-- The head of a `for (;;)`, printed in the ordinary mode. -/
def forInitHeadDoc (init : MiniForInit) : Doc := forInitHeadDocOf false init

/-- The context anything outside the head of a `for (;;)` is printed in. -/
def topCtx : PrintCtx := { inForInit := false, forInit := forInitHeadDoc }

/-- The context of the mode which writes the parentheses that say what
the text means. -/
def guardCtx : PrintCtx :=
  { inForInit := false, guarded := true,
    forInit := forInitHeadDocOf true }


/-! ### Document builders for AST nodes -/

/-- An expression in position `pos`. -/
def exprDoc (pos : Pos) (e : MiniExpr) : Doc := inPos pos e (exprCore topCtx .none pos e)

/-- The object of a `.` or `[]` access. -/
def memberObjectDoc (e : MiniExpr) : Doc := exprDoc (.memberObject false false false) e

/-- The callee of a call. -/
def calleeDoc (e : MiniExpr) : Doc := exprDoc (.callee false 0) e

/-- The argument list of a call. -/
def argsDoc (args : List MiniExpr) : Doc :=
  argumentsDoc (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
    (canHugLastArg args) (argDocs topCtx .none args) (argHugFirstDocs topCtx .none false args)
    (argHugDocs topCtx .none false args)

/-- A parameter list. -/
def paramsDoc (params : List MiniParam) : Doc :=
  paramListDocOf params (paramDocs topCtx params)

/-- A type expression. -/
def typeDoc (ty : MiniTsType) : Doc := tsTypeDoc topCtx .normal true 0 ty

def arrayDoc (els : List MiniArrayElement) : Doc := arrayDocOf els (arrayItemDocs topCtx els)

def classBodyDoc (body : List MiniClassElement) : Doc := classBodyOf body (classElemDocsOf topCtx (quoteAllMembers body) body)

def classElementDoc (el : MiniClassElement) : Doc := classElemDoc topCtx false none el

/-- A binding pattern. -/
def patternDocOf (p : MiniPattern) : Doc := patternDoc topCtx false p

/-- One decorator, `@expr`. -/
def decoratorDoc (e : MiniExpr) : Doc := t "@" ++ exprDoc .decorator e

def classDoc (decorators : List MiniExpr) (isAbstract : Bool) (name : Option NEString)
    (typeParams : List MiniTsTypeParam) (heritage : Option MiniClassHeritage)
    (implements_ : List MiniTsHeritage) (body : List MiniClassElement) : Doc :=
  classDocOf (decoratorDocs topCtx decorators) isAbstract name
    (tsTypeParamsDocOf topCtx false typeParams)
    (classHeritageGroupMode false heritage implements_)
    (match heritage with
      | none => Doc.nil
      | some h => exprDoc .classHeritage h.expr ++ tsTypeArgsDoc topCtx h.typeArgs)
    (tsHeritageDocs topCtx implements_)
    body (classElemDocsOf topCtx (quoteAllMembers body) body)

def methodDoc (kind : MethodKind) (key : MiniPropertyName)
    (params : List MiniParam) (body : List MiniStatement) : Doc :=
  methodDocOf kind (propertyKeyDoc topCtx false key) Doc.nil Doc.nil [] params
    (paramDocs topCtx params) none Doc.nil (some body)
    (Doc.joinWith .hardline (statementDocs topCtx true true body))

def functionDoc (isAsync isGen : Bool) (name : Option NEString)
    (params : List MiniParam) (body : List MiniStatement) : Doc :=
  functionDocOf false isAsync isGen name [] Doc.nil params (paramDocs topCtx params) none Doc.nil
    (some body) (Doc.joinWith .hardline (statementDocs topCtx true true body))

/-- A statement list, one statement per line. -/
def statementsDoc (body : List MiniStatement) : Doc :=
  Doc.joinWith .hardline (statementDocs topCtx true false body)

/-- A brace enclosed statement list. -/
def blockDoc (body : List MiniStatement) : Doc :=
  blockDocOf false (bodyIsEmpty body) (statementsDoc body)

/-- The name of a property or of a method. -/
def propertyNameDoc (k : MiniPropertyName) : Doc := propertyKeyDoc topCtx false k

def programDoc (p : MiniProgram) : Doc :=
  Doc.joinWith .hardline (moduleItemDocs topCtx true (p.items.filter (fun i => !isEmptyItem i)))

/-- A program printed with the parentheses that make TypeScript read the
text back as the tree it was printed from. -/
def programGuardedDoc (p : MiniProgram) : Doc :=
  Doc.joinWith .hardline (moduleItemDocs guardCtx true (p.items.filter (fun i => !isEmptyItem i)))

end Printer

/-! ## Entry points -/

/-- Lay out a document under the given options: at their `printWidth`,
with their indentation style, and with their line terminator. -/
def renderDoc (opts : Options) (d : Doc) : String :=
  Doc.renderWith { tabWidth := opts.tabWidth, useTabs := opts.useTabs }
    opts.endOfLine.text opts.printWidth d

/-- Print a program under the given options, preceded by the interpreter
directive (the `#!` line) the file starts with, if it has one.  Prettier
writes the directive on the first line and keeps its text as it finds
it. -/
def printFileWith (opts : Options) (interpreter : Option String) (p : MiniProgram) : String :=
  let eol := opts.endOfLine.text
  let shebang := match interpreter with | none => "" | some s => "#!" ++ s ++ eol
  -- a program prettier writes nothing for -- one with no items, or one
  -- whose items are all the empty statement, which prettier drops -- is
  -- not a blank line either
  if (p.items.filter (fun i => !Printer.isEmptyItem i)).isEmpty then shebang
  else shebang ++ renderDoc opts (Printer.programDoc (o := opts) p) ++ eol

/-- Print a program under the given options. -/
def printProgramWith (opts : Options) (p : MiniProgram) : String :=
  printFileWith opts none p

/-- Print a program in the canonical style, at a given line width,
preceded by the interpreter directive the file starts with, if it has
one. -/
def printFileWidth (interpreter : Option String) (width : Nat) (p : MiniProgram) : String :=
  printFileWith { printWidth := width } interpreter p

/-- Print a program in the canonical style, at a given line width. -/
def printProgramWidth (width : Nat) (p : MiniProgram) : String :=
  printFileWidth none width p

/-- Print a program, under the given options, with the parentheses which
say what it means where TypeScript would otherwise read the text back as
another tree: around an instantiation expression, `f<T>`, and around the
test of a `case`.  The text is not the canonical one — prettier writes no
such parentheses — but it holds the tree the printer means, which is what
lets prettier be asked what it writes for that tree. -/
def printProgramGuardedWith (opts : Options) (interpreter : Option String)
    (p : MiniProgram) : String :=
  let eol := opts.endOfLine.text
  let shebang := match interpreter with | none => "" | some s => "#!" ++ s ++ eol
  if (p.items.filter (fun i => !Printer.isEmptyItem i)).isEmpty then shebang
  else shebang ++ renderDoc opts (Printer.programGuardedDoc (o := opts) p) ++ eol

/-- Print a program with those parentheses, at a given line width. -/
def printProgramGuardedWidth (interpreter : Option String) (width : Nat)
    (p : MiniProgram) : String :=
  printProgramGuardedWith { printWidth := width } interpreter p

/-- Print a program in the canonical style: two space indentation, double
quotes, semicolons, and lines of at most 80 columns. -/
def printProgram (p : MiniProgram) : String :=
  printProgramWith defaultOptions p

/-- Print a file in the canonical style: the interpreter directive, if the
file has one, and then the program. -/
def printFile (interpreter : Option String) (p : MiniProgram) : String :=
  printFileWith defaultOptions interpreter p

/-- Print a single statement under the given options. -/
def printStatementWith (opts : Options) (s : MiniStatement) : String :=
  renderDoc opts (Printer.statementDoc (o := opts) Printer.topCtx false true s)

/-- Print a single statement. -/
def printStatement (s : MiniStatement) : String :=
  printStatementWith defaultOptions s

/-- Print a single expression under the given options. -/
def printExprWith (opts : Options) (e : MiniExpr) : String :=
  renderDoc opts (Printer.exprDoc (o := opts) .statement e)

/-- Print a single expression. -/
def printExpr (e : MiniExpr) : String :=
  printExprWith defaultOptions e

end Language.TypeScript.MiniTsAST

