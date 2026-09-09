/-
Tests for the scope safe AST: `BrujinAST`, the conversion of a `MiniAST`
tree into it (`BrujinOfMini`) and back (`BrujinToMini`), and the printer
that goes with it.

There is no Haskell counterpart for these — the scope safe AST is an
addition to the port — so the expected values were written here.

Each case reads JavaScript source, converts it into a scope safe tree, and
prints the tree back.  Since the tree stores no names, the printed program
shows exactly what the conversion resolved: `_cN` is the const variable of
level `N`, `_mN` the mutable one, and a name that stayed a name is one that
was not bound anywhere (the `unsafeGlobal` escape hatch).
-/
import Spec
import LanguageJavascriptBrujin.AST
import LanguageJavascriptBrujin.OfMini
import LanguageJavascriptBrujin.ToMini

namespace LanguageJavascriptTests.Brujin.AST

open Spec
open Spec.Assert
open Language.JavaScript.BrujinAST

/-- Read source into a scope safe tree and print it back. -/
def brujinRender (src : String) : String :=
  match parse src with
  | .ok p => printProgram p
  | .error e => "ERROR: " ++ e

/-- Does the printed program read back as the same scope safe tree? -/
def brujinStable (src : String) : String :=
  match parse src with
  | .ok p =>
      toString (match parse (printProgram p) with | .ok q => q == p | .error _ => false)
  | .error e => "ERROR: " ++ e

/-! ## What the conversion resolves -/

def resolveCases : List (String × String × String) :=
  [ ("const, let, a function and a global",
      brujinRender
        "const a = 1; let b = a + 2; function f(x, y) { return x + y + a; } console.log(f(a, b));",
      ("const _c0 = 1;\nlet _m0 = _c0 + 2;\nfunction _c1(_m1, _m2) {\n"
        ++ "  return _m1 + _m2 + _c0;\n}\nconsole.log(_c1(_c0, _m0));\n"))
    -- the binder of `for (const ...)` is a const, that of `for (let ...)` a mutable cell
  , ("the two kinds of for binder",
      brujinRender "for (const x of xs) { total += x; } for (let i = 0; i < 10; i++) { g(i); }",
      ("for (const _c0 of xs) {\n  total += _c0;\n}\nfor (let _m0 = 0; _m0 < 10; _m0++) {\n"
        ++ "  g(_m0);\n}\n"))
    -- an imported name is a const binding, and so is a class declaration
  , ("an import binds const variables",
      brujinRender "import def, { a as b } from 'mod'; export { def }; export const q = b;",
      "import _c0, { a as _c1 } from \"mod\";\nexport { _c0 as def };\nexport const _c2 = _c1;\n")
  , ("a namespace import",
      brujinRender "import * as ns from 'm'; ns.f();",
      "import * as _c0 from \"m\";\n_c0.f();\n")
  , ("a re-export does not mention a local name",
      brujinRender "export { a as b } from 'm';", "export { a as b } from \"m\";\n")
  , ("an exported mutable binding",
      brujinRender "let x = 1; export { x };", "let _m0 = 1;\nexport { _m0 as x };\n")
    -- the binder of a catch clause is a mutable cell
  , ("try/catch/finally",
      brujinRender "try { f() } catch (e) { console.log(e) } finally { done() }",
      ("try {\n  f();\n} catch (_m0) {\n  console.log(_m0);\n} finally {\n  done();\n}\n"))
    -- a class is in scope in its own body, an object shorthand loses its name
  , ("a class and an object literal",
      brujinRender
        "class C extends D { m(a) { return new C(a); } } const o = { x, y: 2, m(z) { return z } };",
      ("class _c0 extends D {\n  m(_m0) {\n    return new _c0(_m0);\n  }\n}\nconst _c1 = {\n"
        ++ "  x: x,\n  y: 2,\n  m(_m0) {\n    return _m0;\n  },\n};\n"))
  , ("shadowing",
      brujinRender "let x = 1; { let x = 2; g(x); } g(x);",
      "let _m0 = 1;\n{\n  let _m1 = 2;\n  g(_m1);\n}\ng(_m0);\n")
  , ("a closure captures by index",
      brujinRender "const f = (a) => (b) => a + b;",
      "const _c0 = (_m0) => (_m1) => _m0 + _m1;\n")
  , ("a function is in scope in its own body",
      brujinRender "function outer() { function inner() { return outer; } return inner(); }",
      ("function _c0() {\n  function _c1() {\n    return _c0;\n  }\n  return _c1();\n}\n"))
  , ("a named function expression",
      brujinRender "const f = function g(n) { return n < 2 ? 1 : n * g(n - 1); };",
      ("const _c0 = function _c0(_m0) {\n  return _m0 < 2 ? 1 : _m0 * _c0(_m0 - 1);\n};\n"))
    -- there is no hoisting: a name used before its declaration is a global
  , ("no hoisting: a use before the declaration is an unsafeGlobal",
      brujinRender "g(); function g() {}", "g();\nfunction _c0() {}\n")
  , ("a declaration of several variables is split",
      brujinRender "let a, b = 2; a = b;", "let _m0;\nlet _m1 = 2;\n_m0 = _m1;\n")
  , ("a switch",
      brujinRender "switch (v) { case 1: h(); break; default: k(); }",
      "switch (v) {\n  case 1:\n    h();\n    break;\n  default:\n    k();\n}\n")
  , ("a template literal and a do/while",
      brujinRender "const t = `a${x}b${y}c`; do { i++; } while (i < 3);",
      "const _c0 = `a${x}b${y}c`;\ndo {\n  i++;\n} while (i < 3);\n")
  , ("for (... in ...) over an existing target",
      brujinRender "for (k in obj) { p(k); }", "for (k in obj) {\n  p(k);\n}\n")
  , ("getters, setters and generators",
      brujinRender "const s = { get a() { return 1 }, set a(v) { q(v) }, *gen() { yield 1 } };",
      ("const _c0 = {\n  get a() {\n    return 1;\n  },\n  set a(_m0) {\n    q(_m0);\n  },\n"
        ++ "  *gen() {\n    yield 1;\n  },\n};\n"))
  , ("async and await",
      brujinRender "async function af(x) { const y = await x; return y; }",
      "async function _c0(_m0) {\n  const _c1 = await _m0;\n  return _c1;\n}\n")
  , ("members as assignment targets",
      brujinRender "const o = {}; o.x = 1; o['y']++;",
      "const _c0 = {};\n_c0.x = 1;\n_c0[\"y\"]++;\n")
  , ("a labelled block",
      brujinRender "label: { f(); }", "label: {\n  f();\n}\n")
  , ("a labelled loop with continue",
      brujinRender "outer: while (x) { continue outer; }",
      "outer: while (x) {\n  continue outer;\n}\n")
  , ("holes and spread in an array literal",
      brujinRender "const xs = [1, , 2, ...rest];", "const _c0 = [1, , 2, ...rest];\n")
  , ("an empty statement is dropped",
      brujinRender "f();;;g();", "f();\ng();\n")
  , ("throw", brujinRender "throw new Error('x');", "throw new Error(\"x\");\n")
  ]

/-! ## The conversion is faithful

Reading the printed program back has to give the very same tree — which,
since the names are generated from the tree, is exactly the statement that
no scope information was lost. -/

def brujinStableSources : List String :=
  [ "const a = 1; let b = a + 2; function f(x, y) { return x + y + a; } console.log(f(a, b));"
  , "for (const x of xs) { total += x; } for (let i = 0; i < 10; i++) { g(i); }"
  , "import def, { a as b } from 'mod'; export { def }; export const q = b;"
  , "import * as ns from 'm'; ns.f();"
  , "import 'side-effect';"
  , "export { a as b } from 'm';"
  , "try { f() } catch (e) { console.log(e) } finally { done() }"
  , "try { f() } finally { done() }"
  , "class C extends D { static s() { return 1 } m(a) { return new C(a); } }"
  , "let x = 1; { let x = 2; g(x); } g(x);"
  , "const f = (a) => (b) => a + b;"
  , "function outer() { function inner() { return outer; } return inner(); }"
  , "const f = function g(n) { return n < 2 ? 1 : n * g(n - 1); };"
  , "const C = class Self { m() { return Self; } };"
  , "let a, b = 2; a = b;"
  , "switch (v) { case 1: h(); break; default: k(); }"
  , "const t = `a${x}b${y}c`; do { i++; } while (i < 3);"
  , "for (k in obj) { p(k); } for (const k of ks) { p(k); }"
  , "const s = { get a() { return 1 }, set a(v) { q(v) }, *gen() { yield 1 } };"
  , "async function af(x) { const y = await x; return y; }"
  , "if (a) { f(); } else { g(); }"
  , "if (a) f(); else g();"
  , "const o = {}; o.x = 1; o['y']++; --o.z;"
  , "label: { f(); } outer: while (x) { continue outer; }"
  , "function* gen(a, b) { yield a; yield* b; }"
  ]

/-! ## What the scope safe AST rules out -/

def errorCases : List (String × String × String) :=
  [ ("assignment to a const variable", brujinRender "const c = 1; c = 2;",
      "ERROR: BrujinAST: assignment to the const variable c")
  , ("a destructuring binder", brujinRender "var {a, b} = obj;",
      "ERROR: BrujinAST: a destructuring pattern in a binder")
  , ("a default parameter value", brujinRender "function f(a = 1) {}",
      "ERROR: BrujinAST: a default value in a binder")
  , ("with", brujinRender "with (o) { f(); }",
      "ERROR: BrujinAST: a `with` statement (its scope is dynamic)")
  , ("a catch guard", brujinRender "try { a() } catch (e if b) { c() }",
      "ERROR: BrujinAST: a catch clause with a guard")
  , ("a for clause with two declarators", brujinRender "for (let i = 0, j = 1; i < j; i++) {}",
      "ERROR: BrujinAST: a `for` clause that declares several variables")
  , ("a labelled declaration", brujinRender "l: let x = 1;",
      "ERROR: BrujinAST: a labelled statement that declares a variable")
  ]

/-! ## Trees written by hand

A `BrujinAST` value is written directly, without going through source; the
type of a variable is what keeps it in scope. -/

/-- `(x) => x`, in the empty scope. -/
def identityFn : Expr 0 0 := .arrow 1 (.expr (.mutVar 0))

/-- `(x, y) => x + y`: the *first* parameter is the *last* index. -/
def plusFn : Expr 0 0 := .arrow 2 (.expr (.binary (.mutVar 1) .plus (.mutVar 0)))

/-- An expression that mentions the two variables of its scope and a
global; it only typechecks in a scope with a const and a mutable one. -/
def usesBoth : Expr 1 1 :=
  .call (.unsafeGlobal ⟨"print", by decide⟩)
    (.cons (.binary (.constVar 0) .plus (.mutVar 0)) .nil)

/-- `const x = 1; print(x);` -/
def tinyProgram : Program :=
  ⟨.cons (.stmt (.constDecl (.number ⟨"1", by decide⟩)))
    (.cons (.stmt (.expr (.call (.unsafeGlobal ⟨"print", by decide⟩)
      (.cons (.constVar 0) .nil)))) .nil)⟩

def spec : Spec := do
  describe "BrujinAST Scope Resolution" do
    for (label, actual, expected) in resolveCases do
      it label do
        shouldEqual actual expected

  describe "BrujinAST Stability" do
    for src in brujinStableSources do
      it ("stable: " ++ src) do
        shouldEqual (brujinStable src) "true"

  describe "BrujinAST Errors" do
    for (label, actual, expected) in errorCases do
      it label do
        shouldEqual actual expected

  describe "BrujinAST Hand Written" do
    it "the identity function" do
      shouldEqual (printExpr identityFn) "(_m0) => _m0"
    it "the first parameter has the last index" do
      shouldEqual (printExpr plusFn) "(_m0, _m1) => _m0 + _m1"
    it "an expression in a scope of its own" do
      shouldEqual (printExpr usesBoth) "print(_c0 + _m0)"
    it "a program written by hand" do
      shouldEqual (printProgram tinyProgram) "const _c0 = 1;\nprint(_c0);\n"
    it "and it reads back as itself" do
      shouldEqual (toString (match parse (printProgram tinyProgram) with
        | .ok q => q == tinyProgram
        | .error _ => false)) "true"

end LanguageJavascriptTests.Brujin.AST
