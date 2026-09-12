/-
Tests for the modern syntax the three trees model: optional chaining
(`a?.b`, `a?.[i]`, `f?.(x)`), the nullish operators `??` and `??=`, private
class members (`#x`, `this.#x`, `#x in o`), class fields and static
initialisation blocks, decorators, `import.meta`, dynamic `import()`, and
the binding patterns — a default value and a destructuring pattern — that
a parameter, a declarator, a `for ... of` head or a `catch` binder may use.
It also covers the syntax added afterwards: `super.x`, `super[i]` and
`super(...)`, `new.target`, a labelled declaration and a labelled function
declaration, `using`/`await using` and `await` at the top level of a
module, and `export * as ns from "m"`, `export default <expression>` and
the import attributes of a static `import`.

Each construct is checked in all three trees:

* the annotated tree reproduces the source character for character,
  comments and layout included;
* the deterministic tree prints it in the canonical style, the printed
  program reads back as the same tree, and so does the trip through the
  annotated tree;
* the scope safe tree resolves the variables of the construct and prints
  it back (the two binding patterns are refused there, as the module note
  of `BrujinAST` says, and the error naming the form it met is pinned).
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.Printer
import LanguageJavascriptMini.OfFull
import LanguageJavascriptMini.ToFull
import LanguageJavascriptMini.Printer
import LanguageJavascriptBrujin.OfMini
import LanguageJavascriptBrujin.ToMini

namespace LanguageJavascriptTests.Modern

open Spec
open Spec.Assert
open Language.JavaScript.Parser
open Language.JavaScript.Pretty

/-! ## The annotated tree: the source comes back unchanged -/

/-- Sources the annotated tree has to reproduce exactly. -/
def annotatedCases : List String :=
  [ "a?.b"
  , "a?.[b]"
  , "a?.(b)"
  , "a?.b.c"
  , "(a?.b).c"
  , "a ?? b"
  , "a ??= b"
  , "a ||= b"
  , "a &&= b"
  , "class A { #x = 1 ; static y = 2 ; static { z() ; } m () { return this.#x ; } }"
  , "#x in a"
  , "@dec class A {}"
  , "class A { @dec m () {} }"
  , "class A { @d1 @d2 static #p = 3 ; }"
  , "import.meta.url"
  , "import('x')"
  , "import('x', {with: {type: 'json'}})"
  , "x = {...a}"
  , "var {a = 1} = x"
  , "var {a, ...r} = x"
  , "var [a, , b, ...c] = x"
  , "function f (a = 1, {b, c: d = 2}, ...rest) {}"
  , "for (const {a} of xs) {}"
  , "try { } catch ({message}) { }"
  , "[a, b] = xs"
  , "({a} = o)"
  , "(a = 1) => a"
    -- the comments and the layout of the new syntax come back too
  , "/*a*/x/*b*/?./*c*/y"
  , "/*a*/x/*b*/?./*c*/(/*d*/1/*e*/)"
  , "/*a*/x/*b*/?./*c*/[/*d*/1/*e*/]"
  , "/*a*/x/*b*/??/*c*/y"
  , "/*a*/x/*b*/??=/*c*/y"
  , "/*a*/class/*b*/A/*c*/{/*d*/static/*e*/{/*f*/}/*g*/}"
  , "/*a*/@/*b*/dec/*c*/class/*d*/A/*e*/{/*f*/}"
  , "/*a*/import/*b*/./*c*/meta/*d*/"
  , "/*a*/import/*b*/(/*c*/'x'/*d*/)"
  , "class A { /*a*/#x/*c*/=/*d*/1/*e*/; }"
  , "/*a*/#x/*c*/in/*d*/o"
    -- `super`, `new.target`, `using` and a labelled declaration
  , "class A extends B { constructor ( x ) { super ( x ) ; } }"
  , "class A extends B { m () { return super [ i ] ; } }"
  , "class A extends B { m () { super.x = 1 ; } }"
  , "new . target"
  , "using x = f ()"
  , "await using y = g ()"
  , "using x = a , y = b ;"
  , "await f ()"
  , "l : function f () {}"
  , "l : var x = 1 ;"
  , "/*a*/new/*b*/./*c*/target"
  , "/*a*/using/*b*/x/*c*/=/*d*/1"
  , "/*a*/await/*b*/using/*c*/y/*d*/=/*e*/2"
  ]

/-- Module level sources the annotated tree has to reproduce exactly: an
`import`/`export` declaration is only a module item, so these are read with
the module parser. -/
def annotatedModuleCases : List String :=
  [ "export * as ns from 'm' ;"
  , "export * from 'm' ;"
  , "export default 1 + 2 ;"
  , "export default function f () {}"
  , "import x from 'm' with { type : 'json' } ;"
  , "import 'm' with { type : 'json' } ;"
  , "export { a } from 'm' with { type : 'json' , 'x' : 'y' } ;"
  , "/*a*/export/*b*/*/*c*/as/*d*/ns/*e*/from/*f*/'m'/*g*/;"
  , "/*a*/export/*b*/default/*c*/1/*d*/;"
  , "/*a*/import/*b*/x/*c*/from/*d*/'m'/*e*/with/*f*/{/*g*/type/*h*/:/*i*/'json'/*j*/}/*k*/;"
  ]

/-! ## The deterministic tree -/

open Language.JavaScript.MiniAST in
/-- Parse and print in the canonical style. -/
def miniPrint (src : String) : String :=
  match parse src with
  | .ok p => printProgram p
  | .error e => "ERROR: " ++ e

open Language.JavaScript.MiniAST in
/-- Does the printed program read back as the same tree? -/
def miniStable (src : String) : String :=
  match parse src with
  | .ok p => toString (match parse (printProgram p) with | .ok q => q == p | .error _ => false)
  | .error e => "ERROR: " ++ e

open Language.JavaScript.MiniAST in
/-- Does the trip through the annotated tree preserve the tree? -/
def miniViaAST (src : String) : String :=
  match parse src with
  | .ok p => toString (match ofAST (toAST p) with | .ok q => q == p | .error _ => false)
  | .error e => "ERROR: " ++ e

open Language.JavaScript.MiniAST in
/-- Does the *source* produced from the annotated tree still mean the same? -/
def miniViaASTSource (src : String) : String :=
  match parse src with
  | .ok p => toString (match parse (renderViaAST p) with | .ok q => q == p | .error _ => false)
  | .error e => "ERROR: " ++ e

/-- Sources whose deterministic tree is checked by printing it. -/
def miniPrintCases : List (String × String × String) :=
  [ ("a?.b;", miniPrint "a?.b;", "a?.b;\n")
  , ("a?.[b];", miniPrint "a?.[b];", "a?.[b];\n")
  , ("a?.(b);", miniPrint "a?.(b);", "a?.(b);\n")
    -- a chain is one node, so the parentheses of `(a?.b).c`, which change
    -- what is evaluated, are not dropped
  , ("(a?.b).c;", miniPrint "(a?.b).c;", "(a?.b).c;\n")
  , ("a?.b.c;", miniPrint "a?.b.c;", "a?.b.c;\n")
  , ("a ?? b;", miniPrint "a??b;", "a ?? b;\n")
    -- `??` may not be written next to `&&` or `||` without parentheses
  , ("(a ?? b) || c;", miniPrint "(a??b)||c;", "(a ?? b) || c;\n")
  , ("a ?? (b && c);", miniPrint "a??(b&&c);", "a ?? (b && c);\n")
  , ("a ??= b;", miniPrint "a??=b;", "a ??= b;\n")
  , ("class with private, static and a static block",
      miniPrint "class A { #x = 1; static y = 2; static { z(); } m() { return this.#x; } }",
      "class A {\n  #x = 1;\n  static y = 2;\n  static {\n    z();\n  }\n  m() {\n    return this.#x;\n  }\n}\n")
  , ("#x in a;", miniPrint "#x in a;", "#x in a;\n")
  , ("@dec class A {}", miniPrint "@dec class A {}", "@dec class A {}\n")
  , ("class A { @dec m() {} }", miniPrint "class A { @dec m() {} }",
      "class A {\n  @dec m() {}\n}\n")
  , ("class A { @d1 @d2 static #p = 3; }", miniPrint "class A { @d1 @d2 static #p = 3; }",
      "class A {\n  @d1 @d2 static #p = 3;\n}\n")
  , ("import.meta.url;", miniPrint "import.meta.url;", "import.meta.url;\n")
  , ("import('x');", miniPrint "import('x');", "import(\"x\");\n")
  , ("import with options", miniPrint "import('x', {with: {type: 'json'}});",
      "import(\"x\", { with: { type: \"json\" } });\n")
  , ("x = {...a};", miniPrint "x={...a};", "x = { ...a };\n")
  , ("var {a = 1} = x;", miniPrint "var {a = 1} = x;", "var { a = 1 } = x;\n")
  , ("var {a, ...r} = x;", miniPrint "var {a, ...r} = x;", "var { a, ...r } = x;\n")
  , ("var [a, , b, ...c] = x;", miniPrint "var [a,,b,...c]=x;", "var [a, , b, ...c] = x;\n")
  , ("parameters with a default and a pattern",
      miniPrint "function f(a = 1, {b, c: d = 2}, ...rest) {}",
      "function f(a = 1, { b, c: d = 2 }, ...rest) {}\n")
  , ("for (const {a} of xs) {}", miniPrint "for (const {a} of xs) {}",
      "for (const { a } of xs) {}\n")
  , ("catch ({message})", miniPrint "try { } catch ({message}) { }",
      "try {} catch ({ message }) {}\n")
  , ("[a, b] = xs;", miniPrint "[a,b]=xs;", "[a, b] = xs;\n")
    -- an object pattern at the start of a statement needs its parentheses
  , ("({a} = o);", miniPrint "({a}=o);", "({ a } = o);\n")
  , ("(a = 1) => a;", miniPrint "(a=1)=>a;", "(a = 1) => a;\n")
    -- `super` is a node of its own, in each of the three forms it may be
    -- written in
  , ("super in a class",
      miniPrint "class A extends B { constructor(x) { super(x); } m() { return super.y; } }",
      ("class A extends B {\n  constructor(x) {\n    super(x);\n  }\n  m() {\n"
        ++ "    return super.y;\n  }\n}\n"))
  , ("super[i]", miniPrint "class A extends B { m(i) { return super[i]; } }",
      "class A extends B {\n  m(i) {\n    return super[i];\n  }\n}\n")
  , ("super.x = 1", miniPrint "class A extends B { m() { super.x = 1; } }",
      "class A extends B {\n  m() {\n    super.x = 1;\n  }\n}\n")
  , ("new.target", miniPrint "function F() { return new.target; }",
      "function F() {\n  return new.target;\n}\n")
  , ("using", miniPrint "using x = f();", "using x = f();\n")
  , ("await using", miniPrint "await using y = g();", "await using y = g();\n")
  , ("await at the top level of a module", miniPrint "await f();", "await f();\n")
  , ("a labelled function declaration", miniPrint "l: function f() {}",
      "l: function f() {}\n")
  , ("a labelled declaration", miniPrint "l: let x = 1;", "l: let x = 1;\n")
  , ("export * as ns", miniPrint "export * as ns from 'm';", "export * as ns from \"m\";\n")
  , ("export *", miniPrint "export * from 'm';", "export * from \"m\";\n")
  , ("export default", miniPrint "export default 1 + 2;", "export default 1 + 2;\n")
  , ("import attributes", miniPrint "import x from 'm' with { type: 'json' };",
      "import x from \"m\" with { \"type\": \"json\" };\n")
  , ("import attributes on a bare import", miniPrint "import 'm' with { type: 'json' };",
      "import \"m\" with { \"type\": \"json\" };\n")
  , ("import attributes on an export", miniPrint "export { a } from 'm' with { type: 'json' };",
      "export { a } from \"m\" with { \"type\": \"json\" };\n")
  ]

/-- Sources read into the deterministic tree, printed, and read back. -/
def miniRoundTripSources : List String :=
  [ "a?.b; a?.[b]; a?.(b); (a?.b).c; a?.b.c;"
  , "x = a ?? b; y = (a ?? b) || c; z = a ?? (b && c);"
  , "a ??= b; a ||= b; a &&= b;"
  , "class A { #x = 1; static y = 2; static { z(); } m() { return this.#x; } }"
  , "class A { #x = 1; has(o) { return #x in o; } }"
  , "@dec class A {}"
  , "class A { @d1 @d2 static #p = 3; @dec m() {} }"
  , "const K = class extends B { f = 1; static { g(); } };"
  , "import.meta.url; import('x'); import('y', { with: { type: 'json' } });"
  , "x = { ...a, b: 1 };"
  , "var { a = 1, b: { c } = {}, ...r } = x;"
  , "var [a, , b, ...c] = x;"
  , "function f(a = 1, { b, c: d = 2 }, [e], ...rest) {}"
  , "const g = (a = 1, { b } = {}) => a;"
  , "for (const { a } of xs) {} for ([k, v] of pairs) {}"
  , "try { } catch ({ message }) { }"
  , "[a, b] = xs; ({ a } = o); ({ a: o.p } = o);"
  , "class A extends B { constructor(x) { super(x); } m(i) { return super.y + super[i]; } }"
  , "class A extends B { m() { super.x = 1; } }"
  , "function F() { return new.target; }"
  , "using x = f(); await using y = g(); await h();"
  , "l: function f() {} l: let x = 1; m: { g(); }"
  , "export * as ns from 'm'; export * from 'n';"
  , "export default 1 + 2;"
  , "import x from 'm' with { type: 'json' }; import 'n' with { type: 'json' };"
  , "export { a } from 'm' with { type: 'json' };"
  ]

/-! ## The scope safe tree -/

open Language.JavaScript.BrujinAST in
/-- Read source into a scope safe tree and print it back. -/
def brujinRender (src : String) : String :=
  match parse src with
  | .ok p => printProgram p
  | .error e => "ERROR: " ++ e

open Language.JavaScript.BrujinAST in
/-- Does the printed program read back as the same scope safe tree? -/
def brujinStable (src : String) : String :=
  match parse src with
  | .ok p => toString (match parse (printProgram p) with | .ok q => q == p | .error _ => false)
  | .error e => "ERROR: " ++ e

/-- What the scope safe tree makes of the new syntax. -/
def brujinCases : List (String × String × String) :=
  [ ("an optional chain on a const variable",
      brujinRender "const o = {}; o?.a?.b;", "const _c0 = {};\n_c0?.a?.b;\n")
  , ("an optional call", brujinRender "const f = (x) => x; f?.(1);",
      "const _c0 = (_m0) => _m0;\n_c0?.(1);\n")
  , ("an optional index", brujinRender "const xs = []; xs?.[0];",
      "const _c0 = [];\n_c0?.[0];\n")
  , ("??", brujinRender "const a = null; const b = a ?? 1;",
      "const _c0 = null;\nconst _c1 = _c0 ?? 1;\n")
  , ("??=", brujinRender "let c = null; c ??= 2;", "let _m0 = null;\n_m0 ??= 2;\n")
    -- a private name is resolved against the class, not against a scope,
    -- so it stays a name where every variable has become an index
  , ("private members, a static field and a static block",
      brujinRender "class A { #x = 1; static y = 2; static { z(); } m() { return this.#x; } }",
      ("class _c0 {\n  #x = 1;\n  static y = 2;\n  static {\n    z();\n  }\n  m() {\n"
        ++ "    return this.#x;\n  }\n}\n"))
  , ("#x in o", brujinRender "class A { #x = 1; has(o) { return #x in o; } }",
      "class _c0 {\n  #x = 1;\n  has(_m0) {\n    return #x in _m0;\n  }\n}\n")
  , ("a decorated class", brujinRender "@dec class A {}", "@dec class _c0 {}\n")
  , ("a decorated member", brujinRender "class A { @dec m() {} }",
      "class _c0 {\n  @dec m() {}\n}\n")
  , ("several decorators on a private static field",
      brujinRender "class A { @d1 @d2 static #p = 3; }",
      "class _c0 {\n  @d1 @d2 static #p = 3;\n}\n")
  , ("a field of a class expression", brujinRender "const g = class extends B { f = 1; };",
      "const _c0 = class extends B {\n  f = 1;\n};\n")
  , ("import.meta", brujinRender "import.meta.url;", "import.meta.url;\n")
  , ("a dynamic import", brujinRender "import('x');", "import(\"x\");\n")
  , ("a dynamic import with options", brujinRender "import('x', { with: { type: 'json' } });",
      "import(\"x\", { with: { type: \"json\" } });\n")
    -- the two forms the scope safe tree still refuses, and what it says
  , ("a default parameter value is refused", brujinRender "function f(a = 1) {}",
      "ERROR: BrujinAST: a default value in a parameter")
  , ("a destructuring declarator is refused", brujinRender "var { a = 1 } = x;",
      "ERROR: BrujinAST: a destructuring pattern in a binder")
  , ("a destructuring assignment is refused", brujinRender "[a, b] = xs;",
      "ERROR: BrujinAST: a destructuring pattern in an assignment")
  , ("a spread property", brujinRender "const a = {}; x = { ...a, b: 1 };",
      "const _c0 = {};\nx = { ..._c0, b: 1 };\n")
    -- `super` is a node of the scope safe tree, so the home object of a
    -- method is no longer read as an unknown global
  , ("super in a constructor and in a method",
      brujinRender "class A extends B { constructor(x) { super(x); } m() { return super.y; } }",
      ("class _c0 extends B {\n  constructor(_m0) {\n    super(_m0);\n  }\n  m() {\n"
        ++ "    return super.y;\n  }\n}\n"))
  , ("super[i] and an assignment to super.x",
      brujinRender "class A extends B { m(i) { super.x = super[i]; } }",
      "class _c0 extends B {\n  m(_m0) {\n    super.x = super[_m0];\n  }\n}\n")
  , ("new.target", brujinRender "function F() { return new.target; }",
      "function _c0() {\n  return new.target;\n}\n")
    -- a `using` binding cannot be assigned to, so it is a const binding
  , ("using", brujinRender "const r = f(); using x = r; g(x);",
      "const _c0 = f();\nusing _c1 = _c0;\ng(_c1);\n")
  , ("await using", brujinRender "await using y = g(); h(y);",
      "await using _c0 = g();\nh(_c0);\n")
  , ("await at the top level of a module", brujinRender "await f();", "await f();\n")
    -- a label may carry a declaration, and what it declares is in scope
    -- after it
  , ("a labelled function declaration",
      brujinRender "l: function f() { return 1; } f();",
      "l: function _c0() {\n  return 1;\n}\n_c0();\n")
  , ("a labelled declaration", brujinRender "l: let x = 1; g(x);",
      "l: let _m0 = 1;\ng(_m0);\n")
  , ("export * as ns", brujinRender "export * as ns from 'm';",
      "export * as ns from \"m\";\n")
  , ("export *", brujinRender "export * from 'm';", "export * from \"m\";\n")
  , ("export default of a const variable", brujinRender "const v = 1; export default v;",
      "const _c0 = 1;\nexport default _c0;\n")
  , ("import attributes", brujinRender "import x from 'm' with { type: 'json' }; x();",
      "import _c0 from \"m\" with { \"type\": \"json\" };\n_c0();\n")
  , ("import attributes on a bare import", brujinRender "import 'm' with { type: 'json' };",
      "import \"m\" with { \"type\": \"json\" };\n")
  , ("import attributes on an export",
      brujinRender "export { a } from 'm' with { type: 'json' };",
      "export { a } from \"m\" with { \"type\": \"json\" };\n")
  ]

/-- Sources whose scope safe tree has to survive printing and reading back. -/
def brujinStableSources : List String :=
  [ "const o = {}; o?.a?.b; o?.[0]; o?.();"
  , "const a = null; const b = a ?? 1; let c = 2; c ??= 3;"
  , "class A { #x = 1; static y = 2; static { z(); } m() { return this.#x; } }"
  , "@dec class A { @d1 @d2 static #p = 3; }"
  , "import.meta.url; import('x'); import('y', { with: { type: 'json' } });"
  , "const a = {}; const b = { ...a, c: 1 };"
  , "class A extends B { constructor(x) { super(x); } m(i) { return super.y + super[i]; } }"
  , "function F() { return new.target; }"
  , "const r = f(); using x = r; await using y = g(); h(x, y);"
  , "l: function f() { return 1; } l: let x = 1; g(f, x);"
  , "export * as ns from 'm'; export * from 'n'; const v = 1; export default v;"
  , "import x from 'm' with { type: 'json' }; import 'n' with { type: 'json' }; x();"
  ]

def spec : Spec := do
  describe "Modern Syntax Annotated" do
    for src in annotatedCases do
      it src do
        shouldEqual (renderToString (readJs src)) src
    for src in annotatedModuleCases do
      it src do
        shouldEqual (renderToString (readJsModule src)) src

  describe "Modern Syntax Print" do
    for (label, actual, expected) in miniPrintCases do
      it label do
        shouldEqual actual expected

  describe "Modern Syntax Round Trip" do
    for src in miniRoundTripSources do
      it ("print: " ++ src) do
        shouldEqual (miniStable src) "true"
      it ("toAST: " ++ src) do
        shouldEqual (miniViaAST src) "true"
      it ("render: " ++ src) do
        shouldEqual (miniViaASTSource src) "true"

  describe "Modern Syntax Scope Safe" do
    for (label, actual, expected) in brujinCases do
      it label do
        shouldEqual actual expected
    for src in brujinStableSources do
      it ("stable: " ++ src) do
        shouldEqual (brujinStable src) "true"

end LanguageJavascriptTests.Modern
