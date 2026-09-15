import Tests.Corpus26

/-!
# Samples of the calls prettier keeps on one line

Prettier writes the arguments of a few calls on the line of the call,
however long they are: a `require` of a module, the `define` of a CommonJS
or AMD module, and a call of a test framework, whose function argument
keeps its whole parameter list on that line as well.  A declaration whose
value is a `require` keeps the line of its `=` too.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A module path which does not fit on the line of a declaration. -/
def longModulePath : MiniExpr := .string "a/rather/long/module/path/that/goes/on/here.js"

/-- A body of one statement. -/
def oneCallStatement : List MiniStatement := [.expr (call "computeTheValue" [v "item"])]

/-- The samples. -/
def samples27 : List Sample :=
  [ { name := "require-declaration"
      prog := ⟨[st (constDecl "theModuleBindingName" (call "require" [longModulePath])),
                st (constDecl "theOtherModuleName"
                  (.dot (call "require" [longModulePath]) (nes "theExportName")))]⟩ }
  , { name := "require-chain"
      prog := ⟨[st (constDecl "theBindingName"
                  (.call (.dot (call "require" [longModulePath]) (nes "theFactoryName"))
                    [v "theConfigurationObject"]))]⟩ }
  , { name := "require-resolve"
      prog := ⟨[st (constDecl "theResolvedPathName"
                  (.call (.dot (v "require") (nes "resolve")) [longModulePath])),
                st (constDecl "theResolvedPathsName"
                  (.call (.dot (.dot (v "require") (nes "resolve")) (nes "paths"))
                    [longModulePath])),
                st (constDecl "theResolvedModuleUrl"
                  (.call (.dot .importMeta (nes "resolve")) [longModulePath]))]⟩ }
  , { name := "require-resolve-in-chain"
      prog := ⟨[es (.chain (.call (.dot (v "require") (nes "resolve")) [longModulePath])
                  ⟨.index true (num 23),
                   [.dot false (nes "aVeryVeryLongIdentifierNameHere"), .call true []]⟩)]⟩ }
  , { name := "require-many-arguments"
      prog := ⟨[es (call "require" [.array [.elem longModulePath],
                  .arrow false [par "theModuleName"] (.block oneCallStatement)])]⟩ }
  , { name := "define-amd"
      prog := ⟨[es (call "define" [.array [.elem longModulePath,
                    .elem (.string "another/module")],
                  .arrow false [par "theFirstModule", par "theSecondModule"]
                    (.block oneCallStatement)]),
                es (call "define" [.string "the/name/of/this/module",
                  .array [.elem longModulePath],
                  .arrow false [par "theFirstModule"] (.block oneCallStatement)]),
                es (call "define" [.arrow false [] (.block oneCallStatement)])]⟩ }
  , -- a `define` which is not a statement of its own is laid out as any
    -- other call is
    { name := "define-not-a-statement"
      prog := ⟨[st (constDecl "theResultOfDefine"
                  (call "define" [.array [.elem longModulePath],
                    .arrow false [par "theFirstModuleName"] (.block oneCallStatement)]))]⟩ }
  , { name := "test-call-two-arguments"
      prog := ⟨[es (call "describe" [.string "a test name which is quite long indeed here",
                  .func false false none [] oneCallStatement]),
                es (call "it" [.string "does the thing that it says that it does here",
                  .arrow false [] (.block oneCallStatement)]),
                es (.call (.dot (v "it") (nes "only"))
                  [.string "does only the thing that it says it does",
                   .arrow false [par "done"] (.block oneCallStatement)])]⟩ }
  , { name := "test-call-three-arguments"
      prog := ⟨[es (call "test" [.string "the name of the test which is rather long",
                  .arrow false [par "done"] (.block oneCallStatement), num 2500]),
                es (call "test" [.string "the name of the test which is rather long",
                  .arrow false [par "a", par "bb"] (.block oneCallStatement), num 2500])]⟩ }
  , { name := "test-call-hooks"
      prog := ⟨[es (call "beforeEach" [call "inject" [.arrow false [par "theInjectedService"]
                  (.block oneCallStatement)]]),
                es (call "afterAll" [.arrow false [] (.block oneCallStatement)])]⟩ }
  , { name := "test-call-template-name"
      prog := ⟨[es (call "it" [.template none "a test name which is quite long indeed" [],
                  .arrow false [] (.block oneCallStatement)])]⟩ }
  , { name := "test-call-look-alikes"
      prog := ⟨[es (call "describeTheThing" [.string "a test name which is quite long here",
                  .arrow false [] (.block oneCallStatement)]),
                es (call "describe" [v "theNameOfTheTestHere",
                  .arrow false [] (.block oneCallStatement)])]⟩ }
  , { name := "test-call-in-a-declaration"
      prog := ⟨[st (.decl .const ⟨⟨.object [⟨.ident (nes "currentValue"), p "currentValue"⟩] none,
                  some (call "test" [.string "the name of the test number 14004",
                    .arrow false [par "done"] (.block oneCallStatement), num 2500])⟩, []⟩)]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
