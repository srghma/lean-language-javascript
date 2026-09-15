import Tests.Corpus24

/-!
# Samples of the parentheses of an `await` expression

An `await` written as the object of a member access, or as the callee of a
call, is parenthesised, and prettier lets those parentheses break: the
operand then stands on a line of its own inside them.  The decision is the
`await`'s own, unless it opens the operand of another `await`, where the
line that holds them both decides instead.  The callee of a `new` and the
tag of a template literal take parentheses which never break that way.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A call which does not fit on the line it starts on. -/
def awaitedLongCall : MiniExpr :=
  call "aVeryVeryLongIdentifierNameHere"
    [v "theIteratorOfTheList", v "theConfigurationObject"]

/-- A call short enough for any line. -/
def awaitedShortCall : MiniExpr := call "f" []

/-- The statements, inside an asynchronous function. -/
def asyncProgram (body : List MiniStatement) : MiniProgram :=
  ⟨[st (.funcDecl true false (nes "helper") [] body)]⟩

/-- The samples. -/
def samples25 : List Sample :=
  [ -- an `await` whose operand is too long for the line
    { name := "await-parens-member"
      prog := asyncProgram
        [.expr (.dot (.await awaitedLongCall) (nes "theHandlerName"))] }
  , { name := "await-parens-call"
      prog := asyncProgram [.expr (.call (.await awaitedLongCall) [v "item"])] }
  , { name := "await-parens-index"
      prog := asyncProgram [.expr (.index (.await awaitedLongCall) (.string "key"))] }
  , -- an `await` of another one, at the left edge of its operand
    { name := "await-await-member"
      prog := asyncProgram
        [.expr (.await (.dot (.await awaitedLongCall) (nes "theHandlerName")))] }
  , { name := "await-await-call"
      prog := asyncProgram
        [.expr (.await (.call (.await awaitedLongCall) [v "item"]))] }
  , { name := "await-await-deep"
      prog := asyncProgram
        [.expr (.await (.dot (.dot (.await awaitedLongCall) (nes "theHandlerName"))
          (nes "theRatherLongPropertyName")))] }
  , -- an `await` which is not at the left edge of the operand it stands in
    { name := "await-await-right"
      prog := asyncProgram
        [.expr (.await (.binary (v "item") .plus
          (.dot (.await awaitedLongCall) (nes "name"))))] }
  , -- a block between the two, which ends the left edge
    { name := "await-block-between"
      prog := asyncProgram
        [.expr (.await (.call (.func true false none []
          [.expr (.dot (.await awaitedLongCall) (nes "theHandlerName"))]) []))] }
  , -- the places whose parentheses do not break
    { name := "await-new-and-tag"
      prog := asyncProgram
        [.expr (.new (.await awaitedLongCall) [v "item"]),
         .expr (.template (some (.await awaitedLongCall)) "text" [])] }
  , -- the object of an optional chain, whose parentheses do break
    { name := "await-optional-chain"
      prog := asyncProgram
        [.expr (.chain (.await awaitedLongCall) ⟨.dot true (nes "theHandlerName"), []⟩)] }
  , -- a short `await` whose parentheses break only because the line that
    -- holds the `await` it belongs to does
    { name := "await-edge-member"
      prog := asyncProgram
        [.expr (.await (.dot (.dot (.dot (.await awaitedShortCall)
          (nes "aVeryVeryLongIdentifierNameHere")) (nes "theIteratorOfTheList"))
          (nes "theHandlerNameIsHere")))] }
  , { name := "await-edge-plain"
      prog := asyncProgram
        [.expr (.dot (.dot (.dot (.await awaitedShortCall)
          (nes "aVeryVeryLongIdentifierNameHere")) (nes "theIteratorOfTheList"))
          (nes "theHandlerNameIsHere"))] }
  , { name := "await-edge-call"
      prog := asyncProgram
        [.expr (.await (.call (.await awaitedShortCall)
          [v "aVeryVeryLongIdentifierNameHere", v "theIteratorOfTheList"]))] }
  , { name := "await-edge-return"
      prog := asyncProgram
        [.return_ (some (.await (.dot (.dot (.await awaitedShortCall)
          (nes "aVeryVeryLongIdentifierNameHere")) (nes "theIteratorOfTheList"))))] }
  , { name := "await-edge-declaration"
      prog := asyncProgram
        [.decl .const ⟨⟨p "theValueOfTheThing",
          some (.await (.dot (.dot (.await awaitedShortCall)
            (nes "aVeryVeryLongIdentifierNameHere")) (nes "theIteratorOfTheList")))⟩, []⟩] }
  ]

end Language.JavaScript.MiniAST.Corpus
