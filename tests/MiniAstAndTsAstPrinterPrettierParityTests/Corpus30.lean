import Tests.Corpus29

/-!
# Samples of curried calls

A call whose callee is a call that takes more arguments than it does is a
link of what prettier calls a long curried call chain, `f(a, b)(c)`: its
argument list is left ungrouped, so that it breaks together with the line
that holds the call.  The samples here cover that layout, and the places
it is decided in: an ordinary call, a call of a member chain, an optional
chain, and a `new`, which is not a call for this purpose.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A long array literal, which has to be broken. -/
def longArrayOfNumbers : MiniExpr :=
  .array ((List.range 25).map (fun i => .elem (num (i * 37))))

/-- The samples. -/
def samples30 : List Sample :=
  [ -- the callee takes more arguments than the call: the argument list of
    -- the callee breaks with the line the call stands on
    { name := "curried-two-then-one"
      prog := ⟨[es (.call (call "f" [v "aaa", v "bbb"]) [longArrayOfNumbers])]⟩ }
  , { name := "curried-three-then-one"
      prog := ⟨[es (.call (call "f" [v "aaa", v "bbb", v "ccc"]) [longArrayOfNumbers])]⟩ }
  , -- as many arguments, or none at all: an ordinary call
    { name := "curried-one-then-one"
      prog := ⟨[es (.call (call "f" [v "aaa"]) [longArrayOfNumbers])]⟩ }
  , { name := "curried-none-then-one"
      prog := ⟨[es (.call (call "f" []) [longArrayOfNumbers])]⟩ }
  , { name := "curried-two-then-none"
      prog := ⟨[es (.call (call "f" [v "aaa", v "bbb"]) [])]⟩ }
  , -- the call in the middle keeps the callee of the chain on its line
    { name := "curried-three-links"
      prog := ⟨[es (.call (.call (call "f" [v "aaa", v "bbb"]) [v "g"])
                  [longArrayOfNumbers])]⟩ }
  , -- the callee is a member chain
    { name := "curried-member-chain"
      prog := ⟨[es (.call (.call (.dot (v "z") (nes "f")) [v "aaa", v "bbb"])
                  [longArrayOfNumbers])]⟩ }
  , { name := "curried-long-member-chain"
      prog := ⟨[es (.call (.call (.dot (.call (.dot (v "theCollection") (nes "filter"))
                    [v "aaa", v "bbb"]) (nes "map")) [v "ccc", v "ddd"])
                  [longArrayOfNumbers])]⟩ }
  , -- an optional call of a call
    { name := "curried-optional-call"
      prog := ⟨[es (.chain (call "f" [v "aaa", v "bbb"])
                  ⟨.call true [longArrayOfNumbers], []⟩)]⟩ }
  , -- a `new` is not a call: its callee keeps its arguments on one line
    { name := "curried-new"
      prog := ⟨[es (.new (call "f" [v "aaa", v "bbb"]) [longArrayOfNumbers])]⟩ }
  , -- the arguments of the call itself break rather than those of the
    -- callee when they do not fit
    { name := "curried-plain-arguments"
      prog := ⟨[es (.call (call "f" [v "aaa", v "bbb"])
                  [v "veryLongArgumentNumberOne", v "veryLongArgumentNumberTwo",
                   v "veryLongArgNo3"])]⟩ }
  , -- the same calls written inside a block, where less of the line is
    -- left for them
    { name := "curried-nested-in-blocks"
      prog := ⟨[st (.block [.block [.expr
                  (.call (call "theFunctionName" [v "aaa", v "bbb"])
                    [longArrayOfNumbers])]])]⟩ }
  , -- a chain of several calls, of which one is a curried link: the
    -- argument list of that one breaks, the others stay on their line
    { name := "curried-several-links"
      prog := ⟨[es (.dot (.call (.call (.call (.call (call "computeTheValue" [num 76]) [])
                    [v "theValue", num 1, v "theHandler"]) [v "theVeryLongNameForAVariableHere"])
                  [v "abc"]) (nes "f"))]⟩ }
  , -- a curried call read through by the member accesses of a chain: the
    -- calls belong to the chain that follows them
    { name := "curried-then-member-chain"
      prog := ⟨[es (.call (.dot (.call (.call (call "computeTheValue" [num 1, v "index"])
                    [v "target"]) [.string "a rather long string literal here", num 46,
                      v "currentValue"]) (nes "theVeryLongNameForAVariableHere"))
                  [v "theCollection", v "abc"])]⟩ }
  , -- a curried call followed by member accesses only, which prettier
    -- prints on its own rather than as part of a chain
    { name := "curried-then-members"
      prog := ⟨[es (.dot (.dot (.call (.call (.dot (v "theCollection") (nes "filter"))
                    [v (longName 0), v (longName 1)]) [v "theVeryLongNameForAVariableHere"])
                  (nes "value")) (nes "name"))]⟩ }
  , -- a curried call followed by the links of an optional chain
    { name := "curried-then-optional-members"
      prog := ⟨[es (.chain (.call (.call (.dot (v "theCollection") (nes "filter"))
                    [v (longName 0), v (longName 1)]) [v "theVeryLongNameForAVariableHere"])
                  ⟨.dot true (nes "value"), [.dot false (nes "name")]⟩)]⟩ }
  , -- a curried call whose own argument is a function, which is hugged
    { name := "curried-function-argument"
      prog := ⟨[es (.call (call "theFactory" [v (longName 0), v (longName 1)])
                  [.arrow false [par "x"] (.block [.return_ (some (v "x"))])])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
