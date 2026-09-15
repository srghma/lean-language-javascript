import Tests.Ts.Prelude

/-!
# TypeScript samples for decorated parameters and for `!` of a conditional

The samples here cover the decorators a parameter of a method of a class
may be written with — one and several, on a plain parameter, on a
parameter property, on a rest parameter, on the parameter of a setter, on
a pattern and on a parameter with a default value, at the widths where
the decorators keep the line of the parameter and where they stand on
lines of their own — and the non-null assertion of a conditional
expression, which stands between parentheses of its own lines wherever
prettier indents what those parentheses hold.

They also cover the decorator written as a member access, `@A.b`, which
prettier keeps on one line however long it is, and the long chain of
accesses which it does break, and the constraint of an `infer`, which is
laid out the way the constraint of a type parameter is: it keeps the line
of its `extends` where it fits there, and stands indented below it where
it does not.

The last of them cover the hugged first argument of a call whose second
argument holds a `!`, which prettier reads through when it asks whether
that argument is a short one, and whose type arguments break, and the
field whose decorators make its left hand side one that breaks, so that
its value no longer keeps the line of the `=`.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A class holding the one method `m`. -/
def classWith (elems : List MiniClassElement) : MiniStatement :=
  .classDecl [] false (nes "A") [] none [] elems

/-- A method of a class, with the given parameters. -/
def methodWith (name : String) (params : List MiniParam) : MiniClassElement :=
  .method [] {} .normal (.ident (nes name)) false [] params none (some [])

/-- The samples of this file. -/
def samples4 : List Sample :=
  [ { name := "param-decorator-one"
      prog := ⟨[st (classWith [methodWith "m" [parDec [call "Body" []] "b" (some (ty "T"))]])]⟩ }
  , { name := "param-decorator-two-params"
      prog := ⟨[st (classWith [methodWith "m"
        [parDec [v "a"] "b" none, parDec [v "c"] "d" none]])]⟩ }
  , { name := "param-decorator-many"
      prog := ⟨[st (classWith [methodWith "m"
        [parDec [call "a" [], call "b" [], call "c" [], call "d" [],
          call "averyLongDecoratorNameHereOk" []] "parameterNameIsLong" (some (ty "T"))]])]⟩ }
  , { name := "param-decorator-breaks"
      prog := ⟨[st (classWith [methodWith "m"
        [parDec [call "alphaDecoratorName" [], call "betaDecoratorNameHere" [],
          call "gammaDecoratorNameHere" []] "parameterName" (some (ty "T"))]])]⟩ }
  , { name := "param-decorator-breaks-after"
      prog := ⟨[st (classWith [methodWith "m"
        [parT "q" (ty "number"),
         parDec [call "alphaDecoratorName" [], call "betaDecoratorNameHere" [],
          call "gammaDecoratorName" []] "parameterName" (some (ty "T"))]])]⟩ }
  , { name := "param-decorator-long-object"
      prog := ⟨[st (classWith [methodWith "m"
        [parDec [.call (v "decoratorNumberOneWithLongName") []
            [.object [.keyValue (.ident (nes "alpha")) (num 1),
                      .keyValue (.ident (nes "beta")) (num 2),
                      .keyValue (.ident (nes "gamma")) (num 3),
                      .keyValue (.ident (nes "delta")) (num 44444)]]]
          "x" (some (ty "number"))]])]⟩ }
  , { name := "param-decorator-long-param"
      prog := ⟨[st (classWith [methodWith "m"
        [parDec [call "a" []] "someVeryLongParameterNameHereIndeedYes"
          (some (ty "SomeExtremelyLongTypeNameThatGoesOnAndOn"))]])]⟩ }
  , { name := "param-decorator-property"
      prog := ⟨[st (classWith
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain [call "Inject" [v "SOME_TOKEN_NAME_THAT_IS_LONG"]]
            { accessibility := some .private_, isReadonly := true } (p "serviceName") false
            (some (ty "Service"))] none (some [])])]⟩ }
  , { name := "param-decorator-rest"
      prog := ⟨[st (classWith [methodWith "m"
        [.rest [v "a"] (p "xs") (some (.array (ty "number")))]])]⟩ }
  , { name := "param-decorator-setter"
      prog := ⟨[st (classWith
        [.method [] {} .set (.ident (nes "x")) false []
          [parDec [v "a"] "value" (some (ty "number"))] none (some [])])]⟩ }
  , { name := "param-decorator-object-pattern"
      prog := ⟨[st (classWith [methodWith "m"
        [.plain [v "a"] {} (.object [⟨.ident (nes "b"), p "b"⟩] none) false
          (some (ty "T"))]])]⟩ }
  , { name := "param-decorator-default"
      prog := ⟨[st (classWith [methodWith "m"
        [.plain [call "a" []] {} (.withDefault (p "b") (num 1)) false (some (ty "number"))]])]⟩ }
  , { name := "nonnull-of-ternary-decl"
      prog := ⟨[st (constDecl "q" (some (ty "SomeType"))
        (.nonNull (.ternary (v "aLongConditionExpression") (v "someValueNumberOneHere")
          (v "otherValueTwoHere"))))]⟩ }
  , { name := "nonnull-of-ternary-assign-fits"
      prog := ⟨[es (.assign (v "x") .assign
        (.nonNull (.ternary (v "aLongConditionExpression") (v "someValueNumberOneHere")
          (v "otherValueTwoHere"))))]⟩ }
  , { name := "nonnull-of-ternary-statement"
      prog := ⟨[es (.nonNull (.ternary (v "aLongConditionExpressionHere")
        (v "someValueNumberOneHereIsLong") (v "otherValueTwoHereLong")))]⟩ }
  , { name := "nonnull-of-ternary-arg"
      prog := ⟨[es (.call (v "someFunctionCallHere") [] [v "alpha",
        .nonNull (.ternary (v "aLongConditionExpressionHere")
          (v "someValueNumberOneHereIsLong") (v "otherValueTwoHereLong"))])]⟩ }
  , { name := "nonnull-of-ternary-binary"
      prog := ⟨[st (constDecl "q" none
        (.binary (.nonNull (.ternary (v "aLongConditionExpressionHere")
          (v "someValueNumberOneHereIsLong") (v "otherValueTwoHereLong"))) .plus (num 1)))]⟩ }
  , { name := "nonnull-of-ternary-member"
      prog := ⟨[st (constDecl "q" none
        (.dot (.dot (.nonNull (.ternary (v "aLongConditionExpression")
          (v "someValueNumberOneHere") (v "otherValueTwoHere"))) (nes "someProperty"))
          (nes "anotherOne")))]⟩ }
  , { name := "nonnull-of-ternary-return"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [] none (some
        [.return_ (some (.nonNull (.ternary (v "aLongConditionExpression")
          (v "someValueNumberOneHere") (v "otherValueTwoHere"))))]))]⟩ }
  , { name := "nonnull-of-ternary-unary"
      prog := ⟨[st (constDecl "q" none
        (.unary .not (.nonNull (.ternary (v "aLongConditionExpression")
          (v "someValueNumberOneHere") (v "otherValueTwoHere")))))]⟩ }
  , { name := "nonnull-of-ternary-property"
      prog := ⟨[st (constDecl "o" none (.object [.keyValue (.ident (nes "key"))
        (.nonNull (.ternary (v "aLongConditionExpressionHere")
          (v "someValueNumberOneHereIsLong") (v "otherValueTwoHereLong")))]))]⟩ }
  , { name := "member-decorator-on-field"
      prog := ⟨[st (.classDecl [] false (nes "B") [] none []
        [.field [.dot (v "AVeryVeryLongTypeNameWrittenHereOk")
            (nes "theVeryLongNameForAVariableHereYes")] {} false (.ident (nes "fieldName"))
          false false none (some (num 1))])]⟩ }
  , { name := "member-decorator-on-param"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "m")) false []
          [.plain [.dot (v "AVeryVeryLongTypeNameWrittenHereIndeed")
              (nes "theVeryLongNameForAVariableHereOkay")] {} (p "x") false none]
          none (some [])])]⟩ }
  , { name := "long-member-chain-decorator"
      prog := ⟨[st (.classDecl [] false (nes "E") [] none []
        [.method [.dot (.dot (.dot (.dot (.dot (.dot (.dot (v "Foo") (nes "bar")) (nes "baz"))
            (nes "qux")) (nes "longerAndLongerAndLonger")) (nes "more")) (nes "evenMore"))
            (nes "yetMore")] {} .normal (.ident (nes "m")) false [] [] none (some [])])]⟩ }
  , { name := "call-decorator-on-param"
      prog := ⟨[st (.classDecl [] false (nes "F") [] none []
        [.method [] {} .normal (.ident (nes "m")) false []
          [.plain [.call (.dot (v "Map") (nes "theIteratorOfTheList")) [] [.object []],
                   .dot (v "AVeryVeryLongTypeNameWrittenHere")
                     (nes "theVeryLongNameForAVariableHere")]
            {} (.withDefault (p "computeTheValue") .null) false (some (ty "Bar"))]
          (some (ty "ReadonlyArray")) (some [])])]⟩ }
  , { name := "member-decorator-on-class"
      prog := ⟨[st (.classDecl [.dot (v "AVeryVeryLongTypeNameWrittenHereIndeed")
          (nes "theVeryLongNameForAVariableHereOkay")] false (nes "D") [] none [] [])]⟩ }
  , { name := "infer-constraint-breaks"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.conditional (ty "X")
          (tyA "Array" [.infer_ (nes "TheVeryLongTypeParameterName")
            (some (.ref (.qualified (.ident (nes "AVeryVeryLongTypeName")) (nes "object")) []))])
          (ty "a") (ty "b")))]⟩ }
  , { name := "infer-constraint-fits"
      prog := ⟨[st (.typeAlias (nes "C") []
        (.conditional (ty "X")
          (tyA "Array" [.infer_ (nes "U") (some (.union [ty "A", ty "B"]))])
          (ty "a") (ty "b")))]⟩ }
  , { name := "type-param-constraint-breaks"
      prog := ⟨[st (.typeAlias (nes "B")
        [tpC "TheVeryLongTypeParameterNameHere"
          (.ref (.qualified (.ident (nes "AVeryVeryLongTypeNameWrittenHereOk")) (nes "object")) [])]
        (.numLit (JSNumber.ofNat 1)))]⟩ }
  , { name := "infer-constraint-breaks-deeper"
      prog := ⟨[st (.funcDecl false false (nes "fn698") []
        [parT "collection" (.conditional (.numLit (JSNumber.ofNat 1))
          (tyA "Array" [.infer_ (nes "TheVeryLongTypeParameterName")
            (some (.ref (.qualified (.ident (nes "AVeryVeryLongTypeNameWrittenHere"))
              (nes "object")) []))])
          (ty "never") (ty "string"))]
        none (some []))]⟩ }
  , { name := "hug-first-arg-nonnull-second"
      prog := ⟨[es (.call (v "theCollection") []
        [.arrow false [] [parT "abc" (ty "number")] (some (ty "void")) (.block [.return_ none]),
         .call (.dot (.call (.dot (.nonNull (v "collection")) (nes "g")) [] [])
           (nes "theIteratorOfTheList")) [] []])]⟩ }
  , { name := "hug-first-arg-short-type-args"
      prog := ⟨[es (.call (v "theCollection") [ty "A", ty "B", ty "C", ty "D"]
        [.arrow false [] [parT "abc" (ty "number")] (some (ty "void")) (.block [.return_ none]),
         .call (.dot (.call (.dot (v "collectionHere") (nes "g")) [] []) (nes "theIterator"))
           [] []])]⟩ }
  , { name := "hug-first-arg-four-type-args"
      prog := ⟨[es (.call (v "theCollection")
        [.array (ty "any"), .keyof (ty "U"),
         .typeQuery (.ident (nes "handler")) [.numLit (JSNumber.ofNat 1000), .numLit (JSNumber.ofNat 1000)],
         .objectType [prop "length" (ty "bigint"),
           .indexSig false (nes "item") (ty "string") (ty "never"),
           .indexSig true (nes "theVeryLongNameForAVariableHere") (ty "string") (ty "Result")]]
        [.arrow false [] [parT "abc" (.numLit (JSNumber.ofNat 15))]
            (some (.negNumLit (JSNumber.ofNat 1000)))
            (.block [.return_ (some (.object []))]),
         .call (.dot (.call (.dot (.nonNull (v "collection")) (nes "g")) [] [])
           (nes "theIteratorOfTheList")) [] []])]⟩ }
  , { name := "hug-first-arg-with-broken-type-args"
      prog := ⟨[es (.call (v "theCollection")
        [.objectType [prop "length" (ty "bigint"),
          .indexSig true (nes "theVeryLongNameForAVariableHere") (ty "string") (ty "Result")]]
        [.arrow false [] [parT "abc" (ty "number")] (some (ty "void"))
            (.block [.return_ none]),
         .call (.dot (.call (.dot (v "collection") (nes "g")) [] []) (nes "theIterator")) [] []])]⟩ }
  , { name := "hug-first-arg-no-type-args"
      prog := ⟨[es (.call (v "theCollection") []
        [.arrow false [] [parT "abc" (ty "number")] (some (ty "void"))
            (.block [.return_ none]),
         .call (.dot (.call (.dot (v "collection") (nes "g")) [] [])
           (nes "theIteratorOfTheListHere")) [] []])]⟩ }
  , { name := "decorated-accessor-field-class-value"
      prog := ⟨[st (.classDecl [] false (nes "Outer") [] none []
        [.field [call "Record" [], call "ReadonlyArray" []]
          { accessibility := some .private_, isStatic := true, isOverride := true } true
          (.ident (nes "kind")) true false
          (some (.templateLit "a string" [⟨.strLit "", "a rather long string literal here"⟩]))
          (some (.classExpr [] (some (nes "T")) [] none []
            [.field [] { isStatic := true } false (.ident (nes "abc")) false false
              (some (ty "symbol")) none]))])]⟩ }
  , { name := "accessor-field-class-value-no-decorators"
      prog := ⟨[st (.classDecl [] false (nes "Outer") [] none []
        [.field [] { accessibility := some .private_, isStatic := true, isOverride := true } true
          (.ident (nes "kind")) true false
          (some (.templateLit "a string" [⟨.strLit "", "a rather long string literal here"⟩]))
          (some (.classExpr [] (some (nes "T")) [] none []
            [.field [] { isStatic := true } false (.ident (nes "abc")) false false
              (some (ty "symbol")) none]))])]⟩ }
  , { name := "nonnull-call-member-rhs"
      prog := ⟨[.exportDecl (.decl (.decl .const
        ⟨declT "value102" (some (.union [ty "undefined", ty "null"]))
          (some (.dot (.nonNull (.call (v "f") [ty "ALongTypeNameNumberZero"]
            [.null, .number (JSNumber.bigint .decimal 12)])) (nes "target9"))), []⟩))]⟩ }
  , { name := "call-member-rhs-no-nonnull"
      prog := ⟨[.exportDecl (.decl (.decl .const
        ⟨declT "value102" (some (.union [ty "undefined", ty "null"]))
          (some (.dot (.call (v "f") [ty "ALongTypeNameNumberZero"]
            [.null, .number (JSNumber.bigint .decimal 12)]) (nes "target9"))), []⟩))]⟩ }
  , { name := "nonnull-call-member-rhs-no-type-args"
      prog := ⟨[.exportDecl (.decl (.decl .const
        ⟨declT "value102" (some (.union [ty "undefined", ty "null"]))
          (some (.dot (.nonNull (.call (v "fTheLongerNameOfAFunctionHereOk") []
            [.null, .number (JSNumber.bigint .decimal 12)])) (nes "target9"))), []⟩))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
