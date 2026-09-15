import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part thirteen

The samples of this file pin down two layout rules random programs turned
up.  A `${…}` substitution of a template literal that breaks is indented
onto lines of its own when it holds an `as` or a `satisfies`, and is not
when it holds a `!` or a call.  And the one parameter of a function whose
annotation is an object type keeps that object type ungrouped even when
the parameter carries decorators, so that the two break together: the
parameter list is no longer hugged then, but the object type still breaks
with the decorators rather than on its own.  A parameter property, a
parameter that is not the only one, and a decorated parameter that fits
keep the object type on one line.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A class expression whose body breaks. -/
private def breakingClass13 : MiniExpr :=
  .classExpr [] (some (nes "Foo")) [] none []
    [.indexSig {} (nes "handler") (ty "string") (ty "Partial")]

/-- Five decorators, which prettier writes on lines of their own. -/
private def manyDecorators13 : List MiniExpr :=
  [call "Dec" [], call "Dec2" [], call "Dec3" [], call "Dec4" [], call "Dec5" []]

/-- The samples. -/
def samples13 : List Sample :=
  [ { name := "template-subst-as"
      prog := ⟨[st (constDecl "a" none
        (.template none [] "ok" [⟨.asExpr breakingClass13 .this, " the text after"⟩]))]⟩ }
  , { name := "template-subst-satisfies"
      prog := ⟨[st (constDecl "b" none
        (.template none [] "ok" [⟨.satisfies breakingClass13 .this, " the text after"⟩]))]⟩ }
  , { name := "template-subst-nonnull"
      prog := ⟨[st (constDecl "c" none
        (.template none [] "ok" [⟨.nonNull breakingClass13, " the text after"⟩]))]⟩ }
  , { name := "template-subst-call"
      prog := ⟨[st (constDecl "d" none
        (.template none [] "ok" [⟨call "aFunctionName" [breakingClass13], " the text after"⟩]))]⟩ }
  , { name := "decorated-only-param-object-type"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "f")) false []
          [.plain manyDecorators13 {} (p "computeTheValue") false
            (some (.objectType [.property true (.number (JSNumber.ofNat 1)) false
              (some (ty "number"))]))]
          (some (ty "void")) (some [])])]⟩ }
  , { name := "decorated-only-param-object-type-fits"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "f")) false []
          [.plain [call "Dec" []] {} (p "aParameterWithARatherLongName") false
            (some (.objectType [prop "aLongPropertyName" (ty "number")]))]
          (some (ty "void")) (some [])])]⟩ }
  , { name := "decorated-two-params-object-type"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "f")) false []
          [.plain manyDecorators13 {} (p "theValue") false
            (some (.objectType [prop "aKeyName" (ty "number")])),
           parT "another" (ty "string")]
          (some (ty "void")) (some [])])]⟩ }
  , { name := "decorated-parameter-property-object-type"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain manyDecorators13 { accessibility := some .private_, isReadonly := true }
            (p "theValue") false (some (.objectType [prop "aKeyName" (ty "number")]))]
          none (some [])])]⟩ }
  , { name := "undecorated-only-param-object-type"
      prog := ⟨[st (.funcDecl false false (nes "aFunctionWithALongName") []
        [parT "theValue" (.objectType [prop "aLongPropertyNameHere" (ty "number"),
          prop "anotherLongPropertyName" (ty "string")])] none (some []))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
