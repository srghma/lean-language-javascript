/-
# Why `ImportAttr` holds `String`s and not `NEString`s

`Language.JavaScript.ImportAttr` — one `with { type: "json" }` attribute of
an `import`, or of an `export … from` declaration — holds the *characters*
its key and its value denote, rather than the way they are written:

```
structure ImportAttr where
  key : String
  value : String
```

That is the right choice, and neither field can be an `NEString`, because
both may legitimately be empty.  The grammar of an attribute is

```
WithClause : with { WithEntries }
WithEntry  : AttributeKey : StringLiteral
AttributeKey : IdentifierName | StringLiteral
```

so a key written as a string literal, and every value, may be the empty
string literal `""`; and since these fields hold the denoted characters,
not the source spelling, the empty string literal denotes the empty string.
An `NEString` field would make such an import unrepresentable, even though
the parser of this project accepts it and the printer prints it back.

This module records that fact as three checks on the source

    import a from "m" with { "": "" };

* `MiniAST.emptyAttr_parse` — it parses, and the attribute it yields has an
  empty key and an empty value;
* `MiniAST.emptyAttr_roundTrip` — printing the tree and parsing the result
  again yields that same attribute, so the empty key and value survive a
  round trip;
* `MiniAST.emptyAttr_not_NEString` — no `NEString` holds either of them, so
  a refined field would have to reject this program.

The annotated tree is different, and there `NEString` *is* right:
`JSImportAttribute.key` and `.value` keep the literal as it is written,
quotes included, and `"\"\""` — the two quote characters — is not empty.
-/
import LanguageJavascriptMini.OfFull
import LanguageJavascriptMini.Printer

set_option autoImplicit false

namespace Language.JavaScript.MiniAST

/-- The import attributes of the first item of a program, when that item is
an import declaration; `[]` in every other case. -/
def firstImportAttrs (p : MiniProgram) : List ImportAttr :=
  match p.items with
  | .importDecl (.bare _ attrs) :: _ => attrs
  | .importDecl (.clause c) :: _ => c.attrs
  | _ => []

/-- An import with one attribute whose key and whose value are both the
empty string literal. -/
def emptyAttrSource : String := "import a from \"m\" with { \"\": \"\" };"

/-- The source parses, and the attribute of the resulting tree has an empty
key and an empty value: neither field can be an `NEString`. -/
theorem emptyAttr_parse :
    (parse emptyAttrSource).toOption.map firstImportAttrs = some [⟨"", ""⟩] := by
  native_decide

/-- Printing that tree and parsing the result again gives the same
attribute; the empty key and value are not lost on the way. -/
theorem emptyAttr_roundTrip :
    (do
      let p ← (parse emptyAttrSource).toOption
      let q ← (parse (printProgram p)).toOption
      pure (firstImportAttrs q)) = some [⟨"", ""⟩] := by
  native_decide

/-- No `NEString` holds the key, nor the value, of that attribute: an
`NEString` field would make the program above unrepresentable. -/
theorem emptyAttr_not_NEString (a : ImportAttr) (ha : a ∈ [(⟨"", ""⟩ : ImportAttr)]) :
    (¬ ∃ k : NEString, k.val = a.key) ∧ ¬ ∃ v : NEString, v.val = a.value := by
  simp only [List.mem_singleton] at ha
  subst ha
  exact ⟨fun ⟨k, hk⟩ => k.ne hk, fun ⟨v, hv⟩ => v.ne hv⟩

end Language.JavaScript.MiniAST
