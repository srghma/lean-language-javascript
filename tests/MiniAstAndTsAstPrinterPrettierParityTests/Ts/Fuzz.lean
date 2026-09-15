import MiniTsAST

/-!
# A generator of random TypeScript sample programs

A small deterministic generator of `MiniTsAST` programs, used to compare
the printer's output with prettier's on many more shapes than the hand
written corpus covers.  The generator of `Tests.Fuzz` writes random
JavaScript, which `Tests.Ts.FuzzDump` prints through this printer as well;
what is written here is the TypeScript of the tree: the type expressions,
the declarations that only TypeScript has, and the expressions and the
members that carry types.

The programs stay inside the part of the language whose meaning does not
depend on the context, so that every one of them parses: a parameter
property is only written in a constructor, an `abstract` member only in an
abstract class, `infer` only in the `extends` clause of a conditional
type, a type predicate only on a function which has the parameter it names,
and an ambient declaration is only one that may carry no value.
-/

namespace Language.TypeScript.MiniTsAST.Fuzz

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- The state of the generator: a seed and a counter of fresh names. -/
structure St where
  /-- The seed of the pseudo random number generator. -/
  seed : UInt64
  /-- The number of fresh names handed out so far. -/
  fresh : Nat
deriving Inhabited

/-- One step of a linear congruential generator. -/
def step (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A pseudo random number below `n`, and the state that follows. -/
def rand (st : St) (n : Nat) : Nat × St :=
  let s := step st.seed
  let v := (s >>> 33).toNat
  (if n == 0 then 0 else v % n, { st with seed := s })

/-- A fresh name, and the state that follows. -/
def freshName (st : St) (prefix_ : String) : String × St :=
  (prefix_ ++ toString st.fresh, { st with fresh := st.fresh + 1 })

/-- The identifiers the generator picks from: names of several lengths, so
that a line falls just short of the eightieth column as often as it falls
just past it. -/
def names : Array String :=
  #["a", "bb", "value", "item", "index", "result", "handler", "theCollection",
    "computeTheValue", "theConfigurationObject", "aLongIdentifierNameNumberZero",
    "theVeryLongNameForAVariableHere", "f", "g", "xs", "abc", "node8", "target9",
    "iterator", "collection", "currentValue", "theHandlerName", "theIteratorOfTheList",
    "aVeryVeryLongIdentifierNameHere"]

/-- The names of the types the generator picks from: the predefined types
and names of several lengths. -/
def typeNames : Array String :=
  #["string", "number", "boolean", "any", "unknown", "never", "void", "undefined", "null",
    "object", "symbol", "bigint", "T", "U", "Foo", "Bar", "Result", "Handler",
    "TheConfigurationObject", "ALongTypeNameNumberZero", "AVeryVeryLongTypeNameWrittenHere",
    "Record", "Partial", "Map", "ReadonlyArray"]

/-- The names of the types which may be written with type arguments: a
predefined type, `string` or `never`, may not. -/
def genericTypeNames : Array String :=
  #["T", "U", "Foo", "Bar", "Result", "Handler", "TheConfigurationObject",
    "ALongTypeNameNumberZero", "AVeryVeryLongTypeNameWrittenHere", "Record", "Partial",
    "Map", "ReadonlyArray", "Array"]

/-- The names of `typeNames` which may also be written as a binding: a
reserved word, `null` or `void`, may name a type but not a binding. -/
def declTypeNames : Array String :=
  typeNames.filter fun n => n != "null" && n != "void"

/-- The names the generator declares a type parameter with, which may not
be a predefined type. -/
def typeParamNames : Array String :=
  #["T", "U", "K", "V", "E", "TValue", "TElement", "TheVeryLongTypeParameterName", "TKey"]

/-- The names the generator reads a property off with, which unlike an
identifier may be a reserved word. -/
def memberNames : Array String :=
  #["value", "length", "name", "class", "default", "in", "kind",
    "theRatherLongPropertyName", "id", "items"]

/-- The strings the generator picks from. -/
def strings : Array String :=
  #["", "ok", "a string", "it's", "say \"hi\"", "a rather long string literal here",
    "a-key", "three words here", "mod", "./a/rather/long/module/path/here"]

/-- The keys of an import attribute the generator picks from. -/
def attrKeys : Array String := #["type", "resolution-mode", "a-key"]

/-- The values of an import attribute the generator picks from. -/
def attrValues : Array String := #["json", "import", "require"]

/-- The numeric literals the generator picks from. -/
def numbers : Array JSNumber :=
  #[.decimal 0 0, .decimal 15 (-1), .decimal 1 21, .decimal 123456 (-3),
    .radix .hexadecimal 255, .decimal 1000 0, .bigint .decimal 12]

/-- A non-empty string. -/
def nes (x : String) : NEString := NEString.ofString! x

/-- An identifier expression. -/
def ident (x : String) : MiniExpr := .ident (nes x)

/-- A name from `names`. -/
def genName (st : St) : String × St :=
  let (k, st) := rand st names.size
  (names[k]!, st)

/-- A name of a type. -/
def genTypeName (st : St) : String × St :=
  let (k, st) := rand st typeNames.size
  (typeNames[k]!, st)

/-- A name of a type which may be written with type arguments. -/
def genGenericTypeName (st : St) : String × St :=
  let (k, st) := rand st genericTypeNames.size
  (genericTypeNames[k]!, st)

/-- A name of a type which may also be written as a binding. -/
def genDeclTypeName (st : St) : String × St :=
  let (k, st) := rand st declTypeNames.size
  (declTypeNames[k]!, st)

/-- A name to declare a type parameter with. -/
def genTypeParamName (st : St) : String × St :=
  let (k, st) := rand st typeParamNames.size
  (typeParamNames[k]!, st)

/-- A name to read a property off with. -/
def genMemberName (st : St) : String × St :=
  let (k, st) := rand st (memberNames.size + names.size)
  (if k < memberNames.size then memberNames[k]! else names[k - memberNames.size]!, st)

/-- A string literal. -/
def genString (st : St) : String × St :=
  let (k, st) := rand st strings.size
  (strings[k]!, st)

/-- A numeric literal. -/
def genNumber (st : St) : JSNumber × St :=
  let (k, st) := rand st numbers.size
  (numbers[k]!, st)

/-- The name of a type, possibly read through a namespace. -/
def genEntityName (st : St) : TsEntityName × St :=
  let (k, st) := rand st 6
  let (n, st) := genTypeName st
  if k == 0 then
    let (m, st) := genGenericTypeName st
    (.qualified (.ident (nes m)) (nes n), st)
  else (.ident (nes n), st)

/-- An accessibility modifier, more often than not none at all. -/
def genAccessibility (st : St) : Option TsAccessibility × St :=
  let (k, st) := rand st 6
  match k with
  | 0 => (some .public_, st)
  | 1 => (some .protected_, st)
  | 2 => (some .private_, st)
  | _ => (none, st)

/-- A property name. -/
def genPropertyName (st : St) : MiniPropertyName × St :=
  let (k, st) := rand st 12
  match k with
  | 0 =>
      let (s, st) := genString st
      (.string s, st)
  | 1 =>
      let (n, st) := genNumber st
      -- a property name may not be written with the trailing `n` of a
      -- `BigInt` literal
      (match n with
        | .bigint .. => .ident (nes "value")
        | _ => .number n, st)
  | 2 =>
      let (n, st) := genName st
      (.computed (ident n), st)
  | _ =>
      let (n, st) := genMemberName st
      (.ident (nes n), st)

mutual

/-- A random type expression of depth at most `d`. -/
partial def genType (d : Nat) (st : St) : MiniTsType × St :=
  if d == 0 then
    let (k, st) := rand st 8
    match k with
    | 0 =>
        let (s, st) := genString st
        (.strLit s, st)
    | 1 =>
        let (n, st) := genNumber st
        (.numLit n, st)
    | 2 =>
        let (n, st) := genNumber st
        (.negNumLit n, st)
    | _ =>
        let (n, st) := genEntityName st
        (.ref n [], st)
  else
    let (k, st) := rand st 24
    match k with
    | 0 | 1 =>
        let (many, st) := rand st 3
        if many == 0 then
          let (n, st) := genEntityName st
          (.ref n [], st)
        else
          -- only a type which is not a predefined one takes arguments
          let (n, st) := genGenericTypeName st
          let (args, st) := genTypes (d - 1) st
          (.ref (.ident (nes n)) args, st)
    | 2 =>
        let (e, st) := genType (d - 1) st
        (.array e, st)
    | 3 =>
        let (o, st) := genType (d - 1) st
        let (i, st) := genType 0 st
        (.indexed o i, st)
    | 4 | 5 =>
        let (ts, st) := genTypes (d - 1) st
        (match ts with
          | [] | [_] =>
              let (n, st') := (genTypeName st)
              (.union [.ref (.ident (nes n)) [], .ref (.ident (nes "null")) []], st')
          | ts => (.union ts, st), st).1
    | 6 =>
        let (ts, st) := genTypes (d - 1) st
        (match ts with
          | [] | [_] => .intersection [.ref (.ident (nes "Foo")) [], .ref (.ident (nes "Bar")) []]
          | ts => .intersection ts, st)
    | 7 =>
        let (tps, st) := genTypeParams (d - 1) st
        let (ps, st) := genParams (d - 1) false false st
        let (r, st) := genType (d - 1) st
        (.fn tps ps r, st)
    | 8 =>
        let (ps, st) := genParams (d - 1) false false st
        let (r, st) := genType (d - 1) st
        let (a, st) := rand st 3
        (.ctor (a == 0) [] ps r, st)
    | 9 =>
        let (n, st) := genName st
        let (hasArgs, st) := rand st 3
        let (args, st) := if hasArgs == 0 then genTypes (d - 1) st else ([], st)
        (.typeQuery (.ident (nes n)) args, st)
    | 10 =>
        let (e, st) := genType (d - 1) st
        (.keyof e, st)
    | 11 =>
        let (e, st) := genType (d - 1) st
        (.readonlyOp (match e with
          | .array _ | .tuple _ => e
          | _ => .array e), st)
    | 12 =>
        -- `infer` is only written in the `extends` clause of a conditional
        let (c, st) := genType (d - 1) st
        let (ext, st) := genType (d - 1) st
        let (tt, st) := genType (d - 1) st
        let (ft, st) := genType (d - 1) st
        let (inf, st) := rand st 4
        let (u, st) := genTypeParamName st
        -- `infer U`, and `infer U extends C`, which only the `extends`
        -- clause of a conditional may hold
        if inf == 0 then
          (.conditional c (.ref (.ident (nes "Array")) [.infer_ (nes u) none]) tt ft, st)
        else if inf == 1 then
          let (con, st) := genType 0 st
          (.conditional c (.ref (.ident (nes "Array")) [.infer_ (nes u) (some con)]) tt ft, st)
        else (.conditional c ext tt ft, st)
    | 13 | 14 =>
        let (ms, st) := genTypeMembers (d - 1) st
        (.objectType ms, st)
    | 15 =>
        let (key, st) := genTypeParamName st
        let (c, st) := genType (d - 1) st
        let (v, st) := genType (d - 1) st
        let (ro, st) := rand st 4
        let (opt, st) := rand st 4
        let readonlyMod : Option TsMappedMod :=
          match ro with | 0 => some .keep | 1 => some .add | 2 => some .remove | _ => none
        let optionalMod : Option TsMappedMod :=
          match opt with | 0 => some .keep | 1 => some .add | 2 => some .remove | _ => none
        let (hasAs, st) := rand st 3
        let (as_, st) :=
          if hasAs == 0 then
            let (a, st) := genType 0 st
            (some a, st)
          else (none, st)
        (.mapped readonlyMod (nes key) c as_ optionalMod (some v), st)
    | 16 =>
        let (es, st) := genTupleElems (d - 1) st
        (.tuple es, st)
    | 17 =>
        let (a, st) := genType (d - 1) st
        let (h, st) := genString st
        let (s, st) := genString st
        (.templateLit h [⟨a, s⟩], st)
    | 18 =>
        let (m, st) := genString st
        let (q, st) := rand st 2
        let (n, st) := genTypeName st
        let (hasArgs, st) := rand st 3
        let (args, st) := if hasArgs == 0 && q == 0 then genTypes (d - 1) st else ([], st)
        -- `typeof import("m")`, and the import attributes of the import
        let (isTypeof, st) := rand st 3
        let (withAttrs, st) := rand st 3
        let (key, st) := rand st attrKeys.size
        let (value, st) := rand st attrValues.size
        let attrs : List ImportAttr :=
          if withAttrs == 0 then [⟨attrKeys[key]!, attrValues[value]!⟩] else []
        (.importType (isTypeof == 0) m attrs
          (if q == 0 then some (.ident (nes n)) else none) args, st)
    | 20 =>
        -- `this`, the type of the object a method is called on
        (.this, st)
    | 21 =>
        (.uniqueSymbol, st)
    | 19 =>
        let (n, st) := genGenericTypeName st
        let (args, st) := genTypes (d - 1) st
        (.ref (.ident (nes n)) args, st)
    | _ =>
        let (n, st) := genEntityName st
        (.ref n [], st)

/-- A short list of types. -/
partial def genTypes (d : Nat) (st : St) : List MiniTsType × St :=
  let (n, st) := rand st 4
  genTypeList (n + 1) d st

/-- A list of `n` types. -/
partial def genTypeList (n d : Nat) (st : St) : List MiniTsType × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (t, st) := genType d st
      let (rest, st) := genTypeList k d st
      (t :: rest, st)

/-- A short list of tuple elements. -/
partial def genTupleElems (d : Nat) (st : St) : List MiniTsTupleElem × St :=
  let (n, st) := rand st 4
  genTupleElemList n d st

/-- A list of `n` tuple elements. -/
partial def genTupleElemList (n d : Nat) (st : St) : List MiniTsTupleElem × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (t, st) := genType d st
      let (kind, st) := rand st 6
      let (name, st) := genName st
      let elem : MiniTsTupleElem :=
        match kind with
        | 0 => .optional t
        | 1 => if k == 0 then .rest (.array t) else .elem t
        | 2 => .named (nes name) false false t
        | 3 => .named (nes name) true false t
        | _ => .elem t
      let (rest, st) := genTupleElemList k d st
      (elem :: rest, st)

/-- A short list of the members of an object type or of an interface. -/
partial def genTypeMembers (d : Nat) (st : St) : List MiniTsTypeMember × St :=
  let (n, st) := rand st 4
  genTypeMemberList n d st

/-- A list of `n` members of an object type. -/
partial def genTypeMemberList (n d : Nat) (st : St) : List MiniTsTypeMember × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (m, st) := genTypeMember d st
      let (rest, st) := genTypeMemberList k d st
      (m :: rest, st)

/-- One member of an object type or of an interface. -/
partial def genTypeMember (d : Nat) (st : St) : MiniTsTypeMember × St :=
  let (kind, st) := rand st 12
  match kind with
  | 0 | 1 | 2 | 3 | 4 =>
      let (key, st) := genPropertyName st
      let (t, st) := genType (if d == 0 then 0 else d - 1) st
      let (ro, st) := rand st 5
      let (opt, st) := rand st 4
      (.property (ro == 0) key (opt == 0) (some t), st)
  | 5 | 6 =>
      let (key, st) := genPropertyName st
      let (tps, st) := genTypeParams (if d == 0 then 0 else d - 1) st
      let (ps, st) := genParams (if d == 0 then 0 else d - 1) false false st
      let (r, st) := genType (if d == 0 then 0 else d - 1) st
      let (opt, st) := rand st 4
      (.method .normal key (opt == 0) tps ps (some r), st)
  | 7 =>
      let (key, st) := genPropertyName st
      let (r, st) := genType (if d == 0 then 0 else d - 1) st
      (.method .get key false [] [] (some r), st)
  | 8 =>
      let (key, st) := genPropertyName st
      let (n, st) := genName st
      let (t, st) := genType (if d == 0 then 0 else d - 1) st
      (.method .set key false [] [MiniParam.typed (.ident (nes n)) t] none, st)
  | 9 =>
      let (ps, st) := genParams (if d == 0 then 0 else d - 1) false false st
      let (r, st) := genType (if d == 0 then 0 else d - 1) st
      (.callSig [] ps (some r), st)
  | 10 =>
      let (ps, st) := genParams (if d == 0 then 0 else d - 1) false false st
      let (r, st) := genType (if d == 0 then 0 else d - 1) st
      (.ctorSig [] ps (some r), st)
  | _ =>
      let (n, st) := genName st
      let (v, st) := genType (if d == 0 then 0 else d - 1) st
      let (ro, st) := rand st 4
      (.indexSig (ro == 0) (nes n) (.ref (.ident (nes "string")) []) v, st)

/-- A short list of type parameters, often none at all. -/
partial def genTypeParams (d : Nat) (st : St) (variance : Bool := false) :
    List MiniTsTypeParam × St :=
  let (k, st) := rand st 4
  if k == 0 then
    let (n, st) := rand st 3
    genTypeParamList (n + 1) d st variance
  else ([], st)

/-- A list of `n` type parameters.  `variance` allows the variance
annotations, which only the type parameters of a class, an interface and
a type alias may be written with. -/
partial def genTypeParamList (n d : Nat) (st : St) (variance : Bool := false) :
    List MiniTsTypeParam × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (name, st) := genTypeParamName st
      let (hasC, st) := rand st 3
      let (hasD, st) := rand st 4
      let (isConst, st) := rand st 8
      let (varianceRand, st) := rand st 10
      let varianceMod : Option TsVariance :=
        if !variance then none
        else
          match varianceRand with
          | 0 => some .in_
          | 1 => some .out_
          | 2 => some .inOut
          | _ => none
      let (c, st) := if hasC == 0 then
          let (t, st) := genType (if d == 0 then 0 else d - 1) st
          (some t, st)
        else (none, st)
      let (dflt, st) := if hasD == 0 then
          let (t, st) := genType 0 st
          (some t, st)
        else (none, st)
      let (rest, st) := genTypeParamList k d st variance
      (⟨isConst == 0, varianceMod, nes name, c, dflt⟩ :: rest, st)

/-- A decorator: `@Name`, `@Name.inner`, `@Name(args)`.  The grammar only
allows a name, a name read through a namespace, and a call of one. -/
partial def genDecorator (d : Nat) (st : St) : MiniExpr × St :=
  let (name, st) := genGenericTypeName st
  let (kind, st) := rand st 5
  match kind with
  | 0 => (ident name, st)
  | 1 =>
      let (m, st) := genMemberName st
      (.dot (ident name) (nes m), st)
  | 2 =>
      let (args, st) := genExprList 2 (if d == 0 then 0 else d - 1) st
      (.call (ident name) [] args, st)
  | 3 =>
      let (m, st) := genMemberName st
      let (e, st) := genSimpleExpr st
      (.call (.dot (ident name) (nes m)) [] [e], st)
  | _ => (.call (ident name) [] [], st)

/-- A short list of decorators, most often none at all. -/
partial def genDecorators (d : Nat) (st : St) : List MiniExpr × St :=
  let (k, st) := rand st 8
  match k with
  | 0 =>
      let (x, st) := genDecorator d st
      ([x], st)
  | 1 =>
      let (x, st) := genDecorator d st
      let (y, st) := genDecorator d st
      ([x, y], st)
  | _ => ([], st)

/-- A short list of parameters.  `ctor` allows the modifiers that make a
parameter a parameter property, which only a constructor may carry;
`defaults` allows a default value, which only a function that has a body
may carry; `decorated` allows the decorators only a parameter of a
method of a class may carry. -/
partial def genParams (d : Nat) (ctor defaults : Bool) (st : St)
    (decorated : Bool := false) : List MiniParam × St :=
  let (n, st) := rand st 4
  genParamList n d ctor defaults st decorated

/-- A list of `n` parameters; the optional ones, and the rest parameter,
are written last, as the grammar requires. -/
partial def genParamList (n d : Nat) (ctor defaults : Bool) (st : St)
    (decorated : Bool := false) : List MiniParam × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (name, st) := genName st
      let (kind, st) := rand st 12
      let (t, st) := genType (if d == 0 then 0 else d - 1) st
      let (decs, st) :=
        if decorated then genDecorators (if d == 0 then 0 else d - 1) st else ([], st)
      let (mods, st) :=
        if ctor then
          let (acc, st) := genAccessibility st
          let (ro, st) := rand st 4
          ({ accessibility := acc, isReadonly := ro == 0 : TsParamMods }, st)
        else (({} : TsParamMods), st)
      -- a rest parameter, and an optional one, are only written last
      let (param, st) : MiniParam × St :=
        if k == 0 then
          match kind with
          | 0 => (.rest decs (.ident (nes name)) (some (.array t)), st)
          | 1 => (.plain decs mods (.ident (nes name)) true (some t), st)
          | 2 =>
              let (e, st) := genSimpleExpr st
              (if defaults then
                  .plain decs mods (.withDefault (.ident (nes name)) e) false (some t)
                else .plain decs mods (.ident (nes name)) false (some t), st)
          | 3 =>
              let (a, st) := genName st
              let (b, st) := genName st
              (.plain decs {} (.object [⟨.ident (nes a), .ident (nes a)⟩,
                                   ⟨.ident (nes b), .ident (nes b)⟩] none) false (some t), st)
          | _ => (.plain decs mods (.ident (nes name)) false (some t), st)
        else
          match kind with
          | 2 =>
              let (e, st) := genSimpleExpr st
              (if defaults then
                  .plain decs mods (.withDefault (.ident (nes name)) e) false (some t)
                else .plain decs mods (.ident (nes name)) false (some t), st)
          | 3 =>
              let (a, st) := genName st
              (.plain decs {} (.array [.elem (.ident (nes a))]) false (some (.array t)), st)
          | _ => (.plain decs mods (.ident (nes name)) false (some t), st)
      let (rest, st) := genParamList k d ctor defaults st decorated
      (param :: rest, st)

/-- The value of a member of an `enum`, which may only be a constant. -/
partial def genEnumValue (st : St) : MiniExpr × St :=
  let (k, st) := rand st 4
  match k with
  | 0 =>
      let (s, st) := genString st
      (.string s, st)
  | 1 =>
      let (a, st) := genNumber st
      let (b, st) := genNumber st
      (.binary (.number a) .plus (.number b), st)
  | _ =>
      let (n, st) := genNumber st
      (match n with | .bigint .. => .number (JSNumber.ofNat 1) | _ => .number n, st)

/-- A simple expression: one that needs no depth. -/
partial def genSimpleExpr (st : St) : MiniExpr × St :=
  let (k, st) := rand st 8
  match k with
  | 0 =>
      let (n, st) := genNumber st
      (.number n, st)
  | 1 =>
      let (s, st) := genString st
      (.string s, st)
  | 2 => (.true_, st)
  | 3 => (.null, st)
  | 4 => (.array [], st)
  | 5 => (.object [], st)
  | _ =>
      let (n, st) := genName st
      (ident n, st)

/-- A random expression of depth at most `d`, written to exercise the
TypeScript expressions: the ones that carry a type. -/
partial def genExpr (d : Nat) (st : St) : MiniExpr × St :=
  if d == 0 then genSimpleExpr st else
    let (k, st) := rand st 34
    match k with
    | 0 | 1 => genSimpleExpr st
    | 2 =>
        let (e, st) := genExpr (d - 1) st
        let (t, st) := genType (d - 1) st
        (.asExpr e t, st)
    | 3 =>
        let (e, st) := genExpr (d - 1) st
        (.asExpr e (.ref (.ident (nes "const")) []), st)
    | 4 =>
        let (e, st) := genExpr (d - 1) st
        let (t, st) := genType (d - 1) st
        (.satisfies e t, st)
    | 5 | 6 =>
        let (e, st) := genExpr (d - 1) st
        (.nonNull (match e with
          | .number _ | .string _ | .true_ | .null => ident "value"
          | e => e), st)
    | 7 =>
        let (n, st) := genName st
        let (args, st) := genTypes (d - 1) st
        (.instantiation (ident n) args, st)
    | 8 | 9 =>
        let (n, st) := genName st
        let (targs, st) := genTypes (d - 1) st
        let (args, st) := genExprList 2 (d - 1) st
        (.call (ident n) targs args, st)
    | 10 =>
        let (n, st) := genName st
        let (targs, st) := genTypes (d - 1) st
        let (args, st) := genExprList 1 (d - 1) st
        (.new (ident n) targs args, st)
    | 11 =>
        let (tps, st) := genTypeParams (d - 1) st
        let (ps, st) := genParams (d - 1) false true st
        let (r, st) := genType (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (async, st) := rand st 4
        (.arrow (async == 0) tps ps (some r) (.expr b), st)
    | 12 =>
        let (ps, st) := genParams (d - 1) false true st
        let (r, st) := genType (d - 1) st
        let (e, st) := genExpr (d - 1) st
        (.arrow false [] ps (some r) (.block [.return_ (some e)]), st)
    | 13 =>
        let (o, st) := genExpr (d - 1) st
        let (n, st) := genMemberName st
        (.dot (match o with
          | .number _ => ident "value"
          | o => o) (nes n), st)
    | 14 =>
        let (o, st) := genName st
        let (n, st) := genMemberName st
        let (m, st) := genMemberName st
        (.chain (ident o) ⟨.dot true (nes n), [.nonNull, .dot false (nes m)]⟩, st)
    | 15 =>
        let (o, st) := genName st
        let (n, st) := genMemberName st
        let (args, st) := genExprList 1 (d - 1) st
        (.chain (ident o) ⟨.dot false (nes n), [.nonNull, .call false [] args]⟩, st)
    | 16 =>
        let (o, st) := genName st
        let (n, st) := genMemberName st
        let (m, st) := genMemberName st
        let (args, st) := genExprList 1 (d - 1) st
        (.call (.dot (.call (.dot (.nonNull (ident o)) (nes n)) [] args) (nes m)) [] [], st)
    | 17 =>
        let (n, st) := genName st
        let (t, st) := genType (d - 1) st
        let (e, st) := genExpr (d - 1) st
        (.call (ident n) [t] [e], st)
    | 18 =>
        let (props, st) := genProperties (d - 1) st
        (.object props, st)
    | 19 =>
        let (els, st) := genExprList 3 (d - 1) st
        (.array (els.map MiniArrayElement.elem), st)
    | 20 =>
        let (c, st) := genExpr (d - 1) st
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        (.ternary c a b, st)
    | 21 =>
        let (l, st) := genExpr (d - 1) st
        let (r, st) := genExpr (d - 1) st
        let (op, st) := rand st 4
        (.binary l (match op with
          | 0 => .plus | 1 => .and | 2 => .coalesce | _ => .strictEq) r, st)
    | 22 =>
        let (name, st) := genName st
        let (t, st) := genType (d - 1) st
        let (e, st) := genExpr (d - 1) st
        (.assign (ident name) .assign (.asExpr e t), st)
    | 23 =>
        -- a generic arrow function, whose one unconstrained type
        -- parameter keeps a trailing comma of its own
        let (name, st) := genTypeParamName st
        let (p, st) := genName st
        let (e, st) := genExpr (d - 1) st
        (.arrow false [⟨false, none, nes name, none, none⟩]
          [MiniParam.typed (.ident (nes p)) (.ref (.ident (nes name)) [])] none (.expr e), st)
    | 24 =>
        let (f, st) := genName st
        let (e, st) := genExpr (d - 1) st
        let (t, st) := genType (d - 1) st
        (.call (.dot (.asExpr e t) (nes "map")) [] [ident f], st)
    | 25 =>
        let (elems, st) := genClassElements (d - 1) st
        let (n, st) := genDeclTypeName st
        (.classExpr [] (some (nes n)) [] none [] elems, st)
    | 26 =>
        let (n, st) := genName st
        let (t, st) := genType (d - 1) st
        (.nonNull (.asExpr (ident n) t), st)
    | 27 =>
        let (f, st) := genName st
        let (a, st) := genExpr (d - 1) st
        let (t, st) := genType (d - 1) st
        (.call (ident f) [] [.asExpr a t], st)
    | 29 =>
        -- a tagged template literal read at type arguments,
        -- `` tag<T>`text ${e}` ``
        let (name, st) := genName st
        let (m, st) := genMemberName st
        let (onMember, st) := rand st 2
        let tag := if onMember == 0 then .dot (ident name) (nes m) else ident name
        let (nargs, st) := rand st 2
        let (targs, st) := genTypeList (nargs + 1) (d - 1) st
        let (head, st) := genString st
        let (hasPart, st) := rand st 2
        let (e, st) := genExpr (d - 1) st
        let parts : List MiniTemplatePart :=
          if hasPart == 0 then [⟨e, " and the text that follows"⟩] else []
        (.template (some tag) targs head parts, st)
    | 32 =>
        -- the callee of a `new`, which an `as` takes parentheses in
        let (n, st) := genName st
        let (m, st) := genMemberName st
        let (t, st) := genType (d - 1) st
        let (args, st) := genExprList 1 (d - 1) st
        let (k2, st) := rand st 3
        let callee : MiniExpr :=
          match k2 with
          | 0 => .asExpr (ident n) t
          | 1 => .dot (.asExpr (ident n) t) (nes m)
          | _ => .satisfies (ident n) t
        (.new callee [] args, st)
    | 30 =>
        -- `as` and `satisfies` written one after the other
        let (e, st) := genExpr (d - 1) st
        let (t, st) := genType (d - 1) st
        let (u, st) := genType (d - 1) st
        let (k2, st) := rand st 2
        (if k2 == 0 then .asExpr (.satisfies e t) u else .asExpr (.asExpr e t) u, st)
    | 31 =>
        -- a type written inside a template literal substitution, and one
        -- inside a spread argument
        let (e, st) := genExpr (d - 1) st
        let (t, st) := genType (d - 1) st
        let (f, st) := genName st
        let (head, st) := genString st
        let (k2, st) := rand st 2
        (if k2 == 0 then .template none [] head [⟨.asExpr e t, " the text after"⟩]
          else .call (ident f) [] [.spread (.asExpr e (.array t))], st)
    | 28 =>
        -- a JSX component read at type arguments, `<Comp<T> x={e} />`
        let (name, st) := genDeclTypeName st
        let (nargs, st) := rand st 3
        let (args, st) := genTypeList (nargs + 1) (d - 1) st
        let (hasAttr, st) := rand st 2
        let (e, st) := genExpr (d - 1) st
        let attrs : List MiniJSXAttribute :=
          if hasAttr == 0 then [.attr (.ident (nes "value")) (some (.expr e))] else []
        let (hasKids, st) := rand st 3
        let kids : Option (List MiniJSXChild) :=
          if hasKids == 0 then some [.text "the text of the child"] else none
        (.jsx (.element (.ident (nes name)) args attrs kids), st)
    | _ =>
        let (n, st) := genName st
        let (t, st) := genType (d - 1) st
        (.asExpr (ident n) t, st)

/-- A list of at most `n` expressions. -/
partial def genExprList (n d : Nat) (st : St) : List MiniExpr × St :=
  let (k, st) := rand st (n + 1)
  genExprsOf k d st

/-- A list of exactly `n` expressions. -/
partial def genExprsOf (n d : Nat) (st : St) : List MiniExpr × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (e, st) := genExpr d st
      let (rest, st) := genExprsOf k d st
      (e :: rest, st)

/-- A short list of the properties of an object literal. -/
partial def genProperties (d : Nat) (st : St) : List MiniProperty × St :=
  let (n, st) := rand st 4
  genPropertyList n d st

/-- A list of `n` properties of an object literal. -/
partial def genPropertyList (n d : Nat) (st : St) : List MiniProperty × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (kind, st) := rand st 8
      let (key, st) := genPropertyName st
      let (prop, st) : MiniProperty × St :=
        match kind with
        | 0 =>
            let (n, st) := genName st
            (.shorthand (nes n), st)
        | 1 =>
            let (tps, st) := genTypeParams (if d == 0 then 0 else d - 1) st
            let (ps, st) := genParams (if d == 0 then 0 else d - 1) false true st
            let (r, st) := genType (if d == 0 then 0 else d - 1) st
            (.method .normal key tps ps (some r) [], st)
        | _ =>
            let (e, st) := genExpr (if d == 0 then 0 else d - 1) st
            (.keyValue key e, st)
      let (rest, st) := genPropertyList k d st
      (prop :: rest, st)

/-- A short list of the members of a class.  `abstract_` says that the
class is an abstract one, which alone may hold an abstract member. -/
partial def genClassElementsOf (n d : Nat) (abstract_ : Bool) (st : St)
    (decorated : Bool := false) : List MiniClassElement × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (m, st) := genClassElement d abstract_ st decorated
      let (rest, st) := genClassElementsOf k d abstract_ st decorated
      (m :: rest, st)

/-- A short list of the members of a class. -/
partial def genClassElements (d : Nat) (st : St) : List MiniClassElement × St :=
  let (n, st) := rand st 4
  genClassElementsOf n d false st

/-- One member of a class. -/
partial def genClassElement (d : Nat) (abstract_ : Bool) (st : St)
    (decorated : Bool := false) : MiniClassElement × St :=
  let dd := if d == 0 then 0 else d - 1
  let (kind, st) := rand st 16
  let (acc, st) := genAccessibility st
  let (isStatic, st) := rand st 5
  let (isReadonly, st) := rand st 5
  let (isAbstractRand, st) := rand st 4
  let (isOverride, st) := rand st 6
  let isAbstract := abstract_ && isAbstractRand == 0
  let mods : TsMemberMods :=
    { accessibility := acc, isStatic := !isAbstract && isStatic == 0,
      isOverride := isOverride == 0,
      isAbstract := isAbstract, isReadonly := isReadonly == 0 }
  -- a decorator may not be written on an abstract member, nor anywhere
  -- inside a class expression, which TypeScript does not accept
  let (decs, st) := if isAbstract || !decorated then ([], st) else genDecorators dd st
  match kind with
  | 0 | 1 | 2 | 3 =>
      -- a field, which an abstract member carries no value for
      let (key, st) := genPropertyName st
      let (t, st) := genType dd st
      let (opt, st) := rand st 5
      let (hasInit, st) := rand st 3
      let (e, st) := genExpr dd st
      let (isAccessor, st) := rand st 8
      let init := if isAbstract || hasInit == 0 then none else some e
      -- the definite assignment assertion is only written where there is
      -- no value, and `?` and `!` may not be written together
      let (definite, st) := rand st 6
      let isDefinite := init.isNone && !isAbstract && opt != 0 && definite == 0
      (.field decs { mods with isReadonly := mods.isReadonly && !isAccessor.beq 0 }
        (isAccessor == 0 && !isAbstract && !mods.isReadonly) key (opt == 0) isDefinite
        (some t) init, st)
  | 4 | 5 | 6 =>
      let (key, st) := genPropertyName st
      let (tps, st) := genTypeParams dd st
      let (ps, st) := genParams dd false (!isAbstract) st (decorated := decorated && !isAbstract)
      let (r, st) := genType dd st
      let (body, st) := genStatements 1 dd st
      let (opt, st) := rand st 6
      -- an abstract method is written with no body
      (.method decs { mods with isReadonly := false } .normal key (opt == 0) tps ps (some r)
        (if isAbstract then none else some body), st)
  | 7 =>
      -- a constructor, whose parameters may be parameter properties
      let (ps, st) := genParams dd true true st (decorated := decorated)
      let (body, st) := genStatements 1 dd st
      (.method [] { accessibility := acc } .normal (.ident (nes "constructor")) false [] ps none
        (some body), st)
  | 8 =>
      let (key, st) := genPropertyName st
      let (r, st) := genType dd st
      let (e, st) := genExpr dd st
      (.method decs { mods with isReadonly := false, isAbstract := false } .get key false [] []
        (some r) (some [.return_ (some e)]), st)
  | 9 =>
      let (key, st) := genPropertyName st
      let (n, st) := genName st
      let (t, st) := genType dd st
      (.method decs { mods with isReadonly := false, isAbstract := false } .set key false []
        [MiniParam.typed (.ident (nes n)) t] none (some []), st)
  | 10 =>
      let (n, st) := genName st
      let (v, st) := genType dd st
      let (ro, st) := rand st 3
      (.indexSig { isStatic := isStatic == 0, isReadonly := ro == 0 } (nes n)
        (.ref (.ident (nes "string")) []) v, st)
  | 11 =>
      let (body, st) := genStatements 1 dd st
      (.staticBlock body, st)
  | 12 =>
      -- an overload signature, with no body
      let (key, st) := genPropertyName st
      let (ps, st) := genParams dd false false st
      let (r, st) := genType dd st
      (.method [] { mods with isReadonly := false, isAbstract := false } .normal key false [] ps
        (some r) none, st)
  | 13 =>
      let (key, st) := genPropertyName st
      let (tps, st) := genTypeParams dd st
      let (ps, st) := genParams dd false true st (decorated := decorated)
      let (r, st) := genType dd st
      let (body, st) := genStatements 1 dd st
      (.method decs { mods with isReadonly := false, isAbstract := false } .async key false tps ps
        (some (.ref (.ident (nes "Promise")) [r])) (some body), st)
  | 14 =>
      let (key, st) := genPropertyName st
      let (t, st) := genType dd st
      (.field [] { mods with isAbstract := false, isStatic := true } false key false false
        (some t) none, st)
  | _ =>
      -- an ambient field, `declare x: number;`, which carries no value
      let (key, st) := genPropertyName st
      let (t, st) := genType dd st
      (.field [] { accessibility := acc, isDeclare := true, isStatic := isStatic == 0,
                   isReadonly := isReadonly == 0 }
        false key false false (some t) none, st)

/-- A list of at most `n` statements. -/
partial def genStatements (n d : Nat) (st : St) : List MiniStatement × St :=
  let (k, st) := rand st (n + 1)
  genStatementList k d st

/-- A list of `n` statements. -/
partial def genStatementList (n d : Nat) (st : St) : List MiniStatement × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (s, st) := genStatement d st
      let (rest, st) := genStatementList k d st
      (s :: rest, st)

/-- A random statement of depth at most `d`. -/
partial def genStatement (d : Nat) (st : St) : MiniStatement × St :=
  let dd := if d == 0 then 0 else d - 1
  let (kind, st) := rand st (if d == 0 then 4 else 22)
  match kind with
  | 0 | 1 =>
      -- a declaration with a type annotation
      let (name, st) := freshName st "value"
      let (t, st) := genType dd st
      let (e, st) := genExpr dd st
      let (hasType, st) := rand st 4
      let (hasInit, st) := rand st 6
      let (k, st) := rand st 3
      let kind : VarKind := match k with | 0 => .const | 1 => .let_ | _ => .var
      let type := if hasType == 0 then none else some t
      let init := if hasInit == 0 && kind != .const then none else some e
      (.decl kind ⟨⟨.ident (nes name), false, type, init⟩, []⟩, st)
  | 2 =>
      let (e, st) := genExpr dd st
      (.expr e, st)
  | 3 =>
      let (name, st) := freshName st "T"
      let (tps, st) := genTypeParams dd st (variance := true)
      let (t, st) := genType dd st
      (.typeAlias (nes name) tps t, st)
  | 4 | 5 =>
      let (name, st) := freshName st "I"
      let (tps, st) := genTypeParams dd st (variance := true)
      let (ms, st) := genTypeMembers dd st
      let (hasExt, st) := rand st 3
      -- an interface may only extend a name, not a predefined type
      let (b, st) := genGenericTypeName st
      let (args, st) := genTypes dd st
      let ext := if hasExt == 0 then [(⟨.ident (nes b), args⟩ : MiniTsHeritage)] else []
      (.interface_ (nes name) tps ext ms, st)
  | 6 | 7 =>
      -- a function, and now and then its overload signature instead
      let (name, st) := freshName st "fn"
      let (tps, st) := genTypeParams dd st
      let (noBody, st) := rand st 5
      -- an overload signature carries no default value
      let (ps, st) := genParams dd false (noBody != 0) st
      let (r, st) := genType dd st
      let (body, st) := genStatements 2 dd st
      let (async, st) := rand st 5
      let (pred, st) := rand st 6
      -- a type predicate names a parameter of the function
      let ret : Option MiniTsType :=
        match pred, ps with
        | 0, .plain _ _ (.ident n) _ _ :: _ => some (.predicate false n (some r))
        | 1, .plain _ _ (.ident n) _ _ :: _ => some (.predicate true n none)
        | _, _ => if async == 0 then some (.ref (.ident (nes "Promise")) [r]) else some r
      (.funcDecl (async == 0) false (nes name) tps ps ret
        (if noBody == 0 then none else some body), st)
  | 8 | 9 =>
      let (name, st) := freshName st "C"
      let (tps, st) := genTypeParams dd st (variance := true)
      let (isAbstract, st) := rand st 4
      let (n, st) := genClassMemberCount st
      let (elems, st) := genClassElementsOf n dd (isAbstract == 0) st (decorated := true)
      let (hasExt, st) := rand st 3
      let (base, st) := genName st
      let (targs, st) := genTypes dd st
      let (hasImpl, st) := rand st 3
      -- a class may only implement a name, not a predefined type
      let (iface, st) := genGenericTypeName st
      let heritage : Option MiniClassHeritage :=
        if hasExt == 0 then some ⟨ident base, targs⟩ else none
      let impls : List MiniTsHeritage :=
        if hasImpl == 0 then [⟨.ident (nes iface), []⟩] else []
      let (decs, st) := genDecorators dd st
      (.classDecl decs (isAbstract == 0) (nes name) tps heritage impls elems, st)
  | 10 =>
      let (name, st) := freshName st "E"
      let (n, st) := rand st 4
      let (ms, st) := genEnumMembers (n + 1) dd st
      let (isConst, st) := rand st 4
      (.enum_ (isConst == 0) (nes name) ms, st)
  | 11 =>
      -- an ambient declaration, which carries no value
      let (k, st) := rand st 6
      match k with
      | 0 =>
          let (name, st) := freshName st "fn"
          let (ps, st) := genParams dd false false st
          let (r, st) := genType dd st
          (.declare_ (.funcDecl false false (nes name) [] ps (some r) none), st)
      | 1 =>
          let (name, st) := freshName st "value"
          let (t, st) := genType dd st
          (.declare_ (.decl .const ⟨⟨.ident (nes name), false, some t, none⟩, []⟩), st)
      | 2 =>
          let (name, st) := freshName st "T"
          let (t, st) := genType dd st
          (.declare_ (.typeAlias (nes name) [] t), st)
      | 3 =>
          let (name, st) := freshName st "C"
          let (n, st) := rand st 3
          let (isAbstract, st) := rand st 3
          let (ms, st) := genClassElementsOf n dd (isAbstract == 0) st
          (.declare_ (.classDecl [] (isAbstract == 0) (nes name) [] none [] ms), st)
      | 4 =>
          let (name, st) := freshName st "E"
          let (n, st) := rand st 3
          let (ms, st) := genEnumMembers (n + 1) dd st
          let (isConst, st) := rand st 3
          (.declare_ (.enum_ (isConst == 0) (nes name) ms), st)
      | _ =>
          let (name, st) := freshName st "N"
          let (t, st) := genType dd st
          let (inner, st) := freshName st "value"
          let (qualified, st) := rand st 3
          let inner2 := nes (name ++ "Inner")
          (.declare_ (.namespaceDecl false
            (.qualified (if qualified == 0 then ⟨nes name, [inner2]⟩ else ⟨nes name, []⟩))
            (some [.stmt (.decl .const ⟨⟨.ident (nes inner), false, some t, none⟩, []⟩)])), st)
  | 12 =>
      let (name, st) := freshName st "N"
      let (body, st) := genStatements 2 dd st
      let (isModule, st) := rand st 4
      let (qualified, st) := rand st 3
      let names : NEList NEString :=
        if qualified == 0 then ⟨nes name, [nes "Inner", nes "Deeper"]⟩ else ⟨nes name, []⟩
      (.namespaceDecl (isModule == 0) (.qualified names) (some (body.map .stmt)), st)
  | 13 =>
      let (e, st) := genExpr dd st
      let (body, st) := genStatements 2 dd st
      (.if_ e (.block body) none, st)
  | 14 =>
      let (name, st) := freshName st "item"
      let (e, st) := genExpr dd st
      let (body, st) := genStatements 2 dd st
      (.forOf false (.decl .const (.ident (nes name))) e (.block body), st)
  | 15 =>
      let (body, st) := genStatements 2 dd st
      let (name, st) := genName st
      -- TypeScript takes only `any` and `unknown` as the type of the
      -- binding of a `catch`
      let (k, st) := rand st 2
      let t : MiniTsType := .ref (.ident (nes (if k == 0 then "any" else "unknown"))) []
      let (catchBody, st) := genStatements 1 dd st
      (.try_ body (.catches ⟨⟨.ident (nes name), some t, none, catchBody⟩, []⟩ .none), st)
  | 16 =>
      let (name, st) := freshName st "value"
      let (t, st) := genType dd st
      (.decl .let_ ⟨⟨.ident (nes name), true, some t, none⟩, []⟩, st)
  | 17 =>
      -- a destructuring declaration with a type annotation
      let (a, st) := genName st
      let (b, st) := genName st
      let (t, st) := genType dd st
      let (e, st) := genExpr dd st
      (.decl .const ⟨⟨.object [⟨.ident (nes a), .ident (nes a)⟩,
                               ⟨.ident (nes b), .ident (nes b)⟩] none, false, some t, some e⟩,
        []⟩, st)
  | 18 =>
      let (e, st) := genExpr dd st
      let (body, st) := genStatements 2 dd st
      (.while_ e (.block body), st)
  | 19 =>
      let (name, st) := freshName st "value"
      let (t, st) := genType dd st
      let (e, st) := genExpr dd st
      let (n2, st) := freshName st "other"
      let (e2, st) := genExpr dd st
      (.decl .const ⟨⟨.ident (nes name), false, some t, some e⟩,
        [⟨.ident (nes n2), false, none, some e2⟩]⟩, st)
  | 20 =>
      let (e, st) := genExpr dd st
      let (body, st) := genStatements 1 dd st
      let (other, st) := genStatements 1 dd st
      (.switch e [.case e body, .default other], st)
  | _ =>
      let (name, st) := freshName st "fn"
      let (tps, st) := genTypeParams dd st
      let (ps, st) := genParams dd false false st
      let (r, st) := genType dd st
      let (e, st) := genExpr dd st
      (.decl .const ⟨⟨.ident (nes name), false,
        some (.fn tps ps r), some (.arrow false [] ps (some r) (.expr e))⟩, []⟩, st)

/-- How many members a class is written with. -/
partial def genClassMemberCount (st : St) : Nat × St :=
  let (n, st) := rand st 4
  (n + 1, st)

/-- A list of `n` members of an `enum`. -/
partial def genEnumMembers (n d : Nat) (st : St) : List MiniTsEnumMember × St :=
  match n with
  | 0 => ([], st)
  | k + 1 =>
      let (key, st) := genPropertyName st
      let (hasInit, st) := rand st 3
      let (e, st) := genEnumValue st
      let key := match key with
        | .computed _ => .ident (nes "member")
        | .number _ => .ident (nes "member")
        | k => k
      let (rest, st) := genEnumMembers k d st
      (⟨key, if hasInit == 0 then some e else none⟩ :: rest, st)

end

/-- One `import` or `export` declaration. -/
def genModuleItem (d : Nat) (st : St) : MiniModuleItem × St :=
  let (kind, st) := rand st 18
  let (mod, st) := genString st
  let mod := if mod == "" then "mod" else mod
  match kind with
  | 0 =>
      let (a, st) := genDeclTypeName st
      let (b, st) := genTypeName st
      let (isType, st) := rand st 3
      (.importDecl (.clause (MiniImportClause.mk! none none
        (some [⟨false, nes a, none⟩, ⟨isType == 0, nes b, some (nes "Alias")⟩]) (nes mod)
        [] (isType == 1))), st)
  | 1 =>
      let (a, st) := genName st
      (.importDecl (.clause (MiniImportClause.mk! (some (nes a)) none none (nes mod))), st)
  | 2 =>
      let (a, st) := genName st
      (.importDecl (.equals false (nes a) (.require mod)), st)
  | 3 =>
      let (a, st) := genDeclTypeName st
      let (b, st) := genDeclTypeName st
      (.importDecl (.equals false (nes a) (.entity (.qualified (.ident (nes b)) (nes "Inner")))), st)
  | 4 =>
      let (a, st) := genDeclTypeName st
      let (isType, st) := rand st 2
      (.exportDecl (.locals (isType == 0) [⟨false, nes a, none⟩]), st)
  | 5 =>
      let (a, st) := genTypeName st
      (.exportDecl (.fromClause true [⟨false, nes a, some (nes "Renamed")⟩] (nes mod) []), st)
  | 6 =>
      let (name, st) := freshName st "T"
      let (t, st) := genType d st
      (.exportDecl (.decl (.typeAlias (nes name) [] t)), st)
  | 7 =>
      let (name, st) := freshName st "I"
      let (ms, st) := genTypeMembers d st
      (.exportDecl (.decl (.interface_ (nes name) [] [] ms)), st)
  | 8 =>
      let (e, st) := genExpr d st
      (.exportDecl (.defaultExpr e), st)
  | 9 =>
      -- `export = expr;`, the TypeScript export assignment
      let (e, st) := genExpr d st
      (.exportDecl (.assign e), st)
  | 10 =>
      let (a, st) := genDeclTypeName st
      (.exportDecl (.asNamespace (nes a)), st)
  | 11 =>
      -- `export import A = B.Inner;`
      let (a, st) := genDeclTypeName st
      let (b, st) := genDeclTypeName st
      (.importDecl (.equals true (nes a) (.entity (.qualified (.ident (nes b)) (nes "Inner")))), st)
  | 12 =>
      -- an ambient module declaration, and `declare global`
      let (isGlobal, st) := rand st 2
      let (name, st) := freshName st "value"
      let (t, st) := genType d st
      let body : List MiniModuleItem :=
        [.stmt (.declare_ (.decl .const ⟨⟨.ident (nes name), false, some t, none⟩, []⟩))]
      (.stmt (.declare_ (.namespaceDecl false
        (if isGlobal == 0 then .global else .str mod) (some body))), st)
  | 14 =>
      -- `export * from "mod";`, and its type only form
      let (a, st) := genDeclTypeName st
      let (hasAlias, st) := rand st 2
      let (isType, st) := rand st 2
      (.exportDecl (.all (isType == 0) (if hasAlias == 0 then some (nes a) else none)
        (nes mod) []), st)
  | 15 =>
      -- `declare module "mod";`, an ambient module with no body
      (.stmt (.declare_ (.namespaceDecl true (.str mod) none)), st)
  | 16 =>
      -- `export default abstract class C { … }`
      let (name, st) := freshName st "C"
      let (n, st) := rand st 4
      let (ms, st) := genClassElementsOf n d true st
      (.exportDecl (.defaultDecl (.classDecl [] true (nes name) [] none [] ms)), st)
  | 17 =>
      -- `export default interface I { … }`
      let (name, st) := freshName st "I"
      let (ms, st) := genTypeMembers d st
      (.exportDecl (.defaultDecl (.interface_ (nes name) [] [] ms)), st)
  | _ =>
      let (name, st) := freshName st "value"
      let (t, st) := genType d st
      let (e, st) := genExpr d st
      (.exportDecl (.decl (.decl .const ⟨⟨.ident (nes name), false, some t, some e⟩, []⟩)), st)

/-- A random program: `n` top level items of depth at most `d`. -/
def genProgram (n d : Nat) (st : St) : MiniProgram × St :=
  let rec go (n : Nat) (st : St) : List MiniModuleItem × St :=
    match n with
    | 0 => ([], st)
    | k + 1 =>
        let (isModule, st) := rand st 8
        let (item, st) :=
          if isModule == 0 then genModuleItem d st
          else
            let (s, st) := genStatement d st
            (.stmt s, st)
        let (rest, st) := go k st
        (item :: rest, st)
  let (items, st) := go n st
  (⟨items⟩, st)

/-- `count` random programs, each of `stmts` items of depth at most
`depth`. -/
def programs (count depth stmts : Nat) (seed : UInt64) : List MiniProgram :=
  let rec go (n : Nat) (st : St) : List MiniProgram :=
    match n with
    | 0 => []
    | k + 1 =>
        let (prog, st) := genProgram stmts depth st
        prog :: go k st
  go count ⟨seed, 0⟩

end Language.TypeScript.MiniTsAST.Fuzz
