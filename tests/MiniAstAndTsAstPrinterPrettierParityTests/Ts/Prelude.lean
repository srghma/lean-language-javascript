import MiniTsAST

/-!
# Helpers for the TypeScript corpus

Short names for building the sample programs of `Tests/Ts/Corpus*.lean`.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A non-empty string, for building samples. -/
def nes (x : String) : NEString := NEString.ofString! x

/-- An identifier expression. -/
def v (x : String) : MiniExpr := .ident (nes x)

/-- An identifier pattern. -/
def p (x : String) : MiniPattern := .ident (nes x)

/-- A plain parameter with no type. -/
def par (x : String) : MiniParam := .plain [] {} (p x) false none

/-- A parameter with a type annotation. -/
def parT (x : String) (ty : MiniTsType) : MiniParam := .plain [] {} (p x) false (some ty)

/-- An optional parameter, `x?: T`. -/
def parOpt (x : String) (ty : MiniTsType) : MiniParam := .plain [] {} (p x) true (some ty)

/-- A rest parameter, `...x: T`. -/
def parRest (x : String) (ty : Option MiniTsType := none) : MiniParam := .rest [] (p x) ty

/-- A parameter written with decorators, `@Dec() x: T`. -/
def parDec (decorators : List MiniExpr) (x : String) (ty : Option MiniTsType := none) :
    MiniParam :=
  .plain decorators {} (p x) false ty

/-- A numeric literal. -/
def num (k : Nat) : MiniExpr := .number (JSNumber.ofNat k)

/-- A statement item of a program. -/
def st (x : MiniStatement) : MiniModuleItem := .stmt x

/-- An expression statement. -/
def es (e : MiniExpr) : MiniModuleItem := .stmt (.expr e)

/-- A type read by name, with no type arguments. -/
def ty (x : String) : MiniTsType := .ref (.ident (nes x)) []

/-- A type read by name, with type arguments. -/
def tyA (x : String) (args : List MiniTsType) : MiniTsType := .ref (.ident (nes x)) args

/-- A declarator with a type annotation and an initialiser. -/
def declT (x : String) (type : Option MiniTsType) (init : Option MiniExpr) : MiniDeclarator :=
  ⟨p x, false, type, init⟩

/-- A `const x: T = e;` statement. -/
def constDecl (x : String) (type : Option MiniTsType) (e : MiniExpr) : MiniStatement :=
  .decl .const ⟨declT x type (some e), []⟩

/-- A `let x: T;` statement. -/
def letDecl (x : String) (type : Option MiniTsType) : MiniStatement :=
  .decl .let_ ⟨declT x type none, []⟩

/-- A call of `f` on `args`. -/
def call (f : String) (args : List MiniExpr) : MiniExpr := .call (v f) [] args

/-- A type parameter with no constraint and no default. -/
def tp (x : String) : MiniTsTypeParam := ⟨false, none, nes x, none, none⟩

/-- A type parameter with a constraint. -/
def tpC (x : String) (c : MiniTsType) : MiniTsTypeParam := ⟨false, none, nes x, some c, none⟩

/-- A property of an object type, `a: T`. -/
def prop (x : String) (type : MiniTsType) : MiniTsTypeMember :=
  .property false (.ident (nes x)) false (some type)

/-- An entry of an `extends` or `implements` clause. -/
def her (x : String) (args : List MiniTsType := []) : MiniTsHeritage := ⟨.ident (nes x), args⟩

/-- A long identifier, to force lines to break. -/
def longName (k : Nat) : String :=
  match k with
  | 0 => "aLongIdentifierNameNumberZero"
  | 1 => "aLongIdentifierNameNumberOne"
  | 2 => "aLongIdentifierNameNumberTwo"
  | 3 => "aLongIdentifierNameNumberThree"
  | _ => "aLongIdentifierNameNumberFour"

/-- A long type name, to force lines to break. -/
def longType (k : Nat) : String :=
  match k with
  | 0 => "ALongTypeNameNumberZero"
  | 1 => "ALongTypeNameNumberOne"
  | 2 => "ALongTypeNameNumberTwo"
  | 3 => "ALongTypeNameNumberThree"
  | _ => "ALongTypeNameNumberFour"

/-- One named sample. -/
structure Sample where
  /-- The name of the sample. -/
  name : String
  /-- The program. -/
  prog : MiniProgram
  /-- The interpreter directive the file starts with, if it has one. -/
  interpreter : Option String := none

end Language.TypeScript.MiniTsAST.Corpus
