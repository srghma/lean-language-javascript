/-
Port of the Haskell test module `ModuleParser`.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.AST
import LanguageJavascript.ShowStripped

namespace LanguageJavascriptTests.ModuleParser

open Spec
open Spec.Assert
open Language.JavaScript.Parser
open Language.JavaScript.Parser.AST

def escapeLabel (s : String) : String :=
  s.replace "\n" "\\n" |>.replace "\r" "\\r"

def showStrippedMaybe : Except String JSAST → String
  | .ok ast => "Right (" ++ showStripped ast ++ ")"
  | .error e => "Left (\"" ++ e ++ "\")"

def testModule (str : String) : String := showStrippedMaybe (parseModule str)

def moduleCases : List (String × String) :=
  -- as
  [ ("as", "Right (JSAstModule [JSModuleStatementListItem (JSIdentifier 'as')])")
  -- import
  , ("import def from 'mod';", "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseDefault (JSIdentifier 'def'),JSFromClause ''mod''))])")
  , ("import def from \"mod\";", "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseDefault (JSIdentifier 'def'),JSFromClause '\"mod\"'))])")
  , ("import * as thing from 'mod';", "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseNameSpace (JSImportNameSpace (JSIdentifier 'thing')),JSFromClause ''mod''))])")
  , ("import { foo, bar, baz as quux } from 'mod';", "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseNameSpace (JSImportsNamed ((JSImportSpecifier (JSIdentifier 'foo'),JSImportSpecifier (JSIdentifier 'bar'),JSImportSpecifierAs (JSIdentifier 'baz',JSIdentifier 'quux')))),JSFromClause ''mod''))])")
  , ("import def, * as thing from 'mod';", "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseDefaultNameSpace (JSIdentifier 'def',JSImportNameSpace (JSIdentifier 'thing')),JSFromClause ''mod''))])")
  , ("import def, { foo, bar, baz as quux } from 'mod';", "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseDefaultNamed (JSIdentifier 'def',JSImportsNamed ((JSImportSpecifier (JSIdentifier 'foo'),JSImportSpecifier (JSIdentifier 'bar'),JSImportSpecifierAs (JSIdentifier 'baz',JSIdentifier 'quux')))),JSFromClause ''mod''))])")
  -- export
  , ("export {}", "Right (JSAstModule [JSModuleExportDeclaration (JSExportLocals (JSExportClause (())))])")
  , ("export {};", "Right (JSAstModule [JSModuleExportDeclaration (JSExportLocals (JSExportClause (())))])")
  , ("export const a = 1;", "Right (JSAstModule [JSModuleExportDeclaration (JSExport (JSConstant (JSVarInitExpression (JSIdentifier 'a') [JSDecimal '1'])))])")
  , ("export function f() {};", "Right (JSAstModule [JSModuleExportDeclaration (JSExport (JSFunction 'f' () (JSBlock [])))])")
  , ("export { a };", "Right (JSAstModule [JSModuleExportDeclaration (JSExportLocals (JSExportClause ((JSExportSpecifier (JSIdentifier 'a')))))])")
  , ("export { a as b };", "Right (JSAstModule [JSModuleExportDeclaration (JSExportLocals (JSExportClause ((JSExportSpecifierAs (JSIdentifier 'a',JSIdentifier 'b')))))])")
  , ("export {} from 'mod'", "Right (JSAstModule [JSModuleExportDeclaration (JSExportFrom (JSExportClause (()),JSFromClause ''mod''))])")
  ]

def spec : Spec := do
  describe "Module parser" do
    let mut seen : Std.HashSet String := {}
    for (input, expected) in moduleCases do
      let rawName := escapeLabel input
      let name := if seen.contains rawName then s!"{rawName} (duplicate)" else rawName
      seen := seen.insert rawName
      it name do
        shouldEqual (testModule input) expected

end LanguageJavascriptTests.ModuleParser
