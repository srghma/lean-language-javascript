/-
Port of the Haskell test module `ModuleParser`.
-/
import LanguageJavascriptTests.Utils

namespace Test.Language.Javascript

def testModuleParser : List Test :=
  -- as
  [ shouldBe "as" (testModule "as") "Right (JSAstModule [JSModuleStatementListItem (JSIdentifier 'as')])"
  -- import
  , shouldBe "import def from 'mod';" (testModule "import def from 'mod';") "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseDefault (JSIdentifier 'def'),JSFromClause ''mod''))])"
  , shouldBe "import def from \"mod\";" (testModule "import def from \"mod\";") "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseDefault (JSIdentifier 'def'),JSFromClause '\"mod\"'))])"
  , shouldBe "import * as thing from 'mod';" (testModule "import * as thing from 'mod';") "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseNameSpace (JSImportNameSpace (JSIdentifier 'thing')),JSFromClause ''mod''))])"
  , shouldBe "import { foo, bar, baz as quux } from 'mod';" (testModule "import { foo, bar, baz as quux } from 'mod';") "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseNameSpace (JSImportsNamed ((JSImportSpecifier (JSIdentifier 'foo'),JSImportSpecifier (JSIdentifier 'bar'),JSImportSpecifierAs (JSIdentifier 'baz',JSIdentifier 'quux')))),JSFromClause ''mod''))])"
  , shouldBe "import def, * as thing from 'mod';" (testModule "import def, * as thing from 'mod';") "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseDefaultNameSpace (JSIdentifier 'def',JSImportNameSpace (JSIdentifier 'thing')),JSFromClause ''mod''))])"
  , shouldBe "import def, { foo, bar, baz as quux } from 'mod';" (testModule "import def, { foo, bar, baz as quux } from 'mod';") "Right (JSAstModule [JSModuleImportDeclaration (JSImportDeclaration (JSImportClauseDefaultNamed (JSIdentifier 'def',JSImportsNamed ((JSImportSpecifier (JSIdentifier 'foo'),JSImportSpecifier (JSIdentifier 'bar'),JSImportSpecifierAs (JSIdentifier 'baz',JSIdentifier 'quux')))),JSFromClause ''mod''))])"
  -- export
  , shouldBe "export {}" (testModule "export {}") "Right (JSAstModule [JSModuleExportDeclaration (JSExportLocals (JSExportClause (())))])"
  , shouldBe "export {};" (testModule "export {};") "Right (JSAstModule [JSModuleExportDeclaration (JSExportLocals (JSExportClause (())))])"
  , shouldBe "export const a = 1;" (testModule "export const a = 1;") "Right (JSAstModule [JSModuleExportDeclaration (JSExport (JSConstant (JSVarInitExpression (JSIdentifier 'a') [JSDecimal '1'])))])"
  , shouldBe "export function f() {};" (testModule "export function f() {};") "Right (JSAstModule [JSModuleExportDeclaration (JSExport (JSFunction 'f' () (JSBlock [])))])"
  , shouldBe "export { a };" (testModule "export { a };") "Right (JSAstModule [JSModuleExportDeclaration (JSExportLocals (JSExportClause ((JSExportSpecifier (JSIdentifier 'a')))))])"
  , shouldBe "export { a as b };" (testModule "export { a as b };") "Right (JSAstModule [JSModuleExportDeclaration (JSExportLocals (JSExportClause ((JSExportSpecifierAs (JSIdentifier 'a',JSIdentifier 'b')))))])"
  , shouldBe "export {} from 'mod'" (testModule "export {} from 'mod'") "Right (JSAstModule [JSModuleExportDeclaration (JSExportFrom (JSExportClause (()),JSFromClause ''mod''))])"
  ]

#guard allPass testModuleParser

end Test.Language.Javascript
