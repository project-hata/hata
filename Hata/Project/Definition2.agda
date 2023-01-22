
--
-- We introduce file (2) for definitions because currently
-- in file 1 the def for isProjectType contains some experimental
-- configurations which we don't need for treesitter.
--
module Hata.Project.Definition2 where

open import Hata.Conventions
open import Hata.Base.HIO.Definition
open import Hata.Reflection.Definition
open import Hata.Abstract.Path.Definition

data FilePattern : 𝒰₀ where
  exact : Text -> FilePattern

FileContents = List (((Rel , File)-Path) × FilePattern)

writeFileContents : (Abs , Dir)-Path -> FileContents -> HIO ⊤
writeFileContents _ [] = return-HIO tt
writeFileContents root ((path , exact content) ∷ xs) =
  do
    writeFile (toFilePath $ concat root path) content
    writeFileContents root xs
    return-HIO tt

------------------------------------------
-- project in general

record isSimpleProjectType (A : 𝒰₀) : 𝒰₂ where
  field ContentType : 𝒰₁
  field generate : A -> ContentType -> FileContents
  field build : HIO ⊤

open isSimpleProjectType public

data Projects : 𝒰₂ where
  _:=_ : {A : 𝒰₀} -> (a : A) -> {{PP : isSimpleProjectType A}} -> ContentType PP -> Projects

generateProjects : (Abs , Dir)-Path -> Projects -> HIO ⊤
generateProjects root (_:=_ a {{PP}} content) =
  do
    writeFileContents root (generate PP a content)
    let path = toFilePath $ concat root (:: / "grammar" ∶ "js")
    runCommand-HIO "tree-sitter" ("generate" ∷ path ∷ [])
    return-HIO tt

------------------------------------------
-- Treesitter projects

open import Hata.Extern.TreeSitter.Syntax.Definition as TreeSitter
open import Hata.Extern.TreeSitter.Generate as TreeSitter

record TreesitterCargo : 𝒰₀ where
  constructor newTreesitterCargo
  field languageName : Text

open TreesitterCargo


instance
  isSimpleProjectType:TreesitterCargo : isSimpleProjectType TreesitterCargo
  isSimpleProjectType:TreesitterCargo = record
    { ContentType = TreeSitter.Grammar
    ; generate = λ cfg g
                -> (:: / "grammar" ∶ "js" , exact (TreeSitter.generate (languageName cfg) g)) ∷ []
    ; build = {!!}
    }



