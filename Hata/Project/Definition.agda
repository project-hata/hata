
module Hata.Project.Definition where

open import Hata.Conventions
open import Hata.Reflection.Definition
open import Hata.Abstract.Path.Definition


------------------------------------------

record RustProjectDefinition : 𝒰₀ where

data ProjectDefinition : 𝒰₀ where
  rust : RustProjectDefinition -> ProjectDefinition

a = #reflect ProjectDefinition

-- _ = #do
--   a <- #reflect ProjectDefinition
--   let p = HaskellStackProject (∷ / "Common" / )
--   #generate



record HaskellStackProject : 𝒰₀ where
  field root : (Abs , Dir)-Path

record HaskellAgdaMapping (TM : TypeMap) : 𝒰₀ where

instance
  isProjectType:HaskellStackProject : isProjectType HaskellStackProject
  isProjectType:HaskellStackProject = record
                                        { SingleFile = {!!}
                                        ; IdentMapping = HaskellAgdaMapping
                                        ; generateProjectFile = {!!}
                                        ; projectFilePath = {!!}
                                        }


------------------------------------------
-- defining projects

HSI : HaskellStackProject
HSI = record { root = # sln-root / "Common" / "HataSystemInterface" }

HaskellTypeMap : TypeMap
HaskellTypeMap =
  ((Abs , Dir)-Path , FilePath , "FilePath")
  ∷ {!!}

-- P = # do
--   a <-

open import Verification.Conventions.Meta.Term

makeAgdaBindings : ∀{TM} -> HaskellAgdaMapping TM -> TC 𝟙-𝒰
makeAgdaBindings mapping = return tt


_ = # do
  let RP = #reflect RustProjectDefinition
  let P = #reflect ProjectDefinition
  mapping <- generateFile HaskellTypeMap HSI {!!} (:: / "HataSystemInterface" / "Project")

  makeAgdaBindings mapping



------------------------------------------
-- NOTES
--
-- 1. Generating a haskell file from an agda definition
--    requires that there is a mapping agda-type -> haskell-type
-- 2. Generating the resulting agda bindings further requires that
--    there is native agda type for the haskell types, and that
--    there is an iso between the good agda type and the raw agda type.
--
--


