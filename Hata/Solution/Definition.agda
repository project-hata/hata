
module Hata.Solution.Definition where

open import Hata.Conventions
open import Hata.Reflection.Definition
open import Hata.Abstract.Path.Definition


------------------------------------------
-- components

record TypeProvider : 𝒰₀ where

-- record isComponentType (C : 𝒰₀) : 𝒰₀ where

record ComponentType : 𝒰₀ where
  -- field : mapping abstract modules to filesystem paths
  -- field : supported HataTypes

record isHataType (T : 𝒰₀) : 𝒰₀ where

HataType = _ :& isHataType

record Component (t : ComponentType) : 𝒰₁ where
  field types : List HataType
  -- field interfaces : List (Member types × Member types)
  -- field implementations : for each τ ∈ types say where it is to be generated
  -- field impls2          : for each f ∈ interfaces, say where it is to be generated

record Project : 𝒰₁ where
  field components : List (∑ Component)
  -- field links : for each c , d ∈ component, give a list of interfaces of c and for each of them
  --               a location in d where the call should be generated

  -- note, components can be merged in different ways: there are executable boundaries.
  -- thus, links can be either FFI or StdOutIn or Network



------------------------------------------
-- NOTES
--
-- The general idea is "single source of truth". Definitions of interfaces
-- are all done in Agda, the resulting definitions for other languages are
-- generated from here.
--
-- 1. CLI interfaces are also defined as data types.
--   example:

data HataCommand : 𝒰₀ where
  echo : Text -> HataCommand
  writeFile : Text -> FilePath -> HataCommand
  -- ...

open import Hata.Base.IO.Definition

postulate
  runCommand : HataCommand -> IO Text



