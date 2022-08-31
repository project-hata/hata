
module Verification.Application.CompGen.Theory.Tool.Definition where

open import Verification.Conventions hiding (Path)

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural

record FilePath : 𝒰₀ where
  constructor _∶_#_
  field name : String
  field ending : String
  field directories : List String

_∶⟳_ : FilePath -> String -> FilePath
_∶⟳_ x = {!!}

DirPath = List String



record Space : 𝒰₀ where
  constructor space
  field paths : List DirPath

open Space public

-- Space = List String

record State (s : Space) : 𝒰₀ where
  constructor state
  field files : ∀{p} -> paths s ∍♮ p -> FilePath -> String

record Tool (s : Space) : 𝒰₁ where
  constructor tool
  field action : (State s -> 𝒰₀) -> (State s -> 𝒰₀)


postulate
  isCSource : String -> 𝒰₀

--------------------------------------------
-- examples

gccSpace : DirPath -> Space
gccSpace root = space (
  ("src" ∷ root)
  ∷ ("bin" ∷ root)
  ∷ [])

gcc : (root : DirPath) -> Tool (gccSpace root)
gcc root = tool a
  where
    a : (State (gccSpace root) -> 𝒰₀) -> (State (gccSpace root) -> 𝒰₀)
    a post (state files) = isCSource (files incl ("main" ∶ "c" # []))



