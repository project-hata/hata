
module Hata.Language.PP.Definition where

open import Hata.Conventions
open import Hata.Reflection.Definition
open import Verification.Conventions.Meta.Term hiding (_×_)
open import Hata.Program.HataCmd.Common

record Signature : 𝒰₁ where
  field
    Filetype : 𝒰₀
    File : Filetype -> 𝒰₀

open Signature public

data ♭ {@♭ l : Level} (@♭ A : 𝒰 l) : 𝒰 l where
  con : (@♭ x : A) → ♭ A

module _ (@♭ Σ : Signature) where
  FILETYPE = ♭ (Filetype Σ)

  FILE : FILETYPE -> 𝒰₀
  FILE (con ty) = ♭ (File Σ ty)

module ExamplePP where

  data EFiletype : 𝒰₀ where
    YamlSingleString Empty None : EFiletype

  EFile : EFiletype -> 𝒰₀
  EFile YamlSingleString = Text × Text
  EFile Empty = ⊤
  EFile None = ⊥

  Sig : Signature
  Sig = record { Filetype = EFiletype ; File = EFile }

open ExamplePP

S = ExamplePP.Sig


Y : FILE S (con Empty)
Y = con tt


-- X = PP S





