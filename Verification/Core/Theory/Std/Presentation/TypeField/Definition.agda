
module Verification.Core.Theory.TypeField.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Theory.Presentation.Signature.SingleSorted.Definition

record isDirSet (X : Setoid ğ) : ğ° (ğ âº) where
  field Dir : ğ°â
open isDirSet public

DirSet : â ğ -> ğ° _
DirSet ğ = Setoid ğ :& isDirSet

-- record DirSet ğ : ğ° ğ where
--   â¨_â© : Setoid ğ
--   Dir : ğ°â
-- open DirSet public

record Tâ (X : DirSet ğ) (Ï : ğ°â) : ğ° (ğ âº) where
  inductive
  -- field map0 : â¨ X â© -> (Bool) +-ğ° ((â Var Ï) Ã-ğ° (Dir (of X) -> Tâ X Ï))



