
module Verification.Core.Setoid.Power.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category


-- record PowerSetoid (A : ๐๐ญ๐ ๐) : ๐ฐ (๐ โบ) where
--   field El : Subsetoid A

PowerSetoid = Subsetoid

module _ (A : ๐๐ญ๐ ๐) where
  macro
    ๐ซ-๐๐ญ๐ = #structureOn (PowerSetoid A)

instance
  hasPower:๐๐ญ๐ : hasPower (๐๐ญ๐ ๐) (๐ฐ (fst ๐ โบ โ snd ๐))
  hasPower:๐๐ญ๐ = record { ๐ซแต = Subsetoid }




