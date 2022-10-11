
module Verification.Core.Setoid.Power.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category


-- record PowerSetoid (A : 𝐒𝐭𝐝 𝑖) : 𝒰 (𝑖 ⁺) where
--   field El : Subsetoid A

PowerSetoid = Subsetoid

module _ (A : 𝐒𝐭𝐝 𝑖) where
  macro
    𝒫-𝐒𝐭𝐝 = #structureOn (PowerSetoid A)

instance
  hasPower:𝐒𝐭𝐝 : hasPower (𝐒𝐭𝐝 𝑖) (𝒰 (fst 𝑖 ⁺ ⊔ snd 𝑖))
  hasPower:𝐒𝐭𝐝 = record { 𝒫ᵘ = Subsetoid }




