
module Verification.Core.Setoid.Power.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category


record PowerSetoid (A : 𝐒𝐭𝐝 𝑖) : 𝒰 (𝑖 ⁺) where
  field El : Subsetoid A

module _ (A : 𝐒𝐭𝐝 𝑖) where
  macro
    𝒫-𝐒𝐭𝐝 = #structureOn (PowerSetoid A)


module _ {A : 𝐒𝐭𝐝 𝑖} where

  data _∼-𝒫-𝐒𝐭𝐝_ : (a b : 𝒫-𝐒𝐭𝐝 A) -> 𝒰 (𝑖 ⁺) where
    -- incl : ∀


  instance
    isSetoid:PowerSetoid : isSetoid (𝒫-𝐒𝐭𝐝 A)
    isSetoid:PowerSetoid = isSetoid:byDef _∼-𝒫-𝐒𝐭𝐝_ {!!} {!!} {!!}

-- 𝒫-𝐒𝐭𝐝 : ∀ 𝑗 -> 𝐒𝐭𝐝 𝑖 -> 𝐒𝐭𝐝 _
-- 𝒫-𝐒𝐭𝐝 𝑗 A = {!𝒫 ⟨ !}



