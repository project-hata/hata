
module Verification.Core.Setoid.Power.Intersection where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Power.Definition


----------------------------------------------------------
-- Finitary intersections
----------------------------------------------------------

module _ {A : 𝐒𝐭𝐝 𝑖} where

  module _
         {U : ⟨ A ⟩ -> Prop _} {{_ : isSubsetoid U}}
         {V : ⟨ A ⟩ -> Prop _} {{_ : isSubsetoid V}}
         where
    instance
      isSubsetoid:∩-𝒫-𝐒𝐭𝐝 : isSubsetoid (U ∩ᵘ V)
      isSubsetoid:∩-𝒫-𝐒𝐭𝐝 = record
        { transp-∼ = λ a∼b (a∈U , b∈V) → (transp-∼ a∼b a∈U) , (transp-∼ a∼b b∈V)
        }

  _∩-𝒫-𝐒𝐭𝐝_ : 𝒫 A -> 𝒫 A -> 𝒫 A
  _∩-𝒫-𝐒𝐭𝐝_ U V = U ∩ V



  instance
    isSubsetoid:℧-𝒫-𝐒𝐭𝐝 : isSubsetoid {X = ⟨ A ⟩} ℧ᵘ
    isSubsetoid:℧-𝒫-𝐒𝐭𝐝 = record
      { transp-∼ = λ a∼b a∈℧ → tt
      }

  ℧-𝒫-𝐒𝐭𝐝 : 𝒫 A
  ℧-𝒫-𝐒𝐭𝐝 = ℧

----------------------------------------------------------
-- Indexed intersections
----------------------------------------------------------

module _ {A : 𝐒𝐭𝐝 𝑖} {I : 𝒰₀} where
  -- module _ {Uᵢ : I -> ⟨ A ⟩ -> Prop _} {{_ : ∀{i} -> isSubsetoid (Uᵢ i)}} where
  module _ (Uᵢ : I -> 𝒫 A) where
    instance
      isSubsetoid:⋂-𝒫-𝐒𝐭𝐝 : isSubsetoid (⋂ᵘ Uᵢ)
      isSubsetoid:⋂-𝒫-𝐒𝐭𝐝 = record
        { transp-∼ = λ a∼b aᵢ∈U i → transp-∼ {{_}} {{of Uᵢ i}} a∼b (aᵢ∈U i)
        }

  ⋂-𝒫-𝐒𝐭𝐝 : (Uᵢ : I -> 𝒫 A) -> 𝒫 A
  ⋂-𝒫-𝐒𝐭𝐝 Uᵢ = ⋂ᵘ Uᵢ since isSubsetoid:⋂-𝒫-𝐒𝐭𝐝 Uᵢ


