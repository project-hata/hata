
module Verification.Core.Setoid.Power.Intersection where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Power.Definition


module _ {A : 𝐒𝐭𝐝 𝑖} where

  module _
         {U : ⟨ A ⟩ -> Prop _} {{_ : isSubsetoid U}}
         {V : ⟨ A ⟩ -> Prop _} {{_ : isSubsetoid V}}
         where
    instance
      isSubsetoid:∩-𝒫 : isSubsetoid (U ∩ᵘ V)
      isSubsetoid:∩-𝒫 = record
        { transp-Subsetoid = λ a∼b (a∈U , b∈V) → (transp-Subsetoid a∼b a∈U) , (transp-Subsetoid a∼b b∈V)
        }

  _∩-𝒫-𝐒𝐭𝐝_ : 𝒫 A -> 𝒫 A -> 𝒫 A
  _∩-𝒫-𝐒𝐭𝐝_ U V = U ∩ V

  instance
    isSubsetoid:∅-𝒫-𝐒𝐭𝐝 : isSubsetoid {X = ⟨ A ⟩} ℧ᵘ
    isSubsetoid:∅-𝒫-𝐒𝐭𝐝 = record
      { transp-Subsetoid = λ a∼b a∈℧ → tt
      }

  ℧-𝒫-𝐒𝐭𝐝 : 𝒫 A
  ℧-𝒫-𝐒𝐭𝐝 = ℧


