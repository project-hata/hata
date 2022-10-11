
module Verification.Workspace.Probability.ChengSpace.DisjointPair.Definition where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Imports

-- Mostly following https://ncatlab.org/nlab/show/Cheng+space

-- CDL = Complete distributive lattice


record isCompleteLatticeCategory (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⁺) where
  field {{hasIndexedProducts-CDL}}   : hasAllIndexedProducts ℓ₀ 𝒞
  field {{hasProducts-CDL}}          : hasFiniteProducts 𝒞
  field {{hasIndexedCoproducts-CDL}} : hasAllIndexedCoproducts ℓ₀ 𝒞
  field {{hasCoproducts-CDL}}        : hasFiniteCoproducts 𝒞

open isCompleteLatticeCategory {{...}} public

module _ 𝑖 where
  CompleteLatticeCategory = Category 𝑖 :& isCompleteLatticeCategory

record isDispairDistributive (𝒞 : CompleteLatticeCategory 𝑖) : 𝒰 (𝑖 ⁺) where
  -- field codist : ∀{a b c : ⟨ 𝒞 ⟩} -> a ⊔ (b ⊓ c) ≅ (a ⊔ b) ⊓ (a ⊔ c)
  field dist : ∀{a b c : ⟨ 𝒞 ⟩} -> a ⊓ (b ⊔ c) ≅ a ⊓ b ⊔ a ⊓ c
  field distᵢ : ∀{I : 𝒰₀} {a : ⟨ 𝒞 ⟩} {b : I -> ⟨ 𝒞 ⟩} -> a ⊓ (⨆ᵢ b) ≅ ⨆[ i ] a ⊓ b i

open isDispairDistributive {{...}} public

module _ 𝑖 where
  DCLC = Category 𝑖 :& isCompleteLatticeCategory :& isDispairDistributive

module _ {A : 𝐒𝐭𝐝 𝑖} where
  instance
    isCompleteLatticeCategory:𝒫-𝐒𝐭𝐝 : isCompleteLatticeCategory (𝒫 A)
    isCompleteLatticeCategory:𝒫-𝐒𝐭𝐝 = record {}

  instance
    isDispairDistributive:𝒫-𝐒𝐭𝐝 : isDispairDistributive (𝒫 A)
    isDispairDistributive:𝒫-𝐒𝐭𝐝 = record { dist = lem1 ; distᵢ = lem3 }


module _ (𝒞 : DCLC 𝑖) where
  record DisjointPair : 𝒰 (𝑖 ⁺) where
    constructor _,_because_
    field fst : ⟨ 𝒞 ⟩
    field snd : ⟨ 𝒞 ⟩
    field dis : fst ⊓ snd ⟶ ⊥

  open DisjointPair public

  macro 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = #structureOn DisjointPair




