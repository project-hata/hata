
module Verification.Workspace.Probability.ChengSpace.Definition where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Imports
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Definition
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.Category
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.HasCoproducts
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.HasProducts

module _ {X : 𝐒𝐭𝐝 𝑖} where
  infix 120 ⫞_
  ⫞_ : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (𝒫 X) -> 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (𝒫 X)
  ⫞_ (a , b because f) = b , a because (incl λ (a , b) → ⟨ f ⟩ (b , a))

  private
    testlem1 : ∀{a} -> ⫞ ⫞ a ≣ a
    testlem1 = refl-≣

    testlem2 : ∀{U V : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (𝒫 X)} -> ⫞ (U ⊓ V) ≅ (⫞ U) ⊔ (⫞ V)
    testlem2 {U} {V} = f since record { inverse-◆ = g ; inv-r-◆ = tt ; inv-l-◆ = tt }
      where
        f : ⫞ (U ⊓ V) ⟶ (⫞ U) ⊔ (⫞ V)
        f = id , id

        g : (⫞ U) ⊔ (⫞ V) ⟶ ⫞ (U ⊓ V)
        g = id , id


record isChengSpace (X : 𝐒𝐭𝐝 𝑖) : 𝒰 (𝑖 ⁺ ⁺) where
  field isComplementedPair : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (𝒫 X) -> 𝒰 𝑖
  field closed-⊥ : isComplementedPair ⊥
  field closed-⫞ : ∀ (P : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (𝒫 X)) -> isComplementedPair P -> isComplementedPair (⫞ P)
  field closed-⨆ : (P : ℕ -> 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (𝒫 X)) -> (∀ i -> isComplementedPair (P i)) -> isComplementedPair (⨆ᵢ P)

  Compl : 𝒰 _
  Compl = ∑ isComplementedPair

open isChengSpace {{...}} hiding (Compl) public
open isChengSpace using (Compl) public

module _ (X : 𝐒𝐭𝐝 𝑖) where
  isChengSpace:byDiscrete : isChengSpace X
  isChengSpace:byDiscrete = record
                              { isComplementedPair = λ x → ⊤-𝒰
                              ; closed-⊥ = tt
                              ; closed-⫞ = λ P x → tt
                              ; closed-⨆ = λ P x → tt
                              }

module _ 𝑖 where
  ChengSpace = 𝐒𝐭𝐝 𝑖 :& isChengSpace

module _ {X : ChengSpace 𝑖} where
  isFull : 𝒫 (↳ X) -> 𝒰 _
  isFull S = ∑ λ (P : Compl (of X)) -> fst (fst P) ⊔ snd (fst P) ⟶ S


open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Ring.Domain
open import Verification.Core.Order.Linearorder

record Measure (R : OrderedRing 𝑗) (X : ChengSpace 𝑖) : 𝒰 (𝑖 ⁺ ⁺ ､ 𝑗) where
  field μ : Compl (of X) -> ⟨ R ⟩
  field M1 : ∀{P : Compl (of X)} -> isFull {X = X} (snd (fst P)) -> μ P ∼ ◌
  field M2 : ∀{P Q : Compl (of X)} -> μ P ⋆ μ Q ∼ μ (fst P ⊓ fst Q , {!!}) ⋆ μ (fst P ⊔ fst Q , {!!})

open Measure {{...}} public


----------------------------------------------------------
-- for security, we have

module _
      (R : OrderedRing 𝑗)
      (M : ChengSpace 𝑖)
      {{MM : Measure R M}}
      where

  postulate instance
    _ : isSetoid {fst 𝑖} ⟨ M ⟩

  singleMsg : ⟨ M ⟩ -> Compl (of M)
  singleMsg m = (((λ m' -> ∣ m' ∼ m ∣) since {!!}) , {!!} because {!!}) , {!!}

  attacker : (m : ⟨ M ⟩) -> μ (singleMsg m) ∼ {!!}
  attacker = {!!}






