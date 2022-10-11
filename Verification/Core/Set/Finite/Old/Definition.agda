

module Verification.Core.Set.Finite.Old.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.HeytingAlgebra
open import Verification.Core.Set.Finite.Old.Reach


record isFinite (A : 𝒰 𝑖 :& isDiscrete') : 𝒰 (𝑖 ⁺) where
  field reach : ∀ (p q : 𝒫-Dec ⟨ A ⟩) -> (s : ⟨ p ⟩ ≤ ⟨ q ⟩) -> Reachable ⟨ p ⟩ ⟨ q ⟩ s
open isFinite {{...}} public

Finite : (𝑖 : 𝔏) -> 𝒰 _
Finite 𝑖 = 𝒰 𝑖 :& isDiscrete' :& isFinite

module _ {A B : 𝒰 _} {{_ : Finite 𝑖 on A}} {{_ : Finite 𝑖 on B}} where
  instance
    isFinite:+ : isFinite (′ A ∨ B ′)
    isFinite.reach isFinite:+ P Q a =
      let P₀ = reach (P ∣ left) (Q ∣ left) (monotone a)

          P₀' : Reachable (⟨ P ⟩ ∧ Im left) (⟨ Q ⟩ ∧ Im left) _
          P₀' = pb-Reach left ⟨ P ⟩ ⟨ Q ⟩ P₀

          P₁ = reach (P ∣ right) (Q ∣ right) (monotone a)

          P₁' : Reachable (⟨ P ⟩ ∧ Im right) (⟨ Q ⟩ ∧ Im right) _
          P₁' = pb-Reach right ⟨ P ⟩ ⟨ Q ⟩ P₁

      in {!!}

-- size : Finite 𝑖 -> ℕ
-- size A = f ⟨ A ⟩ (⊥ , {!!}) {!!} {!!} (reach _ _ _)
--   where f : ∀(A : 𝒰 𝑖) (P Q : 𝒫-Dec A) -> (R : ⟨ P ⟩ ≤ ⟨ Q ⟩) -> Reachable R -> ℕ
--         f A P (.(⟨ P ⟩) , Proof₁) (incl .(isPreorder.reflexive isPreorder:Prop)) refl-Reach = 0
--         f A P Q R (step-Reach .R x Y r) = suc (f _ _ _ _ r)


