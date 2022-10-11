
module Verification.Core.Algebra.MonoidAction.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Algebra.Monoid.Definition


record isActed {𝑗 𝑖} (M : Monoid 𝑖) (A : Setoid 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field _↷_ : ⟨ M ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
        assoc-l-↷ : ∀{m n a} -> (m ⋆ n) ↷ a ∼ m ↷ (n ↷ a)
        _≀↷≀_ : ∀{a b} {m n} -> (a ∼ b) -> (m ∼ n) -> (a ↷ m) ∼ (b ↷ n)

  infixr 30 _↷_
open isActed {{...}} public

Acted : (M : Monoid 𝑖) -> ∀ 𝑗 -> _
Acted M 𝑗 = _ :& isActed {𝑗} M

module _ {M : Monoid 𝑖} where

  record isTransitiveActed (A : Acted M 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
    field _⇜_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ M ⟩
    field trans-↷ : ∀{a b} -> (b ⇜ a) ↷ a ∼ b

  record isFreeActed (A : Acted M 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
    field free-↷ : ∀{m : ⟨ M ⟩} {a : ⟨ A ⟩} -> m ↷ a ∼ a -> m ∼ ◌






module Old where
  module _ {M : 𝒰 _} {A : 𝒰 _} {{_ : Monoid 𝑖 on M}} {{_ : Setoid 𝑗 on A}} {{_ : isActed ′ M ′ ′ A ′}} where
    -- _≀↷≀'_ : ∀{a b : ⟨ M ⟩} {m n : ⟨ A ⟩} -> (a ∼ b) -> (m ∼ n) -> (a ↷ m) ∼ (b ↷ n)
    _≀↷≀'_ : ∀{a b : M} {m n : A} -> (a ∼ b) -> (m ∼ n) -> (a ↷ m) ∼ (b ↷ n)
    _≀↷≀'_ = {!!}


  record hasDistributiveActionₗ (M : Monoid 𝑖) (A : Setoid 𝑗 :& (isMonoid :, isActed M)) : 𝒰 (𝑖 ､ 𝑗) where
    private
      ◌A : ⟨ A ⟩
      ◌A = ◌
    field absorb-r-↷ : ∀{m : ⟨ M ⟩} -> m ↷ ◌A ∼ ◌A
    field distr-l-↷ : ∀{m : ⟨ M ⟩} {a b : ⟨ A ⟩} -> m ↷ (a ⋆ b) ∼ ((m ↷ a) ⋆ (m ↷ b))

  open hasDistributiveActionₗ {{...}} public



