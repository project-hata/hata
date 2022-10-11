
module Verification.Core.Data.Real.Cauchy.Sequence where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Int.Definition

open import Verification.Core.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Algebra.Ring.Localization
open import Verification.Core.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Core.Algebra.Ring.Localization.Instance.OrderedRing
open import Verification.Core.Algebra.Field.Definition
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder
open import Verification.Core.Data.Rational.Definition
open import Verification.Core.Data.Rational.Inclusion

open AbelianMonoidNotation


record Sequence (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field ix : ℕ -> A

open Sequence public

module _ {A : 𝒰 𝑖} where
  instance
    Index-Notation:Sequence : Index-Notation (Sequence A) (const ℕ) (λ _ -> ⊤-𝒰 {ℓ₀}) (const A)
    Index-Notation:Sequence = record { _⌄_ = λ x i → ix x i }

  instance
    hasU:Sequence : hasU (Sequence A) _ _
    hasU:Sequence = hasU:Base (Sequence A)


record isRegular (x : Sequence ℚ) : 𝒰₀ where
  field reg : ∀(m n : ℕ) -> ∣ ((x ⌄ m) + - (x ⌄ n)) ∣ < ⟌(ι (suc m)) + ⟌(ι (suc n))

Realᶜ : 𝒰 _
Realᶜ = _ :& isRegular

macro ℝᶜ = #structureOn Realᶜ

instance
  Index-Notation:Realᶜ : Index-Notation (Realᶜ) (const ℕ) (λ _ -> ⊤-𝒰 {ℓ₀}) (const ℚ)
  Index-Notation:Realᶜ = record { _⌄_ = λ x i → ix ⟨ x ⟩ i }

record _∼-ℝᶜ_ (x y : ℝᶜ) : 𝒰₀ where
  constructor incl
  field sim-ℝᶜ : ∀(n : ℕ) -> ∣ (x ⌄ n) + - (y ⌄ n) ∣ < 2 ⋅ ⟌(ι (suc n))

open _∼-ℝᶜ_ public

private
  lem-1 : ∀{x : ℝᶜ} -> x ∼-ℝᶜ x
  lem-1 = {!!}
  -- ⟨ lem-1 ⟩ n = {!!}

  lem-2 : ∀{x y : ℝᶜ} -> x ∼-ℝᶜ y -> y ∼-ℝᶜ x
  lem-2 = {!!}

  lem-3 : ∀{x y z : ℝᶜ} -> x ∼-ℝᶜ y -> y ∼-ℝᶜ z -> x ∼-ℝᶜ z
  lem-3 = {!!}

instance
  isSetoid:ℝᶜ : isSetoid ℝᶜ
  isSetoid:ℝᶜ = isSetoid:byDef _∼-ℝᶜ_ lem-1 lem-2 lem-3

instance
  isMonoid:ℝᶜ : isMonoid ℝᶜ
  isMonoid:ℝᶜ = {!!}

instance
  isGroup:ℝᶜ : isGroup ℝᶜ
  isGroup:ℝᶜ = {!!}

instance
  isCommutative:ℝᶜ : isCommutative ℝᶜ
  isCommutative:ℝᶜ = {!!}

instance
  isSemiring:ℝᶜ : isSemiring ℝᶜ
  isSemiring:ℝᶜ = {!!}

instance
  isRing:ℝᶜ : isRing ℝᶜ
  isRing:ℝᶜ = record {}

instance
  isField:ℝᶜ : isField ℝᶜ
  isField:ℝᶜ = {!!}

instance
  isOrderedRing:ℝᶜ : isOrderedRing ℓ₀ ℝᶜ
  isOrderedRing:ℝᶜ = {!!}

-- NOTE: this should actually be derived from ordered ring
instance
  isPreorder:ℝᶜ : isPreorder ℓ₀ ℝᶜ
  isPreorder:ℝᶜ = {!!}


