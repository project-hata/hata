
module Verification.Application.CompGen.Languages.CubeLang.Test where

open import Verification.Conventions hiding (_⊔_; _==_ ; refl ; zero)


data _==_ {a} {A : 𝒰 a} (x : A) : A → 𝒰 a where
  refl : x == x

data ⊥ : 𝒰₀ where

infixl 5 _==_

_≠_ : {A : 𝒰₀} → A → A → 𝒰₀
a ≠ b = a == b → ⊥


record isField (K : 𝒰₀) : 𝒰₀ where
  field
    zero : K
    one  : K

    _·_ : K → K → K
    _+_ : K → K → K

    assoc-+-l : ∀(a b c : K) → (a + b) + c == a + (b + c)
    assoc-·-l : ∀(a b c : K) → (a · b) · c == a · (b · c)

    comm-+ : ∀(a b : K) → a + b == b + a
    comm-· : ∀(a b : K) → a · b == b · a

    - : K → K
    mulInv : (a : K) → (proof : a ≠ zero) → K

    _/_ : K → K

    plusZero : ∀(a : K) → a + zero == a
    timesOne : ∀(a : K) → a · one == a

    aMinusAIsZero : ∀(a : K) → a + (- a) == zero

    distributive : ∀(a b c : K) → a · (b + c) == (a · b) + (a · c)

open isField {{...}} public

record Vector (K V : 𝒰₀) : 𝒰₀ where
  field
    scalar : isField K
    vector : V

record isKVectorSpace (K V : 𝒰₀) {{_ : isField K}} : 𝒰₀ where
  field
  ...

    distributiveScaAdd : {a b : K} {v : Vector K V} → (a + b) ∗ v == (a ∗ v) ++ (b ∗ v)

