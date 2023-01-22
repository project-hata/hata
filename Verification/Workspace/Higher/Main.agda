
module Verification.Workspace.Higher.Main where

open import Verification.Conventions

-- open import Cubical.Foundations.HLevels


data S¹ : 𝒰₀ where
  pt : S¹
  loop : pt ≡ pt
  loop2 : pt ≡ pt


data Inter : 𝒰₀ where
  a : Inter
  b : Inter
  pat : a ≡ b


data Trunc (A : 𝒰₀) : 𝒰₀ where
  ∥_∥ : A -> Trunc A
  squash : ∀{a b : Trunc A} -> (p q : a ≡ b) -> p ≡ q



triv : pt ≡ pt
triv = λ i -> pt



module _ {A : 𝒰₀} where

  -- lem1 : ~ i0 ≡ i1
  -- lem1 = ?

  lem2 : loop i0 ≡ pt
  lem2 = {!!}

  lem3 : (p : Inter -> A) -> p a ≡ p b
  lem3 p = λ i -> p (pat i)


  symm : ∀{a b : A} -> (p : a ≡ b) -> b ≡ a
  symm p = λ i -> p (~ i)

  


