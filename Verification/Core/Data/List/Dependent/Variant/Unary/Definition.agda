
module Verification.Core.Data.List.Dependent.Variant.Unary.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
-- open import Verification.Core.Data.List.Variant.Binary.Natural

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Natural

-- dependent lists

module _ {A : 𝒰 𝑖} where
  mutual
    syntax Listᴰ (λ a -> B) as = List[ a ∈ as ] B

    data Listᴰ (B : A -> 𝒰 𝑗) : (as : List A) -> 𝒰 (𝑖 ､ 𝑗) where
      [] : List[ a ∈ [] ] B a
      _∷_ : ∀{a as} -> B a -> List[ a ∈ as ] B a -> List[ a ∈ a ∷ as ] B a



ConstListᴰ : (A : 𝒰 𝑖) (n : ♮ℕ) -> 𝒰 _
ConstListᴰ A = Listᴰ (const A)

-- | And also the following:

Vec : 𝒰 𝑖 -> ♮ℕ -> 𝒰 _
Vec A n = List[ i ∈ n ] A


-- #Notation/Rewrite# ⋆List = {}^{⋆}List


module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} where
  data _∍♮ᵈ_ : {as : List A} (bs : Listᴰ B as) -> ∑ B -> 𝒰 (𝑖 ､ 𝑗) where
    take : ∀{a as} {b : B a} {bs : Listᴰ B as} -> (b ∷ bs) ∍♮ᵈ (a , b)
    skip : ∀{a as v} {b : B a} {w : B v} {bs : Listᴰ B as} -> bs ∍♮ᵈ (v , w) -> (b ∷ bs) ∍♮ᵈ (v , w)




