
module Verification.Research.Strictification.Main where

open import Verification.Conventions hiding (_≡_) renaming (_≣_ to _≡_ ; _≢-Str_ to _≢_)
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition



record FOSignature (𝑖 : 𝔏 ^ 2) : 𝒰 (𝑖 ⁺) where

  field Type : 𝒰 (𝑖 ⌄ 0)
  field Ctor : 𝒰 (𝑖 ⌄ 1)
  field typeof : Ctor -> Type
  field argsof : Ctor -> List Type

  -- field {{isDiscrete:Sort}} : isDiscrete Sort
  -- field {{isDiscrete:Con}} : ∀{αs α} -> isDiscrete (Con αs α)
  -- field {{isSet-Str:Sort}} : isSet-Str Sort

open FOSignature public
-- open FOSignature public using (Type ; Ctor)
-- open FOSignature {{...}} public using (typeof ; argsof)

module _ (Σ : FOSignature 𝑖) where
  data FOTree : (α : Type Σ) -> 𝒰 𝑖 where
    [] : ∀{α} -> FOTree α
    con : (c : Ctor Σ) -> List[ β ∈ argsof Σ c ] (FOTree β) -> FOTree (typeof Σ c)


module _ {Σ : FOSignature 𝑖} where
  data _∍FO_ : ∀{α} -> (FOTree Σ α) -> Type Σ -> 𝒰 𝑖 where
    [] : ∀{α} -> [] {α = α} ∍FO α
    con : {c : Ctor Σ} -> {ts : List[ β ∈ argsof Σ c ] (FOTree Σ β)} -> ∀{β t} -> (_ : ts ∍♮ᵈ (β , t)) -> ∀{γ} -> t ∍FO γ -> con c ts ∍FO γ
















-- module _ (Σ : FOSignature 𝑖) where

--   data Term : List (Type Σ) -> Type Σ -> 𝒰 𝑖 where

--     -- var : ∀{α αs} -> αs ∍ α -> Term αs α
--     -- con : ∀{γs βs α} -> (f : Con Σ βs α) -> ⋆List[ β ∈ ι βs ] (Term γs β) -> Term γs α


-- module _ (Σ : FOSignature 𝑖) where
--   EΣ : FOSignature _
--   EΣ = record
--        { Type = {!!}
--        ; Ctor = Ctor Σ
--        ; typeof = {!!}
--        ; argsof = {!!}
--        }

