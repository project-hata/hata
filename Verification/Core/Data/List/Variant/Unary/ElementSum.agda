
module Verification.Core.Data.List.Variant.Unary.ElementSum where

open import Verification.Core.Conventions
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element


module _ {A : 𝒰 𝑖} where
  record ♮Element (as : List A) : 𝒰 𝑖 where
    constructor _,_
    field getElement : A
    field getElementProof : as ∍♮ getElement




