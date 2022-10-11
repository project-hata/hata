
module Verification.Core.Category.Std.Category.Opposite.Instance.FiniteCoproductCategory where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite.Definition

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product

module _ {𝒞 : Category 𝑖} {{_ : hasProducts 𝒞}} where

  instance
    hasCoproducts:ᵒᵖ-𝐂𝐚𝐭 : hasCoproducts (𝒞 ᵒᵖ⌯)
    hasCoproducts:ᵒᵖ-𝐂𝐚𝐭 = {!!}

  instance
    hasFiniteCoproducts:ᵒᵖ-𝐂𝐚𝐭 : hasFiniteCoproducts (𝒞 ᵒᵖ⌯)
    hasFiniteCoproducts:ᵒᵖ-𝐂𝐚𝐭 = {!!}





