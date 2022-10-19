
module Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.FiniteCoproduct where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Coproduct
open import Verification.Core.Category.Std.Limit.Specific.Product.Variant.Binary


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteProducts 𝒞}} where
  instance
    hasCoproducts:ᵒᵖ : hasCoproducts (𝒞 ᵒᵖ)
    hasCoproducts._⊔_ hasCoproducts:ᵒᵖ = _⊓_
    hasCoproducts.isCoproduct:⊔ hasCoproducts:ᵒᵖ = it

    hasInitial:ᵒᵖ : hasInitial (𝒞 ᵒᵖ)
    hasInitial.⊥ hasInitial:ᵒᵖ = ⊤
    hasInitial.isInitial:⊥ hasInitial:ᵒᵖ = it

  instance
    hasFiniteCoproducts:ᵒᵖ : hasFiniteCoproducts (𝒞 ᵒᵖ)
    hasFiniteCoproducts.hasInitial:this hasFiniteCoproducts:ᵒᵖ = hasInitial:ᵒᵖ
    hasFiniteCoproducts.hasCoproducts:this hasFiniteCoproducts:ᵒᵖ = hasCoproducts:ᵒᵖ






