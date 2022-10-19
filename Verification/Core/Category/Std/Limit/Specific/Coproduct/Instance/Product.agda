
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Product where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition


module _ {𝒞 : Category 𝑖} where
  module _ {a b : ⟨ 𝒞 ⟩} where
    instance
      isProduct:Coproduct : ∀{x} -> {{_ : isCoproduct a b x}} -> isProduct {{of 𝒞 ᵒᵖ}} a b x
      isProduct.π₀ isProduct:Coproduct = ι₀
      isProduct.π₁ isProduct:Coproduct = ι₁
      isProduct.⧼ isProduct:Coproduct ⧽ = ⦗_⦘
      isProduct.isSetoidHom:⧼⧽ isProduct:Coproduct = it
      isProduct.reduce-π₀ isProduct:Coproduct = reduce-ι₀
      isProduct.reduce-π₁ isProduct:Coproduct = reduce-ι₁
      isProduct.expand-π₀,π₁ isProduct:Coproduct = expand-ι₀,ι₁

  instance
    isTerminal:Initial : ∀{x : ⟨ 𝒞 ⟩} -> {{_ : isInitial x}} -> isTerminal {{of 𝒞 ᵒᵖ}} x
    isTerminal.intro-⊤ isTerminal:Initial = elim-⊥
    isTerminal.expand-⊤ isTerminal:Initial = expand-⊥






