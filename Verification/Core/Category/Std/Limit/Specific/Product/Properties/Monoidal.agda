
module Verification.Core.Category.Std.Limit.Specific.Product.Properties.Monoidal where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Definition



module _ {𝒞' : Category 𝑖} {{_ : hasFiniteProducts 𝒞'}} where
  private
    macro 𝒞 = #structureOn ⟨ 𝒞' ⟩
    instance
      _ : isSetoid 𝒞
      _ = isSetoid:byCategory

  byExpand-π₀,π₁ : ∀{a b c : 𝒞} -> {f g : c ⟶ a ⊓ b}
                   -> f ◆ π₀ ∼ g ◆ π₀
                   -> f ◆ π₁ ∼ g ◆ π₁
                   -> f ∼ g
  byExpand-π₀,π₁ {f = f} {g} p₀ p₁ =
    f                   ⟨ expand-π₀,π₁ ⟩-∼
    ⧼ f ◆ π₀ , f ◆ π₁ ⧽ ⟨ ⧼≀ p₀ , p₁ ≀⧽ ⟩-∼
    ⧼ g ◆ π₀ , g ◆ π₁ ⧽ ⟨ expand-π₀,π₁ ⁻¹ ⟩-∼
    g                   ∎

  open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.FiniteCoproduct
  open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal


  fromᵒᵖ-≅ : ∀{a b : 𝒞} -> IsoOf (𝒞 ᵒᵖ) a b -> IsoOf 𝒞 a b
  fromᵒᵖ-≅ ϕ = inverse-◆ {{isCategory:ᵒᵖ}} (of ϕ) since
    record
      { inverse-◆ = ⟨ ϕ ⟩
      ; inv-r-◆ = inv-r-◆ {{isCategory:ᵒᵖ}} (of ϕ)
      ; inv-l-◆ = inv-l-◆ {{isCategory:ᵒᵖ}} (of ϕ)
      }

  assoc-l-⊓ : ∀{a b c : 𝒞} -> (a ⊓ b) ⊓ c ≅ a ⊓ (b ⊓ c)
  assoc-l-⊓ {a} {b} {c} = fromᵒᵖ-≅ (assoc-l-⊔ {𝒞' = ⟨ 𝒞' ⟩ since isCategory:ᵒᵖ })

