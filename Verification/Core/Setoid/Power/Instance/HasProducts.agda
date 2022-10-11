
module Verification.Core.Setoid.Power.Instance.HasProducts where

open import Verification.Core.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition

open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Setoid.Power.Intersection


----------------------------------------------------------
-- Binary products
----------------------------------------------------------
module _ {A : 𝐒𝐭𝐝 𝑖} where

  intro-⊤-𝒫-𝐒𝐭𝐝 : ∀{U : 𝒫 A} -> U ⟶ ℧
  intro-⊤-𝒫-𝐒𝐭𝐝 = incl (λ a∈U → tt)

  instance
    isTerminal:℧-𝒫-𝐒𝐭𝐝 : isTerminal {𝒞 = 𝒫 A} ℧-𝒫-𝐒𝐭𝐝
    isTerminal:℧-𝒫-𝐒𝐭𝐝 = record
      { intro-⊤ = intro-⊤-𝒫-𝐒𝐭𝐝
      ; expand-⊤ = tt
      }

  instance
    hasTerminal:𝒫-𝐒𝐭𝐝 : hasTerminal (𝒫 A)
    hasTerminal.⊤ hasTerminal:𝒫-𝐒𝐭𝐝 = ℧
    hasTerminal.isTerminal:⊤ hasTerminal:𝒫-𝐒𝐭𝐝 = it

  module _ {U V : 𝒫 A} where

    π₀-𝒫-𝐒𝐭𝐝 : U ∩ V ⟶ U
    π₀-𝒫-𝐒𝐭𝐝 = incl (λ a∈U∩V → fst a∈U∩V)

    π₁-𝒫-𝐒𝐭𝐝 : U ∩ V ⟶ V
    π₁-𝒫-𝐒𝐭𝐝 = incl (λ a∈U∩V → snd a∈U∩V)

    ⧼_⧽-𝒫-𝐒𝐭𝐝 : ∀{X} -> (X ⟶ U) ×-𝒰 (X ⟶ V) -> X ⟶ U ∩ V
    ⧼_⧽-𝒫-𝐒𝐭𝐝 (f , g) = incl λ x∈X → ⟨ f ⟩ x∈X , ⟨ g ⟩ x∈X

    instance
      isProduct:∩-𝒫-𝐒𝐭𝐝 : isProduct U V (U ∩ V)
      isProduct.π₀ isProduct:∩-𝒫-𝐒𝐭𝐝 = π₀-𝒫-𝐒𝐭𝐝
      isProduct.π₁ isProduct:∩-𝒫-𝐒𝐭𝐝 = π₁-𝒫-𝐒𝐭𝐝
      isProduct.⧼ isProduct:∩-𝒫-𝐒𝐭𝐝 ⧽ = ⧼_⧽-𝒫-𝐒𝐭𝐝
      isProduct.isSetoidHom:⧼⧽ isProduct:∩-𝒫-𝐒𝐭𝐝 = record { cong-∼ = λ x → tt }
      isProduct.reduce-π₀ isProduct:∩-𝒫-𝐒𝐭𝐝 = tt
      isProduct.reduce-π₁ isProduct:∩-𝒫-𝐒𝐭𝐝 = tt
      isProduct.expand-π₀,π₁ isProduct:∩-𝒫-𝐒𝐭𝐝 = tt

  instance
    hasProducts:𝒫-𝐒𝐭𝐝 : hasProducts (𝒫 A)
    hasProducts:𝒫-𝐒𝐭𝐝 = record { _⊓_ = _ }

  instance
    hasFiniteProducts:𝒫-𝐒𝐭𝐝 : hasFiniteProducts (𝒫 A)
    hasFiniteProducts:𝒫-𝐒𝐭𝐝 = hasFiniteProducts:default

----------------------------------------------------------
-- Indexed products
----------------------------------------------------------

module _ {A : 𝐒𝐭𝐝 𝑖} where

  module _ {I : 𝒰₀} {Uᵢ : I -> 𝒫 A} where
    private
      U = ⋂-𝒫-𝐒𝐭𝐝 Uᵢ

    πᵢ-𝒫-𝐒𝐭𝐝 : ∀ i -> U ⟶ Uᵢ i
    πᵢ-𝒫-𝐒𝐭𝐝 i = incl (λ x → x i)

    ⧼_⧽ᵢ-𝒫-𝐒𝐭𝐝 : ∀{V : 𝒫 A} -> (∀ i -> V ⟶ Uᵢ i) -> V ⟶ U
    ⧼_⧽ᵢ-𝒫-𝐒𝐭𝐝 fᵢ = incl λ x∈V i → ⟨ fᵢ i ⟩ x∈V

    instance
      isIndexedProduct:⋂-𝒫-𝐒𝐭𝐝 : isIndexedProduct Uᵢ U
      isIndexedProduct.πᵢ isIndexedProduct:⋂-𝒫-𝐒𝐭𝐝 = πᵢ-𝒫-𝐒𝐭𝐝
      isIndexedProduct.⧼ isIndexedProduct:⋂-𝒫-𝐒𝐭𝐝 ⧽ᵢ = ⧼_⧽ᵢ-𝒫-𝐒𝐭𝐝
      isIndexedProduct.reduce-πᵢ isIndexedProduct:⋂-𝒫-𝐒𝐭𝐝 = λ f i → tt
      isIndexedProduct.expand-πᵢ isIndexedProduct:⋂-𝒫-𝐒𝐭𝐝 = λ f → tt

  -- module _ {I : 𝒰₀} where
  --   instance
  --     hasIndexedProducts:𝒫-𝐒𝐭𝐝 : hasIndexedProducts I (𝒫 A)
  --     hasIndexedProducts.⨅ᵢ hasIndexedProducts:𝒫-𝐒𝐭𝐝 = ⋂-𝒫-𝐒𝐭𝐝
  --     hasIndexedProducts.isIndexedProduct:⨅ᵢ hasIndexedProducts:𝒫-𝐒𝐭𝐝 = it
  instance
    hasAllIndexedProducts:𝒫-𝐒𝐭𝐝 : hasAllIndexedProducts ℓ₀ (𝒫 A)
    hasAllIndexedProducts.⨅ᵢ hasAllIndexedProducts:𝒫-𝐒𝐭𝐝 = ⋂-𝒫-𝐒𝐭𝐝
    hasAllIndexedProducts.isIndexedProduct:⨅ᵢ hasAllIndexedProducts:𝒫-𝐒𝐭𝐝 = it






