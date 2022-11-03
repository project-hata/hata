
module Verification.Core.Setoid.Power.Instance.HasCoproducts where

open import Verification.Core.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition

open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Setoid.Power.Union


----------------------------------------------------------
-- Binary products
----------------------------------------------------------
module _ {A : 𝐒𝐭𝐝 𝑖} where

  elim-⊥-𝒫-𝐒𝐭𝐝 : ∀{U : 𝒫 A} -> ∅ ⟶ U
  elim-⊥-𝒫-𝐒𝐭𝐝 = incl (λ ())

  instance
    isInitial:℧-𝒫-𝐒𝐭𝐝 : isInitial {𝒞 = 𝒫 A} ∅-𝒫-𝐒𝐭𝐝
    isInitial:℧-𝒫-𝐒𝐭𝐝 = record
      { elim-⊥ = elim-⊥-𝒫-𝐒𝐭𝐝
      ; expand-⊥ = tt
      }


  instance
    hasInitial:𝒫-𝐒𝐭𝐝 : hasInitial (𝒫 A)
    hasInitial.⊥ hasInitial:𝒫-𝐒𝐭𝐝 = ∅
    hasInitial.isInitial:⊥ hasInitial:𝒫-𝐒𝐭𝐝 = it

  module _ {U V : 𝒫 A} where

    ι₀-𝒫-𝐒𝐭𝐝 : U ⟶ U ∪ V
    ι₀-𝒫-𝐒𝐭𝐝 = incl (λ a∈U → left a∈U)

    ι₁-𝒫-𝐒𝐭𝐝 : V ⟶ U ∪ V
    ι₁-𝒫-𝐒𝐭𝐝 = incl (λ a∈V → right a∈V)

    ⦗_⦘-𝒫-𝐒𝐭𝐝 : ∀{X} -> (U ⟶ X) ×-𝒰 (V ⟶ X) -> U ∪ V ⟶ X
    ⦗_⦘-𝒫-𝐒𝐭𝐝 (f , g) = incl (λ x → case x of ⟨ f ⟩ ⟨ g ⟩)

    instance
      isCoproduct:∪-𝒫-𝐒𝐭𝐝 : isCoproduct U V (U ∪ V)
      isCoproduct.ι₀ isCoproduct:∪-𝒫-𝐒𝐭𝐝 = ι₀-𝒫-𝐒𝐭𝐝
      isCoproduct.ι₁ isCoproduct:∪-𝒫-𝐒𝐭𝐝 = ι₁-𝒫-𝐒𝐭𝐝
      isCoproduct.⦗ isCoproduct:∪-𝒫-𝐒𝐭𝐝 ⦘ = ⦗_⦘-𝒫-𝐒𝐭𝐝
      isCoproduct.isSetoidHom:⦗⦘ isCoproduct:∪-𝒫-𝐒𝐭𝐝 = record { cong-∼ = λ x → tt }
      isCoproduct.reduce-ι₀ isCoproduct:∪-𝒫-𝐒𝐭𝐝 = tt
      isCoproduct.reduce-ι₁ isCoproduct:∪-𝒫-𝐒𝐭𝐝 = tt
      isCoproduct.expand-ι₀,ι₁ isCoproduct:∪-𝒫-𝐒𝐭𝐝 = tt

  instance
    hasCoproducts:𝒫-𝐒𝐭𝐝 : hasCoproducts (𝒫 A)
    hasCoproducts:𝒫-𝐒𝐭𝐝 = record { _⊔_ = _ }

  instance
    hasFiniteCoproducts:𝒫-𝐒𝐭𝐝 : hasFiniteCoproducts (𝒫 A)
    hasFiniteCoproducts:𝒫-𝐒𝐭𝐝 = hasFiniteCoproducts:default

----------------------------------------------------------
-- Indexed coproducts
----------------------------------------------------------

module _ {A : 𝐒𝐭𝐝 𝑖} where

  module _ {I : 𝒰₀} {Uᵢ : I -> 𝒫 A} where
    private
      U = ⋃-𝒫-𝐒𝐭𝐝 Uᵢ

    ιᵢ-𝒫-𝐒𝐭𝐝 : ∀ i -> Uᵢ i ⟶ U
    ιᵢ-𝒫-𝐒𝐭𝐝 i = incl λ x → i , x

    ⦗_⦘ᵢ-𝒫-𝐒𝐭𝐝 : ∀{V : 𝒫 A} -> (∀ i -> Uᵢ i ⟶ V) -> U ⟶ V
    ⦗_⦘ᵢ-𝒫-𝐒𝐭𝐝 fᵢ = incl λ (i , x∈V) → ⟨ fᵢ i ⟩ x∈V

    instance
      isIndexedCoproduct:⋃-𝒫-𝐒𝐭𝐝 : isIndexedCoproduct Uᵢ U
      isIndexedCoproduct.ιᵢ isIndexedCoproduct:⋃-𝒫-𝐒𝐭𝐝 = ιᵢ-𝒫-𝐒𝐭𝐝
      isIndexedCoproduct.⦗ isIndexedCoproduct:⋃-𝒫-𝐒𝐭𝐝 ⦘ᵢ = ⦗_⦘ᵢ-𝒫-𝐒𝐭𝐝
      isIndexedCoproduct.reduce-ιᵢ isIndexedCoproduct:⋃-𝒫-𝐒𝐭𝐝 = λ f i → tt
      isIndexedCoproduct.expand-ιᵢ isIndexedCoproduct:⋃-𝒫-𝐒𝐭𝐝 = λ f → tt

  module _ {I : 𝒰₀} where
    -- instance
    --   hasIndexedCoproducts:𝒫-𝐒𝐭𝐝 : hasIndexedCoproducts I (𝒫 A)
    --   hasIndexedCoproducts.⨆ᵢ hasIndexedCoproducts:𝒫-𝐒𝐭𝐝 = ⋃-𝒫-𝐒𝐭𝐝
    --   hasIndexedCoproducts.isIndexedCoproduct:⨆ᵢ hasIndexedCoproducts:𝒫-𝐒𝐭𝐝 = it

  instance
    hasAllIndexedCoproducts:𝒫-𝐒𝐭𝐝 : hasAllIndexedCoproducts ℓ₀ (𝒫 A)
    hasAllIndexedCoproducts.⨆ᵢ hasAllIndexedCoproducts:𝒫-𝐒𝐭𝐝 = ⋃-𝒫-𝐒𝐭𝐝
    hasAllIndexedCoproducts.isIndexedCoproduct:⨆ᵢ hasAllIndexedCoproducts:𝒫-𝐒𝐭𝐝 = it


