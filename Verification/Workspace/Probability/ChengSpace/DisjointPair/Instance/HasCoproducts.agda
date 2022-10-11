
module Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.HasCoproducts where

open import Verification.Conventions hiding (_⊔_)
-- open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Imports

open import Verification.Core.Category.Std.Category.Definition public
open import Verification.Core.Category.Std.Morphism.Iso.Definition public
open import Verification.Core.Data.Prop.Definition public
open import Verification.Core.Data.Sum.Definition public
open import Verification.Core.Setoid.Definition public
open import Verification.Core.Setoid.Instance.Category public
open import Verification.Core.Setoid.Codiscrete public
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition public
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor public
open import Verification.Core.Category.Std.Limit.Specific.Product.Definition public
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor public



open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Definition
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.Category

module _ {𝒞 : DCLC 𝑖} where

  --------------------------------------------------------------------
  -- finite products
  --------------------------------------------------------------------

  ⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞
  ⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ⊥ , ⊤ because π₀

  elim-⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : ∀{a} -> ⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 ⟶ a
  elim-⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = elim-⊥ , intro-⊤

  instance
    isInitial:⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : isInitial ⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
    isInitial:⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = record { elim-⊥ = elim-⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 ; expand-⊥ = tt }

  _⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_ : (a b : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞) -> 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞
  _⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_ (a₀ , a₁ because f) (b₀ , b₁ because g) = (a₀ ⊔ b₀) , (a₁ ⊓ b₁) because h
    where
      h : (a₀ ⊔ b₀) ⊓ (a₁ ⊓ b₁) ⟶ ⊥
      h = {!!} -- ⟨ dist ⟩ ◆ ⦗ (ι₀ ⇃⊔⇂ id) ◆ f , (ι₁ ⇃⊔⇂ id) ◆ g ⦘

  module _ {a b : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞} where
    ι₀-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : a ⟶ (a ⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b)
    ι₀-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ι₀ , π₀

    ι₁-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : b ⟶ (a ⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b)
    ι₁-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ι₁ , π₁

    ⦗_⦘-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : ∀{x} -> (a ⟶ x) ×-𝒰 (b ⟶ x) -> (a ⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b) ⟶ x
    ⦗_⦘-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (f , g) = ⦗ fst f , fst g ⦘ , ⧼ snd f , snd g ⧽

    instance
      isCoproduct:⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : isCoproduct a b (a ⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b)
      isCoproduct.ι₀ isCoproduct:⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ι₀-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
      isCoproduct.ι₁ isCoproduct:⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ι₁-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
      isCoproduct.⦗ isCoproduct:⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 ⦘ = ⦗_⦘-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
      isCoproduct.isSetoidHom:⦗⦘ isCoproduct:⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = record { cong-∼ = λ x → tt }
      isCoproduct.reduce-ι₀ isCoproduct:⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = tt
      isCoproduct.reduce-ι₁ isCoproduct:⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = tt
      isCoproduct.expand-ι₀,ι₁ isCoproduct:⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = tt

  instance
    hasInitial:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : hasInitial (𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞)
    hasInitial.⊥ hasInitial:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ⊥-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
    hasInitial.isInitial:⊥ hasInitial:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = it

  instance
    hasCoproducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : hasCoproducts (𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞)
    hasCoproducts._⊔_ hasCoproducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = _⊔-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_
    hasCoproducts.isCoproduct:⊔ hasCoproducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = it

  --------------------------------------------------------------------
  -- indexed coproducts
  --------------------------------------------------------------------

  module _ {I : 𝒰₀} where
    ⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : (P : I -> 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞) -> 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞
    ⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 P = (⨆ᵢ P₀) , (⨅ᵢ P₁) because f
      where
        P₀ P₁ : I -> ⟨ 𝒞 ⟩
        P₀ i = fst (P i)
        P₁ i = snd (P i)

        g : ∀ i -> (⨅ᵢ P₁ ⊓ P₀ i) ⟶ ⊥
        g i = (πᵢ i ⇃⊓⇂ id) ◆ (⧼ π₁ , π₀ ⧽ ◆ dis (P i))

        f = (⨆ᵢ P₀) ⊓ (⨅ᵢ P₁)         ⟨ ⧼ π₁ , π₀ ⧽ ⟩-Hom

            (⨅ᵢ P₁) ⊓ (⨆ᵢ P₀)         ⟨ ⟨ distᵢ ⟩ ⟩-Hom

            (⨆[ i ] (⨅ᵢ P₁ ⊓ P₀ i))   ⟨ ⦗ g ⦘ᵢ ⟩-Hom

            ⊥                          ∎-Hom

    module _ {P : I -> 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞} where

      ιᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : ∀ i -> P i ⟶ ⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 P
      ιᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 i = (ιᵢ i) , (πᵢ i)

      ⦗_⦘ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : ∀ {Q} -> (∀ i -> P i ⟶ Q) -> ⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 P ⟶ Q
      ⦗_⦘ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 f = ⦗ fst (f i) ⦘[ i ] , ⧼ snd (f i) ⧽[ i ]

      instance
        isIndexedCoproduct:⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : isIndexedCoproduct P (⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 P)
        isIndexedCoproduct.ιᵢ isIndexedCoproduct:⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ιᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
        isIndexedCoproduct.⦗ isIndexedCoproduct:⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 ⦘ᵢ = ⦗_⦘ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
        isIndexedCoproduct.reduce-ιᵢ isIndexedCoproduct:⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = λ f i → tt
        isIndexedCoproduct.expand-ιᵢ isIndexedCoproduct:⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = λ f → tt

  instance
    hasAllIndexedCoproducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : hasAllIndexedCoproducts ℓ₀ (𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞)
    hasAllIndexedCoproducts.⨆ᵢ hasAllIndexedCoproducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ⨆ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
    hasAllIndexedCoproducts.isIndexedCoproduct:⨆ᵢ hasAllIndexedCoproducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = it

