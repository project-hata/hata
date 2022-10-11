
module Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.HasProducts where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Imports
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Definition
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.Category

module _ {𝒞 : DCLC 𝑖} where

  --------------------------------------------------------------------
  -- finite products
  --------------------------------------------------------------------

  ⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞
  ⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ⊤ , ⊥ because π₁

  intro-⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : ∀{a} -> a ⟶ ⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
  intro-⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = intro-⊤ , elim-⊥

  instance
    isTerminal:⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : isTerminal ⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
    isTerminal:⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = record { intro-⊤ = intro-⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 ; expand-⊤ = tt }

  _⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_ : (a b : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞) -> 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞
  _⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_ (a₀ , a₁ because f) (b₀ , b₁ because g) = (a₀ ⊓ b₀) , (a₁ ⊔ b₁) because h
    where
      h : (a₀ ⊓ b₀) ⊓ (a₁ ⊔ b₁) ⟶ ⊥
      h = ⟨ dist ⟩ ◆ ⦗ (π₀ ⇃⊓⇂ id) ◆ f , (π₁ ⇃⊓⇂ id) ◆ g ⦘

  module _ {a b : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞} where
    π₀-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : (a ⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b) ⟶ a
    π₀-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = π₀ , ι₀

    π₁-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : (a ⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b) ⟶ b
    π₁-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = π₁ , ι₁

    ⧼_⧽-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : ∀{x} -> (x ⟶ a) ×-𝒰 (x ⟶ b) -> x ⟶ (a ⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b)
    ⧼_⧽-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (f , g) = ⧼ fst f , fst g ⧽ , ⦗ snd f , snd g ⦘

    instance
      isProduct:⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : isProduct a b (a ⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b)
      isProduct.π₀ isProduct:⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = π₀-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
      isProduct.π₁ isProduct:⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = π₁-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
      isProduct.⧼ isProduct:⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 ⧽ = ⧼_⧽-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
      isProduct.isSetoidHom:⧼⧽ isProduct:⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = record { cong-∼ = λ x → tt }
      isProduct.reduce-π₀ isProduct:⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = tt
      isProduct.reduce-π₁ isProduct:⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = tt
      isProduct.expand-π₀,π₁ isProduct:⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = tt

  instance
    hasTerminal:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : hasTerminal (𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞)
    hasTerminal.⊤ hasTerminal:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = ⊤-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
    hasTerminal.isTerminal:⊤ hasTerminal:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = it

  instance
    hasProducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : hasProducts (𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞)
    hasProducts._⊓_ hasProducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = _⊓-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_
    hasProducts.isProduct:⊓ hasProducts:𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = it


  --------------------------------------------------------------------
  -- indexed products
  --------------------------------------------------------------------

  module _ {I : 𝒰₀} where

    -- ⨅ᵢ-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : 
  -- {a : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞} {b : I -> 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞} where



