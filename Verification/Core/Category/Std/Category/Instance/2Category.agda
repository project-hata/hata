
module Verification.Core.Category.Std.Category.Instance.2Category where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Instance.CategoryLike
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Notation.Associativity





module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} where

  Comp-𝐂𝐚𝐭ᵘ : (Functor 𝒞 𝒟 × Functor 𝒟 ℰ) -> Functor 𝒞 ℰ
  Comp-𝐂𝐚𝐭ᵘ = λ₋ _◆-𝐂𝐚𝐭_

  macro Comp-𝐂𝐚𝐭 = #structureOn Comp-𝐂𝐚𝐭ᵘ

  map-Comp-𝐂𝐚𝐭 : ∀{a b} -> (a ⟶ b) -> Comp-𝐂𝐚𝐭 a ⟶ Comp-𝐂𝐚𝐭 b
  map-Comp-𝐂𝐚𝐭 {f₀ , g₀} {f₁ , g₁} (α , β) = γ since isNatural:γ
    where
      γ : ∀(x : ⟨ 𝒞 ⟩) -> ⟨ (f₀ ◆-𝐂𝐚𝐭 g₀) ⟩ x ⟶ ⟨ (f₁ ◆-𝐂𝐚𝐭 g₁) ⟩ x
      γ x = ⟨ β ⟩ _ ◆ map (⟨ α ⟩ _)

      isNatural:γ : isNatural (f₀ ◆-𝐂𝐚𝐭 g₀) (f₁ ◆-𝐂𝐚𝐭 g₁) γ
      isNatural:γ = {!!}

  instance
    isFunctor:Comp-𝐂𝐚𝐭 : isFunctor (𝐅𝐮𝐧𝐜 𝒞 𝒟 ×-𝐂𝐚𝐭 𝐅𝐮𝐧𝐜 𝒟 ℰ) (𝐅𝐮𝐧𝐜 𝒞 ℰ) Comp-𝐂𝐚𝐭
    isFunctor.map isFunctor:Comp-𝐂𝐚𝐭 = map-Comp-𝐂𝐚𝐭
    isFunctor.isSetoidHom:map isFunctor:Comp-𝐂𝐚𝐭 = {!!}
    isFunctor.functoriality-id isFunctor:Comp-𝐂𝐚𝐭 = {!!}
    isFunctor.functoriality-◆ isFunctor:Comp-𝐂𝐚𝐭 = {!!}
  infixl 50 _⇃◆⇂_
  _⇃◆⇂_ : ∀{f₀ f₁ : Functor 𝒞 𝒟} {g₀ g₁ : Functor 𝒟 ℰ}
        -> (α : Natural f₀ f₁) -> (β : Natural g₀ g₁)
        -> (Natural (f₀ ◆-𝐂𝐚𝐭 g₀) (f₁ ◆-𝐂𝐚𝐭 g₁))
  _⇃◆⇂_ α β = map-Comp-𝐂𝐚𝐭 (α , β)

  -----------------------------------------
  -- properties of ⇃◆⇂
  --
  -- interchange
  module _ {f₀ f₁ f₂ : Functor 𝒞 𝒟} {g₀ g₁ g₂ : Functor 𝒟 ℰ}
           (α : Natural f₀ f₁) (α' : Natural f₁ f₂)
           (β : Natural g₀ g₁) (β' : Natural g₁ g₂) where

    interchange-⇃◆⇂ : ((α ◆-𝐅𝐮𝐧𝐜 α') ⇃◆⇂ (β ◆-𝐅𝐮𝐧𝐜 β')) ∼ ((α ⇃◆⇂ β) ◆-𝐅𝐮𝐧𝐜 (α' ⇃◆⇂ β'))
    interchange-⇃◆⇂ = componentwise $ λ x ->
                        ⟨ β ◆-𝐅𝐮𝐧𝐜 β' ⟩ _ ◆ map (⟨ α ◆-𝐅𝐮𝐧𝐜 α' ⟩ _)               ⟨ refl ⟩-∼
                        (⟨ β ⟩ _ ◆ ⟨ β' ⟩ _) ◆ map (⟨ α ⟩ _ ◆ ⟨ α' ⟩ _)           ⟨ refl ◈ functoriality-◆ ⟩-∼
                        (⟨ β ⟩ _ ◆ ⟨ β' ⟩ _) ◆ (map (⟨ α ⟩ _) ◆ (map (⟨ α' ⟩ _))) ⟨ assoc-[ab][cd]∼a[bc]d-◆ ⟩-∼
                        ⟨ β ⟩ _ ◆ (⟨ β' ⟩ _ ◆ map (⟨ α ⟩ _)) ◆ (map (⟨ α' ⟩ _))   ⟨ refl ◈ naturality (⟨ α ⟩ _) ◈ refl ⟩-∼
                        ⟨ β ⟩ _ ◆ (map (⟨ α ⟩ _) ◆ ⟨ β' ⟩ _) ◆ (map (⟨ α' ⟩ _))   ⟨ assoc-[ab][cd]∼a[bc]d-◆ ⁻¹ ⟩-∼
                        (⟨ β ⟩ _ ◆ map (⟨ α ⟩ _)) ◆ (⟨ β' ⟩ _ ◆ (map (⟨ α' ⟩ _))) ∎



  --
  -- setoid compatability
  --
  module _ {f₀ f₁ : Functor 𝒞 𝒟} {g₀ g₁ : Functor 𝒟 ℰ}
           {α₀ α₁ : Natural f₀ f₁} {β₀ β₁ : Natural g₀ g₁}
         where

    infixl 50 _≀⇃◆⇂≀_
    _≀⇃◆⇂≀_ : α₀ ∼ α₁ -> β₀ ∼ β₁ -> (α₀ ⇃◆⇂ β₀ ∼ α₁ ⇃◆⇂ β₁)
    _≀⇃◆⇂≀_ p q = componentwise $ λ x →
                ⟨ β₀ ⟩ _ ◆ (map (⟨ α₀ ⟩ x))  ⟨ ⟨ q ⟩ _ ◈ cong-∼ (⟨ p ⟩ _) ⟩-∼
                ⟨ β₁ ⟩ _ ◆ (map (⟨ α₁ ⟩ x))  ∎

  --
  -- categorical laws
  --
  module _ {f₀ : Functor 𝒞 𝒟} {g₀ : Functor 𝒟 ℰ} where
    unit-⇃◆⇂ : id-𝐅𝐮𝐧𝐜 {F = f₀} ⇃◆⇂ id-𝐅𝐮𝐧𝐜 {F = g₀} ∼ idOn (f₀ ◆-𝐂𝐚𝐭 g₀)
    unit-⇃◆⇂ = componentwise $ λ x →
                 let lem-1 : (⟨ id-𝐅𝐮𝐧𝐜 {F = f₀} ⇃◆⇂ id-𝐅𝐮𝐧𝐜 {F = g₀} ⟩ x)
                             ∼
                             (⟨ idOn (f₀ ◆-𝐂𝐚𝐭 g₀) ⟩ x)
                     lem-1 = unit-l-◆ ∙ functoriality-id
                 in lem-1
  -----------------------------------------
  -- for isos
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} where
  module _ {f₀ f₁ : Functor 𝒞 𝒟} {g₀ g₁ : Functor 𝒟 ℰ} where
    _≀◆≀-𝐂𝐚𝐭_ : (α : f₀ ∼ f₁) -> (β : g₀ ∼ g₁)
              -> ((f₀ ◆-𝐂𝐚𝐭 g₀) ∼ (f₁ ◆-𝐂𝐚𝐭 g₁))
    _≀◆≀-𝐂𝐚𝐭_ α β = (⟨ α ⟩ ⇃◆⇂ ⟨ β ⟩) since P
      where
        αβ⁻¹ : (f₁ ◆-𝐂𝐚𝐭 g₁) ⟶ (f₀ ◆-𝐂𝐚𝐭 g₀)
        αβ⁻¹ = ⟨ α ⟩⁻¹ ⇃◆⇂ ⟨ β ⟩⁻¹

        lem-1 : (⟨ α ⟩ ⇃◆⇂ ⟨ β ⟩) ◆ (⟨ α ⟩⁻¹ ⇃◆⇂ ⟨ β ⟩⁻¹) ∼ id
        lem-1 = (⟨ α ⟩ ⇃◆⇂ ⟨ β ⟩) ◆ (⟨ α ⟩⁻¹ ⇃◆⇂ ⟨ β ⟩⁻¹)             ⟨ interchange-⇃◆⇂ ⟨ α ⟩ ⟨ α ⟩⁻¹ ⟨ β ⟩ ⟨ β ⟩⁻¹ ⁻¹ ⟩-∼
                (⟨ α ⟩ ◆-𝐅𝐮𝐧𝐜 ⟨ α ⟩⁻¹) ⇃◆⇂ (⟨ β ⟩ ◆-𝐅𝐮𝐧𝐜 ⟨ β ⟩⁻¹)     ⟨ _≀⇃◆⇂≀_ (inv-r-◆ (of α)) (inv-r-◆ (of β)) ⟩-∼
                id-𝐅𝐮𝐧𝐜 {F = f₀} ⇃◆⇂ id-𝐅𝐮𝐧𝐜 {F = g₀}                 ⟨ unit-⇃◆⇂ {f₀ = f₀} {g₀ = g₀} ⟩-∼
                id-𝐅𝐮𝐧𝐜 {F = f₀ ◆-𝐂𝐚𝐭 g₀}                             ∎

        lem-2 : (⟨ α ⟩⁻¹ ⇃◆⇂ ⟨ β ⟩⁻¹) ◆ (⟨ α ⟩ ⇃◆⇂ ⟨ β ⟩) ∼ id
        lem-2 = (⟨ α ⟩⁻¹ ⇃◆⇂ ⟨ β ⟩⁻¹) ◆ (⟨ α ⟩ ⇃◆⇂ ⟨ β ⟩)                ⟨ interchange-⇃◆⇂ ⟨ α ⟩⁻¹ ⟨ α ⟩ ⟨ β ⟩⁻¹ ⟨ β ⟩ ⁻¹ ⟩-∼
                (⟨ α ⟩⁻¹ ◆-𝐅𝐮𝐧𝐜 ⟨ α ⟩) ⇃◆⇂ (⟨ β ⟩⁻¹ ◆-𝐅𝐮𝐧𝐜 ⟨ β ⟩)        ⟨ _≀⇃◆⇂≀_ (inv-l-◆ (of α)) (inv-l-◆ (of β)) ⟩-∼
                id-𝐅𝐮𝐧𝐜 {F = f₁} ⇃◆⇂ id-𝐅𝐮𝐧𝐜 {F = g₁}                 ⟨ unit-⇃◆⇂ {f₀ = f₁} {g₀ = g₁} ⟩-∼
                id-𝐅𝐮𝐧𝐜 {F = f₁ ◆-𝐂𝐚𝐭 g₁}                             ∎

        P = record { inverse-◆ = αβ⁻¹ ; inv-r-◆ = lem-1 ; inv-l-◆ = lem-2 }




