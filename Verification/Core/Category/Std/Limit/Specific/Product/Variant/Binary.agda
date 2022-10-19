
module Verification.Core.Category.Std.Limit.Specific.Product.Variant.Binary where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  record isTerminal (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field intro-⊤ : ∀{a} -> a ⟶ x
    field expand-⊤ : ∀{a} -> {f : a ⟶ x} -> f ∼ intro-⊤

  open isTerminal {{...}} public

  record isProduct (a b x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field π₀ : x ⟶ a
    field π₁ : x ⟶ b
    field ⧼_⧽ : ∀{c} -> ((c ⟶ a) ×-𝒰 (c ⟶ b)) -> c ⟶ x
    field {{isSetoidHom:⧼⧽}} : ∀{c} -> isSetoidHom ′((c ⟶ᵘ a) ×-𝒰 (c ⟶ᵘ b))′ (c ⟶ x) (⧼_⧽ {c})
    field reduce-π₀ : ∀{c} {f : c ⟶ a} {g : c ⟶ b} -> ⧼ f , g ⧽ ◆ π₀ ∼ f
    field reduce-π₁ : ∀{c} {f : c ⟶ a} {g : c ⟶ b} -> ⧼ f , g ⧽ ◆ π₁ ∼ g
    field expand-π₀,π₁  : ∀{c} {f : c ⟶ x} -> f ∼ ⧼ f ◆ π₀ , f ◆ π₁ ⧽

  open isProduct {{...}} public


record hasTerminal (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field ⊤ : ⟨ 𝒞 ⟩
  field {{isTerminal:⊤}} : isTerminal ⊤

open hasTerminal {{...}} public

record hasProducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  infixl 100 _⊓_
  field _⊓_ : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
  field {{isProduct:⊓}} : ∀{a b} -> isProduct a b (a ⊓ b)
open hasProducts {{...}} public

record hasFiniteProducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field {{hasTerminal:this}} : hasTerminal 𝒞
  field {{hasProducts:this}}    : hasProducts 𝒞

open hasFiniteProducts {{...}} public

module _ {𝒞 : Category 𝑖} {{_ : hasProducts 𝒞}} {{_ : hasTerminal 𝒞}} where
  hasFiniteProducts:default : hasFiniteProducts 𝒞
  hasFiniteProducts.hasTerminal:this hasFiniteProducts:default  = it
  hasFiniteProducts.hasProducts:this hasFiniteProducts:default     = it





module _ {𝒞 : Category 𝑖} {{_ : hasFiniteProducts 𝒞}} where
  macro
    ⊓⃨ : SomeStructure
    ⊓⃨ = #structureOn (λ₋ _⊓_)


module _ {𝒞ᵘ : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞ᵘ}} {{_ : hasProducts ′ 𝒞ᵘ ′ }} where

  private macro 𝒞 = #structureOn 𝒞ᵘ
  private instance _ = isSetoidHom:⧼⧽

  ⧼≀_≀⧽ : ∀{a b c : 𝒞} {f₀ f₁ : c ⟶ a} {g₀ g₁ : c ⟶ b} -> (f₀ ∼ f₁) × (g₀ ∼ g₁) -> ⧼ f₀ , g₀ ⧽ ∼ ⧼ f₁ , g₁ ⧽
  ⧼≀_≀⧽ = cong-∼



