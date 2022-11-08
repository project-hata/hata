
module Verification.Classical.Space.Measure.Instance.Category where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition

open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Universe.Definition -- for function ᶜ-σ

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Definition

open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition
open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Setoid.Power.Instance.HasCoproducts
open import Verification.Core.Setoid.Power.Instance.HasProducts
open import Verification.Core.Setoid.Power.Union
open import Verification.Core.Setoid.Power.Intersection
open import Verification.Core.Setoid.Construction.Product

open import Verification.Core.Set.Contradiction

open import Verification.Classical.Space.Measure.Definition



module _ {A : 𝐒𝐭𝐝 𝑖} {B : 𝐒𝐭𝐝 𝑖} where
  infix 90 _⁻¹ᵘ-𝐒𝐭𝐝
  _⁻¹ᵘ-𝐒𝐭𝐝 : (f : SetoidHom A B) -> 𝒫 B -> 𝒫 A
  _⁻¹ᵘ-𝐒𝐭𝐝 f U = Vᵘ since isSubsetoid:Vᵘ
    where
      Vᵘ : ⟨ A ⟩ -> Prop _
      Vᵘ a = ∣ ⟨ f ⟩ a ∈ U ∣

      P : ∀{a b : ⟨ A ⟩} -> a ∼ b -> a ∈ Vᵘ -> b ∈ Vᵘ
      -- P a∼b a∈V = transp-∼ {{_}} {{of U}} (congOf-∼ f a∼b) a∈V
      P a∼b a∈V = transpOf-∼ U (congOf-∼ f a∼b) a∈V

      isSubsetoid:Vᵘ : isSubsetoid Vᵘ
      isSubsetoid:Vᵘ = record { transp-∼ = P }

  module _ (f : SetoidHom A B) where
    macro
      _⁻¹-𝐒𝐭𝐝 = #structureOn (f ⁻¹ᵘ-𝐒𝐭𝐝)

--
-- NOTE: We use the same universe level 𝑖 for both `A` and `B` here
-- because doing otherwise would make the ⁻¹ machinery more complicated.
-- (Taking preimages across functions that switch universes would need
-- to be investigated.)
--
record isHom-𝐌𝐞𝐚𝐬 (A : 𝐌𝐞𝐚𝐬 𝑖) (B : 𝐌𝐞𝐚𝐬 𝑖) (f : SetoidHom (↳ A) (↳ B)) : 𝒰 (𝑖 ⁺) where
  field _⁻¹-σ : Measurable (of B) -> Measurable (of A)
  field eval-⁻¹-σ : ∀{U} -> ⟦ U ⁻¹-σ ⟧ ≅ (f ⁻¹-𝐒𝐭𝐝) ⟦ U ⟧

open isHom-𝐌𝐞𝐚𝐬 {{...}} public

module _ (A B : 𝐌𝐞𝐚𝐬 𝑖) where
  Hom-𝐌𝐞𝐚𝐬 = SetoidHom (↳ A) (↳ B) :& isHom-𝐌𝐞𝐚𝐬 A B

module _ {A B : 𝐌𝐞𝐚𝐬 𝑖} where
  record _∼-Hom-𝐌𝐞𝐚𝐬_ (f g : Hom-𝐌𝐞𝐚𝐬 A B) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : ⟨ f ⟩ ∼ ⟨ g ⟩

  open _∼-Hom-𝐌𝐞𝐚𝐬_ public

  instance
    isSetoid:Hom-𝐌𝐞𝐚𝐬 : isSetoid (Hom-𝐌𝐞𝐚𝐬 A B)
    isSetoid:Hom-𝐌𝐞𝐚𝐬 = isSetoid:byDef
      _∼-Hom-𝐌𝐞𝐚𝐬_
      (incl refl)
      (λ p -> incl (sym ⟨ p ⟩))
      (λ p q -> incl (⟨ p ⟩ ∙ ⟨ q ⟩))

id-𝐌𝐞𝐚𝐬 : ∀{A : 𝐌𝐞𝐚𝐬 𝑖} -> Hom-𝐌𝐞𝐚𝐬 A A
id-𝐌𝐞𝐚𝐬 {A = A} = id-𝒰 since P
  where
    P : isHom-𝐌𝐞𝐚𝐬 A A id-𝐒𝐭𝐝
    P = record
      { _⁻¹-σ = λ V -> V
      ; eval-⁻¹-σ = refl-≅
      }

_◆-𝐌𝐞𝐚𝐬_ : ∀{A B C : 𝐌𝐞𝐚𝐬 𝑖} -> Hom-𝐌𝐞𝐚𝐬 A B -> Hom-𝐌𝐞𝐚𝐬 B C -> Hom-𝐌𝐞𝐚𝐬 A C
_◆-𝐌𝐞𝐚𝐬_ {A = A} {B} {C} f g = ′_′ (⟨ f ⟩ ◆-𝒰 ⟨ g ⟩) {make∑i {{isSetoidHom:◆ {f = ↳ f} {↳ g}}}} {{P}}
  where
    P : isHom-𝐌𝐞𝐚𝐬 A C ((↳ f) ◆-𝐒𝐭𝐝 (↳ g))
    P = record
      { _⁻¹-σ = λ U -> (U ⁻¹-σ) ⁻¹-σ
      ; eval-⁻¹-σ = λ {U} -> ⟦ U ⁻¹-σ ⁻¹-σ ⟧ ⟨ {!!} ⟩-≅
                             (((↳ f) ◆-𝐒𝐭𝐝 (↳ g)) ⁻¹-𝐒𝐭𝐝) ⟦ U ⟧ ∎-≅ 
      }


instance
  isCategory:𝐌𝐞𝐚𝐬 : isCategory (𝐌𝐞𝐚𝐬 𝑖)
  isCategory.Hom isCategory:𝐌𝐞𝐚𝐬 = Hom-𝐌𝐞𝐚𝐬
  isCategory.isSetoid:Hom isCategory:𝐌𝐞𝐚𝐬 = isSetoid:Hom-𝐌𝐞𝐚𝐬
  isCategory.id isCategory:𝐌𝐞𝐚𝐬 = id-𝐌𝐞𝐚𝐬
  isCategory._◆_ isCategory:𝐌𝐞𝐚𝐬 = _◆-𝐌𝐞𝐚𝐬_
  isCategory.unit-l-◆ isCategory:𝐌𝐞𝐚𝐬 {f = f} = incl (unit-l-◆ {{of 𝐒𝐭𝐝 _}} {f = ↳ f})
  isCategory.unit-r-◆ isCategory:𝐌𝐞𝐚𝐬 = {!!}
  isCategory.unit-2-◆ isCategory:𝐌𝐞𝐚𝐬 = {!!}
  isCategory.assoc-l-◆ isCategory:𝐌𝐞𝐚𝐬 = {!!}
  isCategory.assoc-r-◆ isCategory:𝐌𝐞𝐚𝐬 = {!!}
  isCategory._◈_ isCategory:𝐌𝐞𝐚𝐬 = {!!}





