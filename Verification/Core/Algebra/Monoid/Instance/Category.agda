
module Verification.Core.Algebra.Monoid.Instance.Category where

open import Verification.Core.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition


-- module _ (M : Monoid 𝑖) (N : Monoid 𝑗) where
--   data isMonoidHom (f : ⟨ M ⟩ -> ⟨ N ⟩) : 𝒰 (𝑖 ､ 𝑗) where

module _ {M : Monoid 𝑖} where
  isMonoidHom:id-𝐌𝐨𝐧 : isMonoidHom M M id-𝐒𝐭𝐝
  isMonoidHom:id-𝐌𝐨𝐧 = record { pres-◌ = refl ; pres-⋆ = refl }

  id-𝐌𝐨𝐧 : MonoidHom M M
  id-𝐌𝐨𝐧 = (λ a -> a) since isMonoidHom:id-𝐌𝐨𝐧

module _ {M : Monoid 𝑖} {N : Monoid 𝑗} {O : Monoid 𝑘} where
  module _ (f : MonoidHom M N) (g : MonoidHom N O) where

    isMonoidHom:◆-𝐌𝐨𝐧 : isMonoidHom M O ((↳ f) ◆-𝐒𝐭𝐝 (↳ g))
    isMonoidHom:◆-𝐌𝐨𝐧 =
      let P0 : ⟨ g ⟩ (⟨ f ⟩ ◌) ∼ ◌
          P0 = congOf (↳ g) pres-◌ ∙ pres-◌

          P1 : ∀{a b} -> ⟨ g ⟩ (⟨ f ⟩ (a ⋆ b)) ∼ ⟨ g ⟩ (⟨ f ⟩ (a)) ⋆ ⟨ g ⟩ (⟨ f ⟩ (b))
          P1 = congOf (↳ g) pres-⋆ ∙ pres-⋆
      in record
        { pres-◌ = P0
        ; pres-⋆ = P1
        }

    _◆-𝐌𝐨𝐧_ : MonoidHom M O
    _◆-𝐌𝐨𝐧_ = _ since isMonoidHom:◆-𝐌𝐨𝐧

instance
  isCategory:Monoid : isCategory (Monoid 𝑖)
  isCategory.Hom isCategory:Monoid = MonoidHom
  isCategory.isSetoid:Hom isCategory:Monoid = isSetoid:MonoidHom
  isCategory.id isCategory:Monoid = id-𝐌𝐨𝐧
  isCategory._◆_ isCategory:Monoid = _◆-𝐌𝐨𝐧_
  isCategory.unit-l-◆ isCategory:Monoid = incl (refl)
  isCategory.unit-r-◆ isCategory:Monoid = incl refl
  isCategory.unit-2-◆ isCategory:Monoid = incl refl
  isCategory.assoc-l-◆ isCategory:Monoid = incl refl
  isCategory.assoc-r-◆ isCategory:Monoid = incl refl
  isCategory._◈_ isCategory:Monoid = λ p q -> {!!}

macro
  𝐌𝐨𝐧 : ∀ 𝑖 -> _
  𝐌𝐨𝐧 𝑖 = #structureOn (Monoid 𝑖)


