
module Verification.Core.Setoid.Power.Instance.Category where

open import Verification.Core.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition


module _ {A : 𝐒𝐭𝐝 𝑖} where

  record Hom-𝒫-𝐒𝐭𝐝 (U V : 𝒫 A) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : U ⊆ V

  open Hom-𝒫-𝐒𝐭𝐝 public

  id-𝒫-𝐒𝐭𝐝 : ∀{U : 𝒫 A} -> Hom-𝒫-𝐒𝐭𝐝 U U
  id-𝒫-𝐒𝐭𝐝 = incl (λ a∈U → a∈U)

  _◆-𝒫-𝐒𝐭𝐝_ : ∀{U V W : 𝒫 A} -> Hom-𝒫-𝐒𝐭𝐝 U V -> Hom-𝒫-𝐒𝐭𝐝 V W -> Hom-𝒫-𝐒𝐭𝐝 U W
  (f ◆-𝒫-𝐒𝐭𝐝 g) = incl (λ a∈U -> (⟨ g ⟩ (⟨ f ⟩ a∈U)))

  instance
    isCategory:𝒫-𝐒𝐭𝐝 : isCategory (𝒫 A)
    isCategory.Hom isCategory:𝒫-𝐒𝐭𝐝 = Hom-𝒫-𝐒𝐭𝐝
    isCategory.isSetoid:Hom isCategory:𝒫-𝐒𝐭𝐝 = isSetoid:byCodiscrete {𝑗 = ℓ₀}
    isCategory.id isCategory:𝒫-𝐒𝐭𝐝 {U} = id-𝒫-𝐒𝐭𝐝 {U = U}
    isCategory._◆_ isCategory:𝒫-𝐒𝐭𝐝 {U} {V} {W} = _◆-𝒫-𝐒𝐭𝐝_ {U = U} {V} {W}
    isCategory.unit-l-◆ isCategory:𝒫-𝐒𝐭𝐝 = tt
    isCategory.unit-r-◆ isCategory:𝒫-𝐒𝐭𝐝 = tt
    isCategory.unit-2-◆ isCategory:𝒫-𝐒𝐭𝐝 = tt
    isCategory.assoc-l-◆ isCategory:𝒫-𝐒𝐭𝐝 = tt
    isCategory.assoc-r-◆ isCategory:𝒫-𝐒𝐭𝐝 = tt
    isCategory._◈_ isCategory:𝒫-𝐒𝐭𝐝 = λ _ _ → tt


