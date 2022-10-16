
module Verification.Core.Category.Std.Category.Construction.Core where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso.Definition

----------------------------------------
-- Helpers
----------------------------------------
module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} where
  isSetoid:byFullSubsetoid : {B : 𝒰 𝑘} (f : B -> A) -> isSetoid B
  isSetoid:byFullSubsetoid f = isSetoid:byDef (λ x y -> f x ∼ f y) refl sym _∙_

----------------------------------------
-- Begin
----------------------------------------


record Core (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  constructor incl
  field ⟨_⟩ : ⟨ 𝒞 ⟩

open Core public

module _ (𝒞 : Category 𝑖) where
  macro 𝐂𝐨𝐫𝐞 = #structureOn (Core 𝒞)

module _ {𝒞 : Category 𝑖} where
  record Hom-Core (a b : 𝐂𝐨𝐫𝐞 𝒞) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : ⟨ a ⟩ ≅ ⟨ b ⟩
  open Hom-Core public

  module _ {a b : 𝐂𝐨𝐫𝐞 𝒞} where
    instance
      isSetoid:Hom-Core : isSetoid (Hom-Core a b)
      isSetoid:Hom-Core = isSetoid:byFullSubsetoid ⟨_⟩

  id-Core : ∀{a} -> Hom-Core a a
  id-Core = incl refl-≅

  _◆-Core_ : ∀{a b c} -> Hom-Core a b -> Hom-Core b c -> Hom-Core a c
  _◆-Core_ (incl f) (incl g) = incl (f ∙-≅ g)

  instance
    isCategory:𝐂𝐨𝐫𝐞 : isCategory (𝐂𝐨𝐫𝐞 𝒞)
    isCategory.Hom isCategory:𝐂𝐨𝐫𝐞 = Hom-Core
    isCategory.isSetoid:Hom isCategory:𝐂𝐨𝐫𝐞 = isSetoid:Hom-Core
    isCategory.id isCategory:𝐂𝐨𝐫𝐞 = id-Core
    isCategory._◆_ isCategory:𝐂𝐨𝐫𝐞 = _◆-Core_
    isCategory.unit-l-◆ isCategory:𝐂𝐨𝐫𝐞 = incl unit-l-◆
    isCategory.unit-r-◆ isCategory:𝐂𝐨𝐫𝐞 = incl unit-r-◆
    isCategory.unit-2-◆ isCategory:𝐂𝐨𝐫𝐞 = incl unit-2-◆
    isCategory.assoc-l-◆ isCategory:𝐂𝐨𝐫𝐞 = incl assoc-l-◆
    isCategory.assoc-r-◆ isCategory:𝐂𝐨𝐫𝐞 = incl assoc-r-◆
    isCategory._◈_ isCategory:𝐂𝐨𝐫𝐞 = λ (incl p) (incl q) -> incl (p ◈ q)


  open import Verification.Core.Category.Std.Groupoid.Definition public

  module _ {a b : 𝐂𝐨𝐫𝐞 𝒞} (ϕ : a ⟶ b) where
    private
      ϕ⁻¹ : b ⟶ a
      ϕ⁻¹ = incl (sym-≅ ⟨ ϕ ⟩)

      lem-10 : ϕ ◆ ϕ⁻¹ ∼ id
      lem-10 = incl (inv-r-◆ (of ⟨ ϕ ⟩))

      lem-20 : ϕ⁻¹ ◆ ϕ ∼ id
      lem-20 = incl (inv-l-◆ (of ⟨ ϕ ⟩))

    instance
      isIso:Core-Hom : isIso (hom ϕ)
      isIso:Core-Hom = record
        { inverse-◆ = ϕ⁻¹
        ; inv-r-◆ = lem-10
        ; inv-l-◆ = lem-20
        }

  instance
    isGroupoid:𝐂𝐨𝐫𝐞 : isGroupoid (𝐂𝐨𝐫𝐞 𝒞)
    isGroupoid.isIso:hom isGroupoid:𝐂𝐨𝐫𝐞 = isIso:Core-Hom



