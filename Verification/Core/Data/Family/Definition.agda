
module Verification.Core.Data.Family.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category

-- open import Verification.Core.Category.Std.Fibration.Definition

record hasFamily (𝒞 : Category 𝑖) (A : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor family
  field _■ : A -> ⟨ 𝒞 ⟩
  infix 100 _■

open hasFamily {{...}} public

Family : ∀ (𝒞 : Category 𝑖) -> (𝑗 : 𝔏) -> 𝒰 _
Family 𝒞 𝑗 = 𝒰 (𝑗) :& hasFamily 𝒞

macro
  𝐅𝐚𝐦 : ∀(𝒞 : Category 𝑖) -> ∀ 𝑗 -> SomeStructure
  𝐅𝐚𝐦 𝒞 𝑗 = #structureOn (Family 𝒞 𝑗)

module _ {𝒞 : Category 𝑖} where
  record isFamilyHom (X : Family 𝒞 𝑗) (Y : Family 𝒞 𝑘) (f : ⟨ X ⟩ -> ⟨ Y ⟩) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    field map-■ : ∀{a : ⟨ X ⟩} -> a ■ ⟶ f a ■

  open isFamilyHom {{...}} public

module _ {𝒞 : Category 𝑖} (X : Family 𝒞 𝑗) (Y : Family 𝒞 𝑘) where
  FamilyHom : _
  FamilyHom = _ :& isFamilyHom X Y


instance
  isCategory:Family : ∀{𝒞 : Category 𝑖} -> isCategory {_ , ⨆ 𝑗} (Family 𝒞 𝑗)
  isCategory.Hom isCategory:Family = FamilyHom
  isCategory.isSetoid:Hom isCategory:Family = {!!}
  isCategory.id isCategory:Family = {!!}
  isCategory._◆_ isCategory:Family = {!!}
  isCategory.unit-l-◆ isCategory:Family = {!!}
  isCategory.unit-r-◆ isCategory:Family = {!!}
  isCategory.unit-2-◆ isCategory:Family = {!!}
  isCategory.assoc-l-◆ isCategory:Family = {!!}
  isCategory.assoc-r-◆ isCategory:Family = {!!}
  isCategory._◈_ isCategory:Family = {!!}



