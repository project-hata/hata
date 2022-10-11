
module Verification.Core.Algebra.MonoidAction.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Instance.Category
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Opposite

_-𝐀𝐜𝐭ᵘ : ∀{𝑖} -> (M : (Monoid 𝑖 ×-𝒰 (𝔏 ^ 2))) -> 𝒰 _
_-𝐀𝐜𝐭ᵘ (M , 𝑗) = Acted M 𝑗

macro
  _-𝐀𝐜𝐭 : ∀{𝑖} -> (M : (Monoid 𝑖 ×-𝒰 (𝔏 ^ 2))) -> _
  _-𝐀𝐜𝐭 (M , 𝑗) = #structureOn ((M , 𝑗)-𝐀𝐜𝐭ᵘ)

module _ {M : Monoid 𝑖} where
  record isActedHom (A B : (M , 𝑗)-𝐀𝐜𝐭) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    field preserve-↷ : ∀{m : ⟨ M ⟩} {a : ⟨ A ⟩} -> f (m ↷ a) ∼ m ↷ f a

  module _ (A B : (M , 𝑗)-𝐀𝐜𝐭) where
    ActedHom = _ :& isActedHom A B

  module _ {A B : (M , 𝑗)-𝐀𝐜𝐭} where
    record _∼-ActedHom_ (f g : ActedHom A B) : 𝒰 (𝑖 ､ 𝑗) where
      constructor incl
      field ⟨_⟩ : ⟨ f ⟩ ∼ ⟨ g ⟩

    instance
      isSetoid:ActedHom : isSetoid (ActedHom A B)
      isSetoid:ActedHom = isSetoid:byDef _∼-ActedHom_ (incl refl) {!!} {!!}

  instance
    isCategory:-𝐀𝐜𝐭 : isCategory ((M , 𝑗)-𝐀𝐜𝐭)
    isCategory.Hom isCategory:-𝐀𝐜𝐭 = ActedHom
    isCategory.isSetoid:Hom isCategory:-𝐀𝐜𝐭 = it
    isCategory.id isCategory:-𝐀𝐜𝐭 = {!!}
    isCategory._◆_ isCategory:-𝐀𝐜𝐭 = {!!}
    isCategory.unit-l-◆ isCategory:-𝐀𝐜𝐭 = {!!}
    isCategory.unit-r-◆ isCategory:-𝐀𝐜𝐭 = {!!}
    isCategory.unit-2-◆ isCategory:-𝐀𝐜𝐭 = {!!}
    isCategory.assoc-l-◆ isCategory:-𝐀𝐜𝐭 = {!!}
    isCategory.assoc-r-◆ isCategory:-𝐀𝐜𝐭 = {!!}
    isCategory._◈_ isCategory:-𝐀𝐜𝐭 = {!!}

module _ 𝑗 {𝑖} where

  ⏣ᵘ-𝐀𝐜𝐭 : 𝐌𝐨𝐧 𝑖 -> Category _
  ⏣ᵘ-𝐀𝐜𝐭 M = (M , 𝑗)-𝐀𝐜𝐭

  macro
    ⏣-𝐀𝐜𝐭 = #structureOn ⏣ᵘ-𝐀𝐜𝐭

instance
  isFunctor:⏣-𝐀𝐜𝐭 : isFunctor (𝐌𝐨𝐧 𝑖 ᵒᵖ) (𝐂𝐚𝐭 _) (⏣ᵘ-𝐀𝐜𝐭 𝑗)
  isFunctor:⏣-𝐀𝐜𝐭 = {!!}


-- the category of all actions
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Op.Definition

module _ 𝑖 𝑗 where
  𝐀𝐜𝐭ᵘ = ⨊ᵒᵖᵘ (⏣-𝐀𝐜𝐭 𝑗 {𝑖})

  macro
    𝐀𝐜𝐭 = #structureOn 𝐀𝐜𝐭ᵘ


-- fibration notation

record isFibrationBase 𝑗 (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field ⏣ : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)

open isFibrationBase {{...}} public

module _ {𝒞 : Category 𝑖} {{_ : isFibrationBase 𝑗 𝒞}} where
  _* : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> ⟨ ⏣ ⟩ b ⟶ ⟨ ⏣ ⟩ a
  f * = map f


  -- _-𝐀𝐜𝐭 : Category _
  -- _-𝐀𝐜𝐭 = {!!}

-- ⨽ M A

-- ⊾ 	∧⩜ ⩟ ⦡ 	⦰ 	⦱ 	⦲ 	⦳ 	⦴ 	⦵ 	⦶ 	⦷ 	⦸ 	⦹ 	⦺ 	⦻ 	⦼ 	⦽⦾ 	⦿ ﹡⬢ 	⬣⬡⎔

-- ⏣ᵘ-𝐀𝐜𝐭 : 𝐌𝐨𝐧 𝑖 -> Category _



