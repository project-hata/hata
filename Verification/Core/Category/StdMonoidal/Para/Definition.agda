
module Verification.Core.Category.StdMonoidal.Para.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Category.StdMonoidal.Category.Definition



module _ (𝒞 : Monoidal 𝑖) where
  record Para : 𝒰 𝑖 where
    field ⟨_⟩ : ⟨ 𝒞 ⟩

  open Para public

  macro 𝐏𝐚𝐫𝐚 = #structureOn Para

module _ {𝒞 : Monoidal 𝑖} where
  record Hom-𝐏𝐚𝐫𝐚 (A B : Para 𝒞) : 𝒰 𝑖 where
    constructor incl
    field {Param} : ⟨ 𝒞 ⟩
    field ⟨_⟩ : ⟨ A ⟩ ⊗ Param ⟶ ⟨ B ⟩

  open Hom-𝐏𝐚𝐫𝐚 public


  module _ {A B : Para 𝒞} where
    record _∼-Hom-𝐏𝐚𝐫𝐚_ (f g : Hom-𝐏𝐚𝐫𝐚 A B) : 𝒰 𝑖 where
      constructor _,_
      field iparam : Param g ≅ Param f
      field arr : (id ⇃⊗⇂ ⟨ iparam ⟩) ◆ ⟨ f ⟩ ∼ ⟨ g ⟩

    open _∼-Hom-𝐏𝐚𝐫𝐚_

    refl-∼-Hom-𝐏𝐚𝐫𝐚 : ∀{f} -> f ∼-Hom-𝐏𝐚𝐫𝐚 f
    refl-∼-Hom-𝐏𝐚𝐫𝐚 {f} = refl-≅ , functoriality-id-⊗ ◈ refl ∙ unit-l-◆

    instance
      isSetoid:Hom-𝐏𝐚𝐫𝐚 : isSetoid (Hom-𝐏𝐚𝐫𝐚 A B)
      isSetoid:Hom-𝐏𝐚𝐫𝐚 = isSetoid:byDef _∼-Hom-𝐏𝐚𝐫𝐚_ refl-∼-Hom-𝐏𝐚𝐫𝐚 {!!} {!!}

  id-𝐏𝐚𝐫𝐚 : ∀{A : Para 𝒞} -> Hom-𝐏𝐚𝐫𝐚 A A
  id-𝐏𝐚𝐫𝐚 = incl fρ

  infixl 50 _◆-𝐏𝐚𝐫𝐚_
  _◆-𝐏𝐚𝐫𝐚_ : ∀{A B C : Para 𝒞} -> Hom-𝐏𝐚𝐫𝐚 A B -> Hom-𝐏𝐚𝐫𝐚 B C -> Hom-𝐏𝐚𝐫𝐚 A C
  _◆-𝐏𝐚𝐫𝐚_ {A} {B} {C} f g =
    let h : ⟨ A ⟩ ⊗ (Param f ⊗ Param g) ⟶ ⟨ C ⟩
        h = bα ◆ (⟨ f ⟩ ⇃⊗⇂ id) ◆ ⟨ g ⟩
    in incl h

  unit-l-◆-𝐏𝐚𝐫𝐚 : ∀{A B : Para 𝒞} -> {f : Hom-𝐏𝐚𝐫𝐚 A B} -> id-𝐏𝐚𝐫𝐚 ◆-𝐏𝐚𝐫𝐚 f ∼ f
  unit-l-◆-𝐏𝐚𝐫𝐚 {f = f} =  sym-≅ iλ , P
    where
      P : (id ⇃⊗⇂ ⟨ sym-≅ iλ ⟩) ◆ (bα ◆ (fρ ⇃⊗⇂ id) ◆ ⟨ f ⟩) ∼ ⟨ f ⟩
      P = {!!}

  instance
    isCategory:𝐏𝐚𝐫𝐚 : isCategory (𝐏𝐚𝐫𝐚 𝒞)
    isCategory.Hom isCategory:𝐏𝐚𝐫𝐚 = Hom-𝐏𝐚𝐫𝐚
    isCategory.isSetoid:Hom isCategory:𝐏𝐚𝐫𝐚 = it
    isCategory.id isCategory:𝐏𝐚𝐫𝐚 = id-𝐏𝐚𝐫𝐚
    isCategory._◆_ isCategory:𝐏𝐚𝐫𝐚 = _◆-𝐏𝐚𝐫𝐚_
    isCategory.unit-l-◆ isCategory:𝐏𝐚𝐫𝐚 = unit-l-◆-𝐏𝐚𝐫𝐚
    isCategory.unit-r-◆ isCategory:𝐏𝐚𝐫𝐚 = {!!}
    isCategory.unit-2-◆ isCategory:𝐏𝐚𝐫𝐚 = {!!}
    isCategory.assoc-l-◆ isCategory:𝐏𝐚𝐫𝐚 = {!!}
    isCategory.assoc-r-◆ isCategory:𝐏𝐚𝐫𝐚 = {!!}
    isCategory._◈_ isCategory:𝐏𝐚𝐫𝐚 = {!!}



