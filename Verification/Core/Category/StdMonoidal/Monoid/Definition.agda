
module Verification.Core.Category.StdMonoidal.Monoid.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition

open import Verification.Core.Category.StdMonoidal.Category.Definition



module _ (𝒞 : Monoidal 𝑖) where

  record Mon : 𝒰 𝑖 where
    field El : ⟨ 𝒞 ⟩
    field mult : El ⊗ El ⟶ El
    field unit : ident ⟶ El
    field unit-l-mult : bλ ◆ (unit ⇃⊗⇂ id) ◆ mult ∼ id
    field unit-r-mult : bρ ◆ (id ⇃⊗⇂ unit) ◆ mult ∼ id
    field assoc-mult : (mult ⇃⊗⇂ id) ◆ mult ∼ fα ◆ (id ⇃⊗⇂ mult) ◆ mult

  open Mon public
  -- open Mon public using (El)
  -- open Mon {{...}} public hiding (El)

  macro 𝐌𝐨𝐧 = #structureOn Mon

module _ {𝒞 : Monoidal 𝑖} where
  record Hom-𝐌𝐨𝐧 (M N : Mon 𝒞) : 𝒰 𝑖 where
    field Fun : El M ⟶ El N
    field pres-unit : unit M ◆ Fun ∼ unit N
    field pres-mult : mult M ◆ Fun ∼ (Fun ⇃⊗⇂ Fun) ◆ mult N

  open Hom-𝐌𝐨𝐧 public

  module _ {M N : Mon 𝒞} where
    record _∼-Hom-𝐌𝐨𝐧_ (f g : Hom-𝐌𝐨𝐧 M N) : 𝒰 𝑖 where
      constructor incl
      field ⟨_⟩ : Fun f ∼ Fun g

    instance
      isSetoid:Hom-𝐌𝐨𝐧 : isSetoid (Hom-𝐌𝐨𝐧 M N)
      isSetoid:Hom-𝐌𝐨𝐧 = isSetoid:byDef _∼-Hom-𝐌𝐨𝐧_ (incl refl) {!!} {!!}

  id-𝐌𝐨𝐧 : ∀{M} -> Hom-𝐌𝐨𝐧 M M
  id-𝐌𝐨𝐧 = record
    { Fun = id
    ; pres-unit = unit-r-◆
    ; pres-mult = {!!}
    }

  instance
    isCategory:𝐌𝐨𝐧 : isCategory (𝐌𝐨𝐧 𝒞)
    isCategory.Hom isCategory:𝐌𝐨𝐧 = Hom-𝐌𝐨𝐧
    isCategory.isSetoid:Hom isCategory:𝐌𝐨𝐧 = it
    isCategory.id isCategory:𝐌𝐨𝐧 = id-𝐌𝐨𝐧
    isCategory._◆_ isCategory:𝐌𝐨𝐧 = {!!}
    isCategory.unit-l-◆ isCategory:𝐌𝐨𝐧 = {!!}
    isCategory.unit-r-◆ isCategory:𝐌𝐨𝐧 = {!!}
    isCategory.unit-2-◆ isCategory:𝐌𝐨𝐧 = {!!}
    isCategory.assoc-l-◆ isCategory:𝐌𝐨𝐧 = {!!}
    isCategory.assoc-r-◆ isCategory:𝐌𝐨𝐧 = {!!}
    isCategory._◈_ isCategory:𝐌𝐨𝐧 = {!!}




