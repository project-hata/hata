
module Verification.Core.Category.StdMonoidal.Monoid.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition

open import Verification.Core.Category.StdMonoidal.Category.Definition



module _ (š : Monoidal š) where

  record Mon : š° š where
    field El : āØ š ā©
    field mult : El ā El ā¶ El
    field unit : ident ā¶ El
    field unit-l-mult : bĪ» ā (unit āāā id) ā mult ā¼ id
    field unit-r-mult : bĻ ā (id āāā unit) ā mult ā¼ id
    field assoc-mult : (mult āāā id) ā mult ā¼ fĪ± ā (id āāā mult) ā mult

  open Mon public
  -- open Mon public using (El)
  -- open Mon {{...}} public hiding (El)

  macro ššØš§ = #structureOn Mon

module _ {š : Monoidal š} where
  record Hom-ššØš§ (M N : Mon š) : š° š where
    field Fun : El M ā¶ El N
    field pres-unit : unit M ā Fun ā¼ unit N
    field pres-mult : mult M ā Fun ā¼ (Fun āāā Fun) ā mult N

  open Hom-ššØš§ public

  module _ {M N : Mon š} where
    record _ā¼-Hom-ššØš§_ (f g : Hom-ššØš§ M N) : š° š where
      constructor incl
      field āØ_ā© : Fun f ā¼ Fun g

    instance
      isSetoid:Hom-ššØš§ : isSetoid (Hom-ššØš§ M N)
      isSetoid:Hom-ššØš§ = isSetoid:byDef _ā¼-Hom-ššØš§_ (incl refl) {!!} {!!}

  id-ššØš§ : ā{M} -> Hom-ššØš§ M M
  id-ššØš§ = record
    { Fun = id
    ; pres-unit = unit-r-ā
    ; pres-mult = {!!}
    }

  instance
    isCategory:ššØš§ : isCategory (ššØš§ š)
    isCategory.Hom isCategory:ššØš§ = Hom-ššØš§
    isCategory.isSetoid:Hom isCategory:ššØš§ = it
    isCategory.id isCategory:ššØš§ = id-ššØš§
    isCategory._ā_ isCategory:ššØš§ = {!!}
    isCategory.unit-l-ā isCategory:ššØš§ = {!!}
    isCategory.unit-r-ā isCategory:ššØš§ = {!!}
    isCategory.unit-2-ā isCategory:ššØš§ = {!!}
    isCategory.assoc-l-ā isCategory:ššØš§ = {!!}
    isCategory.assoc-r-ā isCategory:ššØš§ = {!!}
    isCategory._ā_ isCategory:ššØš§ = {!!}




