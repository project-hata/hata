
module Verification.Core.Category.StdMonoidal.Para.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Category.StdMonoidal.Category.Definition



module _ (š : Monoidal š) where
  record Para : š° š where
    field āØ_ā© : āØ š ā©

  open Para public

  macro ššš«š = #structureOn Para

module _ {š : Monoidal š} where
  record Hom-ššš«š (A B : Para š) : š° š where
    constructor incl
    field {Param} : āØ š ā©
    field āØ_ā© : āØ A ā© ā Param ā¶ āØ B ā©

  open Hom-ššš«š public


  module _ {A B : Para š} where
    record _ā¼-Hom-ššš«š_ (f g : Hom-ššš«š A B) : š° š where
      constructor _,_
      field iparam : Param g ā Param f
      field arr : (id āāā āØ iparam ā©) ā āØ f ā© ā¼ āØ g ā©

    open _ā¼-Hom-ššš«š_

    refl-ā¼-Hom-ššš«š : ā{f} -> f ā¼-Hom-ššš«š f
    refl-ā¼-Hom-ššš«š {f} = refl-ā , functoriality-id-ā ā refl ā unit-l-ā

    instance
      isSetoid:Hom-ššš«š : isSetoid (Hom-ššš«š A B)
      isSetoid:Hom-ššš«š = isSetoid:byDef _ā¼-Hom-ššš«š_ refl-ā¼-Hom-ššš«š {!!} {!!}

  id-ššš«š : ā{A : Para š} -> Hom-ššš«š A A
  id-ššš«š = incl fĻ

  infixl 50 _ā-ššš«š_
  _ā-ššš«š_ : ā{A B C : Para š} -> Hom-ššš«š A B -> Hom-ššš«š B C -> Hom-ššš«š A C
  _ā-ššš«š_ {A} {B} {C} f g =
    let h : āØ A ā© ā (Param f ā Param g) ā¶ āØ C ā©
        h = bĪ± ā (āØ f ā© āāā id) ā āØ g ā©
    in incl h

  unit-l-ā-ššš«š : ā{A B : Para š} -> {f : Hom-ššš«š A B} -> id-ššš«š ā-ššš«š f ā¼ f
  unit-l-ā-ššš«š {f = f} =  sym-ā iĪ» , P
    where
      P : (id āāā āØ sym-ā iĪ» ā©) ā (bĪ± ā (fĻ āāā id) ā āØ f ā©) ā¼ āØ f ā©
      P = {!!}

  instance
    isCategory:ššš«š : isCategory (ššš«š š)
    isCategory.Hom isCategory:ššš«š = Hom-ššš«š
    isCategory.isSetoid:Hom isCategory:ššš«š = it
    isCategory.id isCategory:ššš«š = id-ššš«š
    isCategory._ā_ isCategory:ššš«š = _ā-ššš«š_
    isCategory.unit-l-ā isCategory:ššš«š = unit-l-ā-ššš«š
    isCategory.unit-r-ā isCategory:ššš«š = {!!}
    isCategory.unit-2-ā isCategory:ššš«š = {!!}
    isCategory.assoc-l-ā isCategory:ššš«š = {!!}
    isCategory.assoc-r-ā isCategory:ššš«š = {!!}
    isCategory._ā_ isCategory:ššš«š = {!!}



