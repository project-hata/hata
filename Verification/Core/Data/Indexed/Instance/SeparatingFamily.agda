
module Verification.Core.Data.Indexed.Instance.SeparatingFamily where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Adjoint
open import Verification.Core.Category.Std.Functor.Adjoint.Property.Base
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Data.Universe.Instance.Category

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Xiix




module _ {π : Category π} {{_ : hasSeparatingFamily π π}} {{_ : hasInitial π}}
         {I : π° π} {{_ : isDiscrete I}}
         where

  Separator-ππ± : π° _
  Separator-ππ± = (Separator Γ I)

  Fam : (i j : I) -> π° π
  Fam i j = i β£ j

  separator-ππ± : Separator-ππ± -> ππ± I π
  separator-ππ± (s , i) = π₯πβ i (separator s)

  instance
    isSeparatingFamily:sep : isSeparatingFamily (ππ± I π) separator-ππ±
    isSeparatingFamily.separate isSeparatingFamily:sep {a = a} {b} Ο Ο p i = P
      where
        P : Ο i βΌ Ο i
        P = separate (Ο i) (Ο i) (Ξ» ΞΎ β
              let p' : free ΞΎ β Ο βΌ free ΞΎ β Ο
                  p' = p (free ΞΎ)

              in destruct-precomp-free p'
            )


  instance
    hasSeparatingFamily:ππ± : hasSeparatingFamily π (ππ± I π)
    hasSeparatingFamily.Separator hasSeparatingFamily:ππ± = Separator-ππ±
    hasSeparatingFamily.separator hasSeparatingFamily:ππ± = separator-ππ±
    hasSeparatingFamily.isSeparatingFamily:seperators hasSeparatingFamily:ππ± = it




