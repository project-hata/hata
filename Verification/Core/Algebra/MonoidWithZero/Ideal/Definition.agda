
module Verification.Core.Algebra.MonoidWithZero.Ideal.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Subsetoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidAction.Definition


-- TODO: Give this a proper name, and move somewhere general
module _ {A : π° π} (P : A -> π° π) where
  βπ«_ : A -> Prop π
  βπ«_ a = β£ P a β£
-- end


record isIdeal {π : π ^ 2} (A : Monoidβ π) (P : π« β¨ A β© :& isSubsetoid) : π° π where
  field ideal-β : β β P
  field ideal-r-β : β{a : β¨ A β©} -> a β P -> β b -> (a β b) β P
open isIdeal {{...}} public


module _ (A : ππ¨π§β π) where
  Idealα΅ : π° _
  Idealα΅ = _ :& isIdeal A

  macro Ideal = #structureOn Idealα΅


module _ {A : Monoidβ π} where

  private
    _βΌ-Ideal_ : Ideal A -> Ideal A -> π° _
    _βΌ-Ideal_ = _βΌ-hasU_

  instance
    isSetoid:Ideal : isSetoid (Ideal A)
    isSetoid:Ideal = isSetoid:hasU

  instance
    isPreorder:Ideal : isPreorder _ (Ideal A)
    isPreorder._β€_ isPreorder:Ideal I J = β¨ I β© β€ β¨ J β©
    isPreorder.reflexive isPreorder:Ideal = Ξ» a β reflexive
    isPreorder._β‘_ isPreorder:Ideal = Ξ» p q a β p a β‘ q a
    isPreorder.transp-β€ isPreorder:Ideal = {!!}

  instance
    isPartialorder:Ideal : isPartialorder (Ideal A)
    isPartialorder:Ideal = record
      { antisym = Ξ» p q -> incl $ antisym p q
      }



----------------------------------------------------------
-- A property of elements

module _ {A : π° _} {{_ : Monoidβ π on A}} where
  isZeroOrEpi : A -> π° _
  isZeroOrEpi a = (a βΌ β) +-π° ((a β β) Γ-π° β{b c : A} -> a β b βΌ a β c -> b βΌ c)

