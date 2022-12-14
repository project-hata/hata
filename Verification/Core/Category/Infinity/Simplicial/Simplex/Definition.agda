
module Verification.Core.Category.Infinity.Simplicial.Simplex.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Finite.Definition

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder
open import Verification.Core.Category.Std.Category.Definition

record isSimplex (A : π° _ :& (is Finite _) :, (is TotalorderβΊ π)) : π° π where
instance
  isSimplex:Anything : β{A : π° π}
                       -> {{_ : isDiscrete' A}} -> {{_ : isFinite β² A β²}}
                       -> {{_ : isSetoid π A }}
                       -> {{_ : isPreorder π β² A β² }}
                       -> {{_ : isPartialorder β² A β² }}
                       -> {{_ : isTotalorderβΊ β² A β²}}
                       -> isSimplex β² A β²
  isSimplex:Anything = record {}

-- isSimplex : (A : π° _ :& (is Finite _) :, (is TotalorderβΊ π)) : π° π where

Simplex : β(π) -> π° _
Simplex π = _ :& isSimplex {π = π}

instance
  isCategory:Simplex : isCategory _ (Simplex π)
  isCategory.Hom' isCategory:Simplex A B = Monotone β² β¨ A β© β² β² β¨ B β© β²
  isSetoid._βΌ'_ (isCategory.isSetoid:Hom isCategory:Simplex) f g = β¨ f β© βΌ' β¨ g β©
  isSetoid.isEquivRel:βΌ (isCategory.isSetoid:Hom isCategory:Simplex) = {!!}
  isCategory.id isCategory:Simplex = {!!}
  isCategory._β_ isCategory:Simplex = {!!}
  isCategory.unit-l-β isCategory:Simplex = {!!}
  isCategory.unit-r-β isCategory:Simplex = {!!}
  isCategory.unit-2-β isCategory:Simplex = {!!}
  isCategory.assoc-l-β isCategory:Simplex = {!!}
  isCategory.assoc-r-β isCategory:Simplex = {!!}
  isCategory._β_ isCategory:Simplex = {!!}


βL : β π -> Category _
βL π = β² Simplex π β²




