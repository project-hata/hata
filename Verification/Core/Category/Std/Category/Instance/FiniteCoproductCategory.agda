
module Verification.Core.Category.Std.Category.Instance.FiniteCoproductCategory where

open import Verification.Conventions
open import Verification.Core.Setoid
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Lift.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Construction.Id
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Construction.Coproduct


module _ {๐ ๐ : ๐๐๐ญ ๐} where
  instance
    isCoproduct:+-๐๐๐ญ : isCoproduct ๐ ๐ (๐ + ๐)
    isCoproduct.ฮนโ isCoproduct:+-๐๐๐ญ = {!!}
    isCoproduct.ฮนโ isCoproduct:+-๐๐๐ญ = {!!}
    isCoproduct.โฆ isCoproduct:+-๐๐๐ญ โฆ = {!!}
    isCoproduct.reduce-ฮนโ isCoproduct:+-๐๐๐ญ = {!!}
    isCoproduct.reduce-ฮนโ isCoproduct:+-๐๐๐ญ = {!!}
    isCoproduct.expand-ฮนโ,ฮนโ isCoproduct:+-๐๐๐ญ = {!!}
    isCoproduct.isSetoidHom:โฆโฆ isCoproduct:+-๐๐๐ญ = {!!}



