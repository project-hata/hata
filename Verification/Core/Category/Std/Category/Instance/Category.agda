
module Verification.Core.Category.Std.Category.Instance.Category where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Instance.2Category

open import Verification.Core.Category.Std.Category.Instance.CategoryLike public


all : ๐ ^ 3 -> ๐
all (i , j , k) = i โ j โ k



instance
  isCategory:Category : โ{๐ : ๐ ^ 3} -> isCategory (Category ๐)
  isCategory.Hom isCategory:Category = Functor
  isCategory.isSetoid:Hom (isCategory:Category {๐}) = it
  isCategory.id isCategory:Category = id-๐๐๐ญ
  isCategory._โ_ isCategory:Category F G = (F โ-๐๐๐ญ G)
  isCategory.unit-l-โ isCategory:Category = unit-l-โ-๐๐๐ญ
  isCategory.unit-r-โ isCategory:Category = unit-r-โ-๐๐๐ญ
  isCategory.unit-2-โ isCategory:Category = unit-r-โ-๐๐๐ญ
  isCategory.assoc-l-โ isCategory:Category {f = f} {g} {h} = assoc-l-โ-๐๐๐ญ {F = f} {g} {h}
  isCategory.assoc-r-โ isCategory:Category {f = f} {g} {h} = assoc-l-โ-๐๐๐ญ {F = f} {g} {h} โปยน
  isCategory._โ_ isCategory:Category = _โโโ-๐๐๐ญ_

instance
  isSetoid:Category : isSetoid (๐๐๐ญ ๐)
  isSetoid:Category = isSetoid:byCategory


open import Verification.Core.Category.Std.2Category.Definition
open import Verification.Core.Category.Std.Functor.Constant

instance
  is2Category:๐๐๐ญ : is2Category (๐๐๐ญ ๐)
  is2Category.cell is2Category:๐๐๐ญ = ฮป a b -> isCategory:Functor
  is2Category.isFunctor:Comp is2Category:๐๐๐ญ = isFunctor:Comp-๐๐๐ญ
  is2Category.isFunctor:Id is2Category:๐๐๐ญ = isFunctor:const


