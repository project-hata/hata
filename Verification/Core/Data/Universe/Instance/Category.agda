
module Verification.Core.Data.Universe.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Data.Universe.Definition


-- [Hide]
instance
  isSetoid:Function : โ{A B : ๐ฐ ๐} -> isSetoid (A -> B)
  isSetoid:Function = isSetoid:byPath
-- //

-- [Example]
-- | The type |๐ฐ| of types together with functions between
--   them is a category.
instance
  isCategory:๐ฐ : isCategory (๐ฐ ๐)
  isCategory.Hom isCategory:๐ฐ A B = A -> B
  isCategory.isSetoid:Hom isCategory:๐ฐ = isSetoid:Function
  isCategory.id isCategory:๐ฐ = id-๐ฐ
  isCategory._โ_ isCategory:๐ฐ = _โ-๐ฐ_
  isCategory.unit-l-โ isCategory:๐ฐ = refl
  isCategory.unit-r-โ isCategory:๐ฐ = refl
  isCategory.unit-2-โ isCategory:๐ฐ = refl
  isCategory.assoc-l-โ isCategory:๐ฐ = refl
  isCategory.assoc-r-โ isCategory:๐ฐ = refl
  isCategory._โ_ isCategory:๐ฐ p q = ฮป i -> p i โ q i
-- //

-- [Example]
-- | Another, more generic example is the following:
--   Given a category |๐|, inverting the direction
--   of all arrows produces a new category, called the
--   /opposite/ category, and denoted by |๐ แตแต|.

-- //

-- [Hide]
instance
  isSetoid:๐ฐ : isSetoid (๐ฐ ๐)
  isSetoid:๐ฐ = isSetoid:byCategory
-- //

