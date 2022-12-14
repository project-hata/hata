
module Verification.Core.Category.Std.Category.Opposite.Strict.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition


-- | For a more general kind of example, consider an arbitrary category |๐|.
--   Then we can construct another category |๐ แตแต| which has the same objects
--   as |๐|, but where the direction of all arrows is reversed.

-- [Definition]
-- | There is a function [..], mapping a category to its opposite. It is defined as:
module _ {๐ : ๐ฐ ๐} {{๐P : isCategory {๐} ๐}} where
  isCategory:แตแต : isCategory ๐
  isCategory.Hom isCategory:แตแต a b = Hom b a
  isCategory.isSetoid:Hom isCategory:แตแต = isSetoid:Hom {{๐P}}
  isCategory.id isCategory:แตแต = id
  isCategory._โ_ isCategory:แตแต f g = g โ f
  isCategory.unit-l-โ isCategory:แตแต = unit-r-โ
  isCategory.unit-r-โ isCategory:แตแต    = unit-l-โ       -- incl โจ unit-l-โ โฉ
  isCategory.unit-2-โ isCategory:แตแต    = unit-2-โ       -- incl โจ unit-2-โ โฉ
  isCategory.assoc-l-โ isCategory:แตแต   = assoc-r-โ      -- incl โจ assoc-r-โ โฉ
  isCategory.assoc-r-โ isCategory:แตแต   = assoc-l-โ      -- incl โจ assoc-l-โ โฉ
  isCategory._โ_ isCategory:แตแต (p) (q) = q โ p -- incl โจ incl q โ incl p โฉ

_แตแต : Category ๐ -> Category ๐
_แตแต ๐ = โจ ๐ โฉ since isCategory:แตแต
  -- where Op : isCategory โจ ๐ โฉ
  --       isCategory.Hom Op a b = Hom b a
  --       isCategory.isSetoid:Hom Op = isSetoid:Hom {{of ๐}}
  --       isCategory.id Op = id
  --       isCategory._โ_ Op f g = g โ f
  --       isCategory.unit-l-โ Op = unit-r-โ
  --       isCategory.unit-r-โ Op    = unit-l-โ       -- incl โจ unit-l-โ โฉ
  --       isCategory.unit-2-โ Op    = unit-2-โ       -- incl โจ unit-2-โ โฉ
  --       isCategory.assoc-l-โ Op   = assoc-r-โ      -- incl โจ assoc-r-โ โฉ
  --       isCategory.assoc-r-โ Op   = assoc-l-โ      -- incl โจ assoc-l-โ โฉ
  --       isCategory._โ_ Op (p) (q) = q โ p -- incl โจ incl q โ incl p โฉ

module _ {๐ : Category ๐} where
  แตแตแตแต : (๐ แตแต แตแต) โก-Str ๐
  แตแตแตแต = refl-โฃ
