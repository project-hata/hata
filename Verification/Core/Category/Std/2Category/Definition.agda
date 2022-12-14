
module Verification.Core.Category.Std.2Category.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Functor.Constant
-- open import Verification.Core.Category.Std.Functor.Instance.Category
-- open import Verification.Core.Category.Std.Natural.Definition
-- open import Verification.Core.Category.Std.Natural.Instance.Setoid
-- open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Setoid.As.Category
-- open import Verification.Core.Category.Std.Groupoid.As.Setoid
-- open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Groupoid.Definition
-- open import Verification.Core.Category.Std.Category.Construction.Core
-- open import Verification.Core.Setoid.Instance.Category



record is2Category {๐ : ๐ ^ 2} {๐} (๐ : Category ๐) : ๐ฐ (๐ ๏ฝค ๐ โบ) where
  field cell : โ(a b : โจ ๐ โฉ) -> isCategory {๐} (a โถ b)

  Cell : โ(a b : โจ ๐ โฉ) -> Category _
  Cell a b = a โถแต b since cell a b

  Comp : โ{a b c} -> (Cell a b ร Cell b c) -> (a โถ c)
  Comp = ฮป (f , g) -> f โ g

  Id : โ{a : โจ ๐ โฉ} -> โจ โค-๐๐๐ญ {๐ โ 0 , ๐ โ 0 โฏ 1} โฉ -> a โถ a
  Id = ฮป _ -> id

  field isFunctor:Comp : โ{a b c} -> isFunctor (Cell a b ร-๐๐๐ญ Cell b c) (Cell a c) Comp
  field isFunctor:Id : โ{a} -> isFunctor โค-๐๐๐ญ (Cell a a) Id


module _ (๐ : ๐ ^ 5) where
  2Category = Category (๐ โ 0 โฏ 2) :& is2Category {๐ โ 3 โฏ 4}



