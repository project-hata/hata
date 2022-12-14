
module Verification.Core.Algebra.Torsor.Definition where

open import Verification.Conventions
-- open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Algebra.MonoidAction.Instance.Category
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Op.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full2

-- record isTorsor (M : Monoid ๐) (T : Acted M ๐) : ๐ฐ (๐ ๏ฝค ๐) where

module _ (M : Monoid ๐) where
  isTorsor : โ{๐} -> Acted M ๐ -> _
  isTorsor = isFreeActed :, isTransitiveActed

  Torsor : โ ๐ -> _
  Torsor ๐ = _ :& isTorsor {๐}


-- _-๐๐จ๐ซ๐ฌ : (Monoid ๐ ร-๐ฐ ๐ ^ 2) -> ๐ฐ _
-- _-๐๐จ๐ซ๐ฌ (M , ๐) = Torsor M ๐

module _ ๐ ๐ where
  record ๐๐จ๐ซ๐ฌแต : ๐ฐ (๐ โบ ๏ฝค ๐ โบ) where
    constructor _,_
    field fst : Monoid ๐
    field snd : Torsor fst ๐

  macro ๐๐จ๐ซ๐ฌ = #structureOn ๐๐จ๐ซ๐ฌแต


ฮนแต-๐๐จ๐ซ๐ฌ : ๐๐จ๐ซ๐ฌ ๐ ๐ -> ๐๐๐ญ _ _
ฮนแต-๐๐จ๐ซ๐ฌ (M , T) = M , โณ T

module _ {๐ ๐} where
  instance
    isCategory:๐๐จ๐ซ๐ฌ : isCategory (๐๐จ๐ซ๐ฌ ๐ ๐)
    isCategory:๐๐จ๐ซ๐ฌ = isCategory:FullSubcategory (ฮนแต-๐๐จ๐ซ๐ฌ {๐} {๐})

-- ๐๐จ๐ซ๐ฌแต : โ ๐ ๐ -> ๐ฐ _
-- ๐๐จ๐ซ๐ฌแต ๐ ๐ = FullSubcategory (๐๐๐ญ _ _) (ฮนแต-๐๐จ๐ซ๐ฌ {๐} {๐})



