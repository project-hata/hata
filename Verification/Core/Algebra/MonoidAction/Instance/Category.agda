
module Verification.Core.Algebra.MonoidAction.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Instance.Category
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Opposite

_-๐๐๐ญแต : โ{๐} -> (M : (Monoid ๐ ร-๐ฐ (๐ ^ 2))) -> ๐ฐ _
_-๐๐๐ญแต (M , ๐) = Acted M ๐

macro
  _-๐๐๐ญ : โ{๐} -> (M : (Monoid ๐ ร-๐ฐ (๐ ^ 2))) -> _
  _-๐๐๐ญ (M , ๐) = #structureOn ((M , ๐)-๐๐๐ญแต)

module _ {M : Monoid ๐} where
  record isActedHom (A B : (M , ๐)-๐๐๐ญ) (f : โจ A โฉ -> โจ B โฉ) : ๐ฐ (๐ ๏ฝค ๐) where
    field preserve-โท : โ{m : โจ M โฉ} {a : โจ A โฉ} -> f (m โท a) โผ m โท f a

  module _ (A B : (M , ๐)-๐๐๐ญ) where
    ActedHom = _ :& isActedHom A B

  module _ {A B : (M , ๐)-๐๐๐ญ} where
    record _โผ-ActedHom_ (f g : ActedHom A B) : ๐ฐ (๐ ๏ฝค ๐) where
      constructor incl
      field โจ_โฉ : โจ f โฉ โผ โจ g โฉ

    instance
      isSetoid:ActedHom : isSetoid (ActedHom A B)
      isSetoid:ActedHom = isSetoid:byDef _โผ-ActedHom_ (incl refl) {!!} {!!}

  instance
    isCategory:-๐๐๐ญ : isCategory ((M , ๐)-๐๐๐ญ)
    isCategory.Hom isCategory:-๐๐๐ญ = ActedHom
    isCategory.isSetoid:Hom isCategory:-๐๐๐ญ = it
    isCategory.id isCategory:-๐๐๐ญ = {!!}
    isCategory._โ_ isCategory:-๐๐๐ญ = {!!}
    isCategory.unit-l-โ isCategory:-๐๐๐ญ = {!!}
    isCategory.unit-r-โ isCategory:-๐๐๐ญ = {!!}
    isCategory.unit-2-โ isCategory:-๐๐๐ญ = {!!}
    isCategory.assoc-l-โ isCategory:-๐๐๐ญ = {!!}
    isCategory.assoc-r-โ isCategory:-๐๐๐ญ = {!!}
    isCategory._โ_ isCategory:-๐๐๐ญ = {!!}

module _ ๐ {๐} where

  โฃแต-๐๐๐ญ : ๐๐จ๐ง ๐ -> Category _
  โฃแต-๐๐๐ญ M = (M , ๐)-๐๐๐ญ

  macro
    โฃ-๐๐๐ญ = #structureOn โฃแต-๐๐๐ญ

instance
  isFunctor:โฃ-๐๐๐ญ : isFunctor (๐๐จ๐ง ๐ แตแต) (๐๐๐ญ _) (โฃแต-๐๐๐ญ ๐)
  isFunctor:โฃ-๐๐๐ญ = {!!}


-- the category of all actions
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Op.Definition

module _ ๐ ๐ where
  ๐๐๐ญแต = โจแตแตแต (โฃ-๐๐๐ญ ๐ {๐})

  macro
    ๐๐๐ญ = #structureOn ๐๐๐ญแต


-- fibration notation

record isFibrationBase ๐ (๐ : Category ๐) : ๐ฐ (๐ ๏ฝค ๐ โบ) where
  field โฃ : Functor (๐ แตแต) (๐๐๐ญ ๐)

open isFibrationBase {{...}} public

module _ {๐ : Category ๐} {{_ : isFibrationBase ๐ ๐}} where
  _* : โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> โจ โฃ โฉ b โถ โจ โฃ โฉ a
  f * = map f


  -- _-๐๐๐ญ : Category _
  -- _-๐๐๐ญ = {!!}

-- โจฝ M A

-- โพ 	โงโฉ โฉ โฆก 	โฆฐ 	โฆฑ 	โฆฒ 	โฆณ 	โฆด 	โฆต 	โฆถ 	โฆท 	โฆธ 	โฆน 	โฆบ 	โฆป 	โฆผ 	โฆฝโฆพ 	โฆฟ ๏นกโฌข 	โฌฃโฌกโ

-- โฃแต-๐๐๐ญ : ๐๐จ๐ง ๐ -> Category _



