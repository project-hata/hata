
module Verification.Core.Algebra.Module.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Abelian.Instance.Category
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Module.Definition
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Category.Opposite



_-๐๐จ๐แต : โ{๐} -> (_ : Ring ๐ ร-๐ฐ ๐ ^ 2) -> ๐ฐ _
_-๐๐จ๐แต (R , ๐) = Module R ๐

macro
  _-๐๐จ๐ : โ{๐} -> (_ : Ring ๐ ร-๐ฐ ๐ ^ 2) -> _
  _-๐๐จ๐ (R , ๐) = #structureOn ((R , ๐)-๐๐จ๐แต)


module _ {R : Ring ๐} where
  record isModuleHom (A B : (R , ๐)-๐๐จ๐) (f : AbelianHom (โณ A) (โณ B) ) : ๐ฐ (๐ ๏ฝค ๐) where
    field preserve-โท : โ{m : โจ R โฉ} {a : โจ A โฉ} -> โจ f โฉ (m โท a) โผ m โท โจ f โฉ a

  module _ (A B : (R , ๐)-๐๐จ๐) where
    ModuleHom = _ :& isModuleHom A B

  module _ {A B : (R , ๐)-๐๐จ๐} where
    record _โผ-ModuleHom_ (f g : ModuleHom A B) : ๐ฐ (๐ ๏ฝค ๐) where
      constructor incl
      field โจ_โฉ : โจ f โฉ โผ โจ g โฉ

    instance
      isSetoid:ModuleHom : isSetoid (ModuleHom A B)
      isSetoid:ModuleHom = isSetoid:byDef _โผ-ModuleHom_ (incl refl) {!!} {!!}

  instance
    isCategory:-๐๐จ๐ : isCategory ((R , ๐)-๐๐จ๐)
    isCategory.Hom isCategory:-๐๐จ๐ = ModuleHom
    isCategory.isSetoid:Hom isCategory:-๐๐จ๐ = it
    isCategory.id isCategory:-๐๐จ๐ = {!!}
    isCategory._โ_ isCategory:-๐๐จ๐ = {!!}
    isCategory.unit-l-โ isCategory:-๐๐จ๐ = {!!}
    isCategory.unit-r-โ isCategory:-๐๐จ๐ = {!!}
    isCategory.unit-2-โ isCategory:-๐๐จ๐ = {!!}
    isCategory.assoc-l-โ isCategory:-๐๐จ๐ = {!!}
    isCategory.assoc-r-โ isCategory:-๐๐จ๐ = {!!}
    isCategory._โ_ isCategory:-๐๐จ๐ = {!!}


