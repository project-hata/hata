
module Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Op.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Natural.Instance.Category

-- record hasGrothendieckSumOp (A : ๐ฐ ๐) (B : ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
--   field โจแตแต : A -> B

-- open hasGrothendieckSumOp {{...}} public

module _ {๐ : Category ๐} where


  record โจแตแตแต (F : Functor (๐ แตแต) (๐๐๐ญ ๐)) : ๐ฐ ((๐ โ 0) โ (๐ โ 0)) where
    constructor _,_
    field base : โจ ๐ โฉ
    field fib : โจ โจ F โฉ base โฉ

  open โจแตแตแต public

  module _ (F : Functor (๐ แตแต) (๐๐๐ญ ๐)) where
    macro
      โจแตแต = #structureOn (โจแตแตแต F)

  -- instance
  --   hasGrothendieckSumOp:๐๐๐ญ : hasGrothendieckSumOp (Functor (๐ แตแต) (๐๐๐ญ ๐)) _
  --   hasGrothendieckSumOp:๐๐๐ญ = record { โจแตแต = โจแตแต }


  module _ {F : Functor (๐ แตแต) (๐๐๐ญ ๐)} where
    private
      instance
        isCategory:F : โ{b : โจ ๐ โฉ} -> isCategory (โจ โจ F โฉ b โฉ)
        isCategory:F {b} = of โจ F โฉ b

      instance
        isSetoid:F : โ{b : โจ ๐ โฉ} {x y : โจ โจ F โฉ b โฉ} -> isSetoid (x โถ y)
        isSetoid:F {b} = isSetoid:Hom {{of โจ F โฉ b}}

    record Hom-โจแตแต (a b : โจแตแต F) : ๐ฐ ((๐ โ 1) ๏ฝค (๐ โ 1)) where
      constructor _,_
      field base : base a โถ base b
      field fib : Hom (fib a) (โจ map base โฉ (fib b))

    open Hom-โจแตแต public

    module _ {a b : โจแตแต F} where
      record _โผ-Hom-โจแตแต_ (f g : Hom-โจแตแต a b) : ๐ฐ (๐ โ 2 ๏ฝค ๐ โ 2) where
        constructor _,_
        field โผ-base : base f โผ base g
        field โผ-fib : (fib f) โ (โจ โจ cong-โผ โผ-base โฉ โฉ _) โผ fib g

      instance
        isSetoid:Hom-โจแตแต : isSetoid (Hom-โจแตแต a b)
        isSetoid:Hom-โจแตแต = isSetoid:byDef _โผ-Hom-โจแตแต_ {!!} {!!} {!!}

    id-โจแตแต : โ{a : โจแตแต F} -> Hom-โจแตแต a a
    id-โจแตแต = id , โจ inverse-โ (of functoriality-id) โฉ _

    _โ-โจแตแต_ : โ{a b c : โจแตแต F} -> Hom-โจแตแต a b -> Hom-โจแตแต b c -> Hom-โจแตแต a c
    _โ-โจแตแต_ (f , fโจ) (g , gโจ) = f โ g , fโจ โ (mapOf (mapOf F f) gโจ โ โจ inverse-โ (of functoriality-โ) โฉ _)


    instance
      isCategory:โจแตแต : isCategory (โจแตแต F)
      isCategory.Hom isCategory:โจแตแต          = Hom-โจแตแต
      isCategory.isSetoid:Hom isCategory:โจแตแต = isSetoid:Hom-โจแตแต
      isCategory.id isCategory:โจแตแต           = id-โจแตแต
      isCategory._โ_ isCategory:โจแตแต          = _โ-โจแตแต_
      isCategory.unit-l-โ isCategory:โจแตแต     = {!!}
      isCategory.unit-r-โ isCategory:โจแตแต     = {!!}
      isCategory.unit-2-โ isCategory:โจแตแต     = {!!}
      isCategory.assoc-l-โ isCategory:โจแตแต    = {!!}
      isCategory.assoc-r-โ isCategory:โจแตแต    = {!!}
      isCategory._โ_ isCategory:โจแตแต          = {!!}



