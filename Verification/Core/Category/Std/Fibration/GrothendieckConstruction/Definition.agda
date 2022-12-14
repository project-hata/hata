
module Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Natural.Instance.Category

-- record hasGrothendieckSum (A : ๐ฐ ๐) (B : ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
--   field โจ : A -> B

-- open hasGrothendieckSum {{...}} public

module _ {๐ : Category ๐} where


  record โจแต (F : Functor ๐ (๐๐๐ญ ๐)) : ๐ฐ ((๐ โ 0) โ (๐ โ 0)) where
    constructor _,_
    field bas : โจ ๐ โฉ
    field fib : โจ โจ F โฉ bas โฉ

  open โจแต public using (bas ; fib)
  -- open โจ {{...}} public using (fib)

  module _ (F : Functor ๐ (๐๐๐ญ ๐)) where
    macro
      โจ = #structureOn (โจแต F)

  -- instance
  --   hasGrothendieckSum:๐๐๐ญ : hasGrothendieckSum (Functor ๐ (๐๐๐ญ ๐)) _
  --   hasGrothendieckSum:๐๐๐ญ = record { โจ = โจ }


  module _ {F : Functor ๐ (๐๐๐ญ ๐)} where
    private
      instance
        isCategory:F : โ{b : โจ ๐ โฉ} -> isCategory (โจ โจ F โฉ b โฉ)
        isCategory:F {b} = of โจ F โฉ b

      instance
        isSetoid:F : โ{b : โจ ๐ โฉ} {x y : โจ โจ F โฉ b โฉ} -> isSetoid (x โถ y)
        isSetoid:F {b} = isSetoid:Hom {{of โจ F โฉ b}}

    record Hom-โจ (a b : โจ F) : ๐ฐ ((๐ โ 1) ๏ฝค (๐ โ 1)) where
      constructor _,_
      field bas : bas a โถ bas b
      field fib : Hom (โจ map bas โฉ (fib a)) (fib b)

    open Hom-โจ public

    module _ {a b : โจ F} where
      record _โผ-Hom-โจ_ (f g : Hom-โจ a b) : ๐ฐ (๐ โ 2 ๏ฝค ๐ โ 2) where
        constructor _,_
        field โผ-bas : bas f โผ bas g
        field โผ-fib : fib f โผ โจ โจ cong-โผ โผ-bas โฉ โฉ _ โ fib g

      instance
        isSetoid:Hom-โจ : isSetoid (Hom-โจ a b)
        isSetoid:Hom-โจ = isSetoid:byDef _โผ-Hom-โจ_ {!!} {!!} {!!}


    instance
      isCategory:โจ : isCategory (โจ F)
      isCategory.Hom isCategory:โจ          = Hom-โจ
      isCategory.isSetoid:Hom isCategory:โจ = isSetoid:Hom-โจ
      isCategory.id isCategory:โจ           = {!!}
      isCategory._โ_ isCategory:โจ          = {!!}
      isCategory.unit-l-โ isCategory:โจ     = {!!}
      isCategory.unit-r-โ isCategory:โจ     = {!!}
      isCategory.unit-2-โ isCategory:โจ     = {!!}
      isCategory.assoc-l-โ isCategory:โจ    = {!!}
      isCategory.assoc-r-โ isCategory:โจ    = {!!}
      isCategory._โ_ isCategory:โจ          = {!!}





