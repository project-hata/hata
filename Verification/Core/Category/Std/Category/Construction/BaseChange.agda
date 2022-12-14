
module Verification.Core.Category.Std.Category.Construction.BaseChange where

open import Verification.Conventions
open import Verification.Core.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.CategoryLike
open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Category.Construction.Id
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Instance.Category
-- open import Verification.Core.Category.Std.Morphism.Iso

module _ {๐๐โ : ๐} where
  ๐๐ : ๐ ^ 3
  ๐๐ = ๐๐โ , ๐๐โ , ๐๐โ
  module _ {๐ : Category ๐๐} {๐ : Category ๐๐} where

    module _ (f : Functor ๐ ๐) where
      -- pbแต : (๐๐ฎ๐ง๐ ๐ (๐๐๐ญ ๐)) -> (๐๐ฎ๐ง๐ ๐ (๐๐๐ญ ๐))
      -- pbแต F = f โ-๐๐๐ญ F

      -- pb : Functor (๐๐ฎ๐ง๐ ๐ (๐๐๐ญ ๐)) (๐๐ฎ๐ง๐ ๐ (๐๐๐ญ ๐))
      -- pb = pbแต since {!!}


      module _ (F : ๐๐ฎ๐ง๐ ๐ (๐๐๐ญ ๐๐)) where

        record Cโแต (d : โจ ๐ โฉ) : ๐ฐ (๐๐) where
          constructor _at_,_
          field pt : โจ ๐ โฉ
          field fst : โจ โจ F โฉ pt โฉ
          field snd : โจ f โฉ pt โถ d

        open Cโแต public

        module _ (d : โจ ๐ โฉ) where
          macro Cโ = #structureOn (Cโแต d)

        module _ {d : โจ ๐ โฉ} where

          record Hom-Cโ (a b : Cโ d) : ๐ฐ ๐๐ where
            constructor _at_,_
            field ptmap : pt a โถ pt b
            field fst : Hom {{of โจ F โฉ (pt b)}} (โจ map ptmap โฉ (fst a)) (fst b)
            field snd : map ptmap โ snd b โผ snd a

          open Hom-Cโ public

          id-Cโ : โ{a : Cโ d} -> Hom-Cโ a a
          id-Cโ {a} = id at fst' , {!!}
            where
              -- open isCategory (of (โจ F โฉ (pt a)))
              ida : Hom {{of (โจ F โฉ (pt a))}} (fst a) (fst a)
              ida = id {{of (โจ F โฉ (pt a))}}
                -- where open isCategory (of (โจ F โฉ (pt a)))

              -- p0 : โ x -> โจ mapOf F (id {a = pt a}) โฉ x โ x
              -- p0 x = {!โจ functoriality-id {{of F}}!}

              fst' : Hom {{of โจ F โฉ (pt a)}} (โจ map id โฉ (fst a)) (fst a)
              fst' = {!!}

          -- Hom-Cโ : Cโ d -> Cโ d -> ๐ฐ ๐๐
          -- Hom-Cโ = {!!}

          instance
            isCategory:Cโ : isCategory (Cโ d)
            isCategory.Hom isCategory:Cโ = {!!}
            isCategory.isSetoid:Hom isCategory:Cโ = {!!}
            isCategory.id isCategory:Cโ = {!!}
            isCategory._โ_ isCategory:Cโ = {!!}
            isCategory.unit-l-โ isCategory:Cโ = {!!}
            isCategory.unit-r-โ isCategory:Cโ = {!!}
            isCategory.unit-2-โ isCategory:Cโ = {!!}
            isCategory.assoc-l-โ isCategory:Cโ = {!!}
            isCategory.assoc-r-โ isCategory:Cโ = {!!}
            isCategory._โ_ isCategory:Cโ = {!!}


        Fโ : ๐๐ฎ๐ง๐ ๐ (๐๐๐ญ ๐)
        Fโ = {!!}



