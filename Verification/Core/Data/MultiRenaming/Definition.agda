
module Verification.Core.Data.MultiRenaming.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Definition
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Op.Definition

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Category.Opposite



module _ (K : ๐ฐ ๐) (L : ๐ฐ ๐) where
  multiren : ๐๐ข๐ง๐๐ฑ K -> ๐๐๐ญ _
  multiren a = ๐๐ฑ (โ (โจ a โฉ โ_)) โฒ(โฎ๐๐๐ง L แตแตโฏแต)โฒ
  macro ๐๐ข๐๐ก๐๐๐๐ = #structureOn multiren

module _ {K : ๐ฐ ๐} {L : ๐ฐ ๐} where
  private
    โ : ๐ฐ _
    โ = โฎ๐๐๐ง L

  map-๐๐ข๐๐ก๐๐๐๐ : โ{a b : ๐๐ข๐ง๐๐ฑ K} -> (f : b โถ a) -> Functor (๐๐ข๐๐ก๐๐๐๐ K L a) (๐๐ข๐๐ก๐๐๐๐ K L b)
  map-๐๐ข๐๐ก๐๐๐๐ {a} {b} f = F since isFunctor:F
    where
      F : ๐๐ฑ (โ (โจ a โฉ โ_)) (โ แตแตโฏ) -> ๐๐ฑ (โ (โจ b โฉ โ_)) (โ แตแตโฏ)
      F x = indexed ฮป (k , kp) โ ix x (k , map f k kp)

      map-F : โ{x y : ๐๐ฑ (โ (โจ a โฉ โ_)) (โ แตแตโฏ)} -> (g : x โถ y) -> F x โถ F y
      map-F {x} {y} g = ฮป i โ g _

      isFunctor:F : isFunctor _ _ F
      isFunctor.map isFunctor:F = map-F
      isFunctor.isSetoidHom:map isFunctor:F = {!!}
      isFunctor.functoriality-id isFunctor:F = {!!}
      isFunctor.functoriality-โ isFunctor:F = {!!}

  instance
    isFunctor:๐๐ข๐๐ก๐๐๐๐ : isFunctor (๐๐ข๐ง๐๐ฑ K แตแต) (๐๐๐ญ _) (๐๐ข๐๐ก๐๐๐๐ K L)
    isFunctor.map isFunctor:๐๐ข๐๐ก๐๐๐๐ = map-๐๐ข๐๐ก๐๐๐๐
    isFunctor.isSetoidHom:map isFunctor:๐๐ข๐๐ก๐๐๐๐ = {!!}
    isFunctor.functoriality-id isFunctor:๐๐ข๐๐ก๐๐๐๐ = {!!}
    isFunctor.functoriality-โ isFunctor:๐๐ข๐๐ก๐๐๐๐ = {!!}

module _ (K : ๐ฐ ๐) (L : ๐ฐ ๐) where
  MultiRen = โจแตแตแต (๐๐ข๐๐ก๐๐๐๐ K L)
  macro ๐๐ฎ๐ฅ๐ญ๐ข๐๐๐ง = #structureOn MultiRen


-- | The category ๐๐ฎ๐ฅ๐ญ๐ข๐๐๐ง has coproducts.
--   Actually, one could show this by showing that the functor |๐๐ข๐๐ก๐๐๐๐ : ๐๐ข๐ง๐๐ฑ โถ ๐๐๐ญ|,
--   seen as the fibration |โจ ๐๐ข๐๐ก๐๐๐๐ โถ ๐๐ข๐ง๐๐ฑ| is a stack/2-sheaf
--   since it seems that stacks inherit the coproducts from their base category, i.e., ๐๐ข๐ง๐๐ฑ.
--
--   For basics on stacks see http://homepage.sns.it/vistoli/descent.pdf .





