
module Verification.Core.Category.Std.Functor.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category


module _ (๐ : Category ๐) (๐ : Category ๐) where
  macro ๐๐ฎ๐ง๐ = #structureOn (Functor ๐ ๐)

module _ {๐ : Category ๐} {๐ : Category ๐} where

  id-๐๐ฎ๐ง๐ : โ{F : ๐๐ฎ๐ง๐ ๐ ๐} -> Natural F F
  id-๐๐ฎ๐ง๐ {F} = id _ since natural lem-1
    where
      lem-1 : โ{x y : โจ ๐ โฉ} (f : x โถ y) -> id โ map f โผ map f โ id
      lem-1 f = unit-l-โ โ unit-r-โ โปยน

  _โ-๐๐ฎ๐ง๐_ : โ{F G H : ๐๐ฎ๐ง๐ ๐ ๐} -> Natural F G -> Natural G H -> Natural F H
  _โ-๐๐ฎ๐ง๐_ ฮฑ ฮฒ = (ฮป x -> โจ ฮฑ โฉ x โ โจ ฮฒ โฉ x) since natural lem-1
    where
      lem-1 : โ{x y : โจ ๐ โฉ} (f : x โถ y) -> (โจ ฮฑ โฉ _ โ โจ ฮฒ โฉ _) โ map f โผ map f โ (โจ ฮฑ โฉ _ โ โจ ฮฒ โฉ _)
      lem-1 f = (โจ ฮฑ โฉ _ โ โจ ฮฒ โฉ _) โ map f    โจ assoc-l-โ โฉ-โผ
                โจ ฮฑ โฉ _ โ (โจ ฮฒ โฉ _ โ map f)    โจ refl โ naturality f โฉ-โผ
                โจ ฮฑ โฉ _ โ (map f โ โจ ฮฒ โฉ _)    โจ assoc-r-โ โฉ-โผ
                (โจ ฮฑ โฉ _ โ map f) โ โจ ฮฒ โฉ _    โจ naturality f โ refl โฉ-โผ
                (map f โ โจ ฮฑ โฉ _) โ โจ ฮฒ โฉ _    โจ assoc-l-โ โฉ-โผ
                map f โ (โจ ฮฑ โฉ _ โ โจ ฮฒ โฉ _)    โ

  instance
    isCategory:Functor : isCategory (๐๐ฎ๐ง๐ ๐ ๐)
    isCategory.Hom isCategory:Functor = Natural
    isCategory.isSetoid:Hom isCategory:Functor = isSetoid:Natural
    isCategory.id isCategory:Functor           = id-๐๐ฎ๐ง๐
    isCategory._โ_ isCategory:Functor          = _โ-๐๐ฎ๐ง๐_
    isCategory.unit-l-โ isCategory:Functor     = componentwise $ ฮป _ -> unit-l-โ
    isCategory.unit-r-โ isCategory:Functor     = componentwise $ ฮป _ -> unit-r-โ
    isCategory.unit-2-โ isCategory:Functor     = componentwise $ ฮป _ -> unit-2-โ
    isCategory.assoc-l-โ isCategory:Functor    = componentwise $ ฮป _ -> assoc-l-โ
    isCategory.assoc-r-โ isCategory:Functor    = componentwise $ ฮป _ -> assoc-r-โ
    isCategory._โ_ isCategory:Functor          = ฮป p q -> componentwise (ฮป x -> โจ p โฉ x โ โจ q โฉ x)

  instance
    isSetoid:Functor : isSetoid (๐๐ฎ๐ง๐ ๐ ๐)
    isSetoid:Functor = isSetoid:byCategory



