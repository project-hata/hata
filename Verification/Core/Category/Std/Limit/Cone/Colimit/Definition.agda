
module Verification.Core.Category.Std.Limit.Cone.Colimit.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Representable2


module _ {๐ฅ : Category ๐} {๐ : Category ๐} where
  record Cocone (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
    constructor cocone
    field pt : โจ ๐ โฉ
    field โบ : F โถ Const pt

  open Cocone public

  module _ (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) where
    macro ๐๐จ๐๐จ๐ง๐ = #structureOn (Cocone F)


  module _ {F : ๐๐ฎ๐ง๐ ๐ฅ ๐} where
    record Hom-Cocone (c d : Cocone F) : ๐ฐ (๐ ๏ฝค ๐) where
      field pt : pt c โถ pt d
      field โบ : โบ c โ map-Const pt โผ โบ d

    open Hom-Cocone public

    module _ {c d : Cocone F} where
      record _โผ-Hom-Cocone_ (f g : Hom-Cocone c d) : ๐ฐ (๐ ๏ฝค ๐) where
        constructor incl
        field โจ_โฉ : pt f โผ pt g

      open _โผ-Hom-Cocone_ public

      refl-โผ-Hom-Cocone : โ{f : Hom-Cocone c d} -> f โผ-Hom-Cocone f
      refl-โผ-Hom-Cocone = incl refl

      sym-โผ-Hom-Cocone : โ{f g : Hom-Cocone c d} -> f โผ-Hom-Cocone g -> g โผ-Hom-Cocone f
      sym-โผ-Hom-Cocone (incl p) = incl (p โปยน)

      trans-โผ-Hom-Cocone : โ{f g h : Hom-Cocone c d} -> f โผ-Hom-Cocone g -> g โผ-Hom-Cocone h -> f โผ-Hom-Cocone h
      trans-โผ-Hom-Cocone (incl p) (incl q) = incl (p โ q)

      instance
        isSetoid:Hom-Cocone : isSetoid (Hom-Cocone c d)
        isSetoid:Hom-Cocone = isSetoid:byDef _โผ-Hom-Cocone_ refl-โผ-Hom-Cocone sym-โผ-Hom-Cocone trans-โผ-Hom-Cocone

    id-๐๐จ๐๐จ๐ง๐ : โ{c : Cocone F} -> Hom-Cocone c c
    id-๐๐จ๐๐จ๐ง๐ = record
      { pt = id
      ; โบ = (refl โ functoriality-id) โ unit-r-โ
      }

    _โ-๐๐จ๐๐จ๐ง๐_ : โ{c d e : Cocone F} -> Hom-Cocone c d -> Hom-Cocone d e -> Hom-Cocone c e
    _โ-๐๐จ๐๐จ๐ง๐_ f g = record
      { pt = pt f โ pt g
      ; โบ = (refl โ functoriality-โ) โ assoc-r-โ โ (โบ f โ refl) โ โบ g
      }

    instance
      isCategory:Cocone : isCategory (Cocone F)
      isCategory.Hom isCategory:Cocone = Hom-Cocone
      isCategory.isSetoid:Hom isCategory:Cocone = isSetoid:Hom-Cocone
      isCategory.id isCategory:Cocone = id-๐๐จ๐๐จ๐ง๐
      isCategory._โ_ isCategory:Cocone = _โ-๐๐จ๐๐จ๐ง๐_
      isCategory.unit-l-โ isCategory:Cocone = incl unit-l-โ
      isCategory.unit-r-โ isCategory:Cocone = incl unit-r-โ
      isCategory.unit-2-โ isCategory:Cocone = incl unit-2-โ
      isCategory.assoc-l-โ isCategory:Cocone = incl assoc-l-โ
      isCategory.assoc-r-โ isCategory:Cocone = incl assoc-r-โ
      isCategory._โ_ isCategory:Cocone = ฮป p q -> incl (โจ p โฉ โ โจ q โฉ)

  record isColimit (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) (rep : โจ ๐ โฉ) : ๐ฐ (๐ ๏ฝค ๐) where
    field colimitCocone : F โถ Const rep
    field colimitUniversal : isInitial (cocone rep colimitCocone)

  open isColimit public

  -- record hasColimit (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
  --   field rep : ๐๐จ๐๐จ๐ง๐ F
  --   field {{isTerminal:rep}} : isInitial rep




