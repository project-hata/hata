
module Verification.Core.Category.Std.Limit.Cone.Limit.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Representable2



module _ {๐ฅ : Category ๐} {๐ : Category ๐} where
  record Cone (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
    constructor cone
    field pt : โจ ๐ โฉ
    field โบ : Const pt โถ F

  open Cone public

  module _ (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) where
    macro ๐๐จ๐ง๐ = #structureOn (Cone F)


  module _ {F : ๐๐ฎ๐ง๐ ๐ฅ ๐} where
    record Hom-Cone (c d : Cone F) : ๐ฐ (๐ ๏ฝค ๐) where
      field pt : pt c โถ pt d
      field โบ : map-Const pt โ โบ d โผ โบ c

    open Hom-Cone public

    module _ {c d : Cone F} where
      record _โผ-Hom-Cone_ (f g : Hom-Cone c d) : ๐ฐ (๐ ๏ฝค ๐) where
        constructor incl
        field โจ_โฉ : pt f โผ pt g

      open _โผ-Hom-Cone_ public

      refl-โผ-Hom-Cone : โ{f : Hom-Cone c d} -> f โผ-Hom-Cone f
      refl-โผ-Hom-Cone = incl refl

      sym-โผ-Hom-Cone : โ{f g : Hom-Cone c d} -> f โผ-Hom-Cone g -> g โผ-Hom-Cone f
      sym-โผ-Hom-Cone (incl p) = incl (p โปยน)

      trans-โผ-Hom-Cone : โ{f g h : Hom-Cone c d} -> f โผ-Hom-Cone g -> g โผ-Hom-Cone h -> f โผ-Hom-Cone h
      trans-โผ-Hom-Cone (incl p) (incl q) = incl (p โ q)

      instance
        isSetoid:Hom-Cone : isSetoid (Hom-Cone c d)
        isSetoid:Hom-Cone = isSetoid:byDef _โผ-Hom-Cone_ refl-โผ-Hom-Cone sym-โผ-Hom-Cone trans-โผ-Hom-Cone

    id-๐๐จ๐ง๐ : โ{c : Cone F} -> Hom-Cone c c
    id-๐๐จ๐ง๐ = record
      { pt = id
      ; โบ = (functoriality-id โ refl) โ unit-l-โ
      }

    _โ-๐๐จ๐ง๐_ : โ{c d e : Cone F} -> Hom-Cone c d -> Hom-Cone d e -> Hom-Cone c e
    _โ-๐๐จ๐ง๐_ f g = record
      { pt = pt f โ pt g
      ; โบ = (functoriality-โ โ refl) โ assoc-l-โ โ (refl โ โบ g) โ โบ f
      }

    instance
      isCategory:Cone : isCategory (Cone F)
      isCategory.Hom isCategory:Cone = Hom-Cone
      isCategory.isSetoid:Hom isCategory:Cone = isSetoid:Hom-Cone
      isCategory.id isCategory:Cone = id-๐๐จ๐ง๐
      isCategory._โ_ isCategory:Cone = _โ-๐๐จ๐ง๐_
      isCategory.unit-l-โ isCategory:Cone = incl unit-l-โ
      isCategory.unit-r-โ isCategory:Cone = incl unit-r-โ
      isCategory.unit-2-โ isCategory:Cone = incl unit-2-โ
      isCategory.assoc-l-โ isCategory:Cone = incl assoc-l-โ
      isCategory.assoc-r-โ isCategory:Cone = incl assoc-r-โ
      isCategory._โ_ isCategory:Cone = ฮป p q -> incl (โจ p โฉ โ โจ q โฉ)

  record isLimit (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) (rep : โจ ๐ โฉ) : ๐ฐ (๐ ๏ฝค ๐) where
    field limitCocone : Const rep โถ F
    field limitUniversal : isTerminal (cone rep limitCocone)

  open isLimit public

  -- record hasLimit (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
  --   field rep : ๐๐จ๐ง๐ F
  --   field {{isTerminal:rep}} : isTerminal rep




