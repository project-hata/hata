
module Verification.Classical.Space.Measure.Instance.Category where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition

open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Universe.Definition -- for function á¶-Ï

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Definition

open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition
open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Setoid.Power.Instance.HasCoproducts
open import Verification.Core.Setoid.Power.Instance.HasProducts
open import Verification.Core.Setoid.Power.Union
open import Verification.Core.Setoid.Power.Intersection
open import Verification.Core.Setoid.Construction.Product

open import Verification.Core.Set.Contradiction

open import Verification.Classical.Space.Measure.Definition



module _ {A : ðð­ð ð} {B : ðð­ð ð} where
  infix 90 _â»Â¹áµ-ðð­ð
  _â»Â¹áµ-ðð­ð : (f : SetoidHom A B) -> ð« B -> ð« A
  _â»Â¹áµ-ðð­ð f U = Váµ since isSubsetoid:Váµ
    where
      Váµ : â¨ A â© -> Prop _
      Váµ a = â£ â¨ f â© a â U â£

      P : â{a b : â¨ A â©} -> a â¼ b -> a â Váµ -> b â Váµ
      -- P aâ¼b aâV = transp-â¼ {{_}} {{of U}} (congOf-â¼ f aâ¼b) aâV
      P aâ¼b aâV = transpOf-â¼ U (congOf-â¼ f aâ¼b) aâV

      isSubsetoid:Váµ : isSubsetoid Váµ
      isSubsetoid:Váµ = record { transp-â¼ = P }

  module _ (f : SetoidHom A B) where
    macro
      _â»Â¹-ðð­ð = #structureOn (f â»Â¹áµ-ðð­ð)

--
-- NOTE: We use the same universe level ð for both `A` and `B` here
-- because doing otherwise would make the â»Â¹ machinery more complicated.
-- (Taking preimages across functions that switch universes would need
-- to be investigated.)
--
record isHom-ðððð¬ (A : ðððð¬ ð) (B : ðððð¬ ð) (f : SetoidHom (â³ A) (â³ B)) : ð° (ð âº) where
  field _â»Â¹-Ï : Measurable (of B) -> Measurable (of A)
  field eval-â»Â¹-Ï : â{U} -> â¦ U â»Â¹-Ï â§ â (f â»Â¹-ðð­ð) â¦ U â§

open isHom-ðððð¬ {{...}} public

module _ (A B : ðððð¬ ð) where
  Hom-ðððð¬ = SetoidHom (â³ A) (â³ B) :& isHom-ðððð¬ A B

module _ {A B : ðððð¬ ð} where
  record _â¼-Hom-ðððð¬_ (f g : Hom-ðððð¬ A B) : ð° ð where
    constructor incl
    field â¨_â© : â¨ f â© â¼ â¨ g â©

  open _â¼-Hom-ðððð¬_ public

  instance
    isSetoid:Hom-ðððð¬ : isSetoid (Hom-ðððð¬ A B)
    isSetoid:Hom-ðððð¬ = isSetoid:byDef
      _â¼-Hom-ðððð¬_
      (incl refl)
      (Î» p -> incl (sym â¨ p â©))
      (Î» p q -> incl (â¨ p â© â â¨ q â©))

id-ðððð¬ : â{A : ðððð¬ ð} -> Hom-ðððð¬ A A
id-ðððð¬ {A = A} = id-ð° since P
  where
    P : isHom-ðððð¬ A A id-ðð­ð
    P = record
      { _â»Â¹-Ï = Î» V -> V
      ; eval-â»Â¹-Ï = refl-â
      }

_â-ðððð¬_ : â{A B C : ðððð¬ ð} -> Hom-ðððð¬ A B -> Hom-ðððð¬ B C -> Hom-ðððð¬ A C
_â-ðððð¬_ {A = A} {B} {C} f g = â²_â² (â¨ f â© â-ð° â¨ g â©) {makeâi {{isSetoidHom:â {f = â³ f} {â³ g}}}} {{P}}
  where
    P : isHom-ðððð¬ A C ((â³ f) â-ðð­ð (â³ g))
    P = record
      { _â»Â¹-Ï = Î» U -> (U â»Â¹-Ï) â»Â¹-Ï
      ; eval-â»Â¹-Ï = Î» {U} -> â¦ U â»Â¹-Ï â»Â¹-Ï â§ â¨ {!!} â©-â
                             (((â³ f) â-ðð­ð (â³ g)) â»Â¹-ðð­ð) â¦ U â§ â-â 
      }


instance
  isCategory:ðððð¬ : isCategory (ðððð¬ ð)
  isCategory.Hom isCategory:ðððð¬ = Hom-ðððð¬
  isCategory.isSetoid:Hom isCategory:ðððð¬ = isSetoid:Hom-ðððð¬
  isCategory.id isCategory:ðððð¬ = id-ðððð¬
  isCategory._â_ isCategory:ðððð¬ = _â-ðððð¬_
  isCategory.unit-l-â isCategory:ðððð¬ {f = f} = incl (unit-l-â {{of ðð­ð _}} {f = â³ f})
  isCategory.unit-r-â isCategory:ðððð¬ = {!!}
  isCategory.unit-2-â isCategory:ðððð¬ = {!!}
  isCategory.assoc-l-â isCategory:ðððð¬ = {!!}
  isCategory.assoc-r-â isCategory:ðððð¬ = {!!}
  isCategory._â_ isCategory:ðððð¬ = {!!}





