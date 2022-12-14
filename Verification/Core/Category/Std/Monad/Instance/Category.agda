
module Verification.Core.Category.Std.Monad.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Morphism.Iso

module _ {ð : ð° ð} {{_ : isCategory {ð} ð}} where
  module ShortMonadNotation where
    --------------
    -- Does not work, probably implicit argument confusion
    --
    -- Î·áµ : â {a : ð} -> a â¶ T a
    -- Î·áµ = pure
    -- macro Î· = #structureOn (Î» {a} -> Î·áµ {a})
    --
    -----
    module _ {T : ð -> ð} {{_ : Monad â² ð â² on T}} where
      Î· : Natural id â² T â²
      Î· = pure since it

      Î¼ : Natural (â² T â² â-ððð­ â² T â²) â² T â²
      Î¼ = join since it

    module _ (T : Monad â² ð â²) where
      Î·Of : Natural id â² â¨ T â© â²
      Î·Of = pure since it

      Î¼Of : Natural (â² â¨ T â© â² â-ððð­ â² â¨ T â© â²) â² â¨ T â© â²
      Î¼Of = join since it


open ShortMonadNotation

module _ (ð : Category ð) where
  macro ðð§ð = #structureOn (Monad ð)

module _ {ð : Category ð} where

  record isMonadHom {S T : Monad ð} (Î± : Natural â² â¨ S â© â² â² â¨ T â© â²) : ð° ð where
    field pres-Î· : Î· â Î± â¼ Î·
    field pres-Î¼ : Î¼ â Î± â¼ ((Î± âââ Î±) â Î¼)

  open isMonadHom {{...}} public

  isMonadHom:id : â{S : Monad ð} -> isMonadHom {S} {S} id
  isMonadHom:id {S} = record { pres-Î· = lem-01 ; pres-Î¼ = {!!}} -- lem-02}
    where
      lem-01 : (Î·Of S â-ðð®ð§ð id-ðð®ð§ð) â¼-Natural Î·
      lem-01 = componentwise $ Î» x -> unit-r-â

      lem-02 : (Î¼Of S â-ðð®ð§ð id-ðð®ð§ð) â¼-Natural ((id-ðð®ð§ð {F = â² â¨ S â© â²} âââ id-ðð®ð§ð {F = â² â¨ S â© â²}) â-ðð®ð§ð Î¼ {T = â¨ S â©})
      lem-02 = {!!}
               -- _ = join â id            â¨ unit-r-â â©-â¼
               --   join                 â¨ unit-l-â â»Â¹ â©-â¼
               --   id â join            â¨ functoriality-id â»Â¹ â refl â©-â¼
               --   (map id) â join      â¨ unit-l-â â»Â¹ â refl â©-â¼
               --   (id â map id) â join â

  isMonadHom:â : â{S T U : Monad ð} -> â{Î± Î²}
                 -> isMonadHom {S} {T} Î± -> isMonadHom {T} {U} Î² -> isMonadHom {S} {U} (Î± â Î²)
  isMonadHom:â {S} {T} {U} {Î±} {Î²} Î±p Î²p = record { pres-Î· = lem-01 ; pres-Î¼ = lem-02 }
    where
      lem-01 : (Î·Of S â-ðð®ð§ð (Î± â-ðð®ð§ð Î²)) â¼ Î·Of U
      lem-01 = componentwise $ Î» x ->
                 (â¨ Î·Of S â© x â (â¨ Î± â© x â â¨ Î² â© x))  â¨ assoc-r-â â©-â¼
                 ((â¨ Î·Of S â© x â â¨ Î± â© x) â â¨ Î² â© x)   â¨ â¨ pres-Î· {{Î±p}} â© x â refl â©-â¼
                 (â¨ Î·Of T â© x â â¨ Î² â© x)               â¨ â¨ pres-Î· {{Î²p}} â© x â©-â¼
                 â¨ Î·Of U â©  x                            â

      lem-02 : (Î¼Of S â-ðð®ð§ð (Î± â-ðð®ð§ð Î²)) â¼ (((Î± â-ðð®ð§ð Î²) âââ (Î± â-ðð®ð§ð Î²)) â-ðð®ð§ð Î¼)
      lem-02 = componentwise $ Î» x ->
                 â¨ Î¼Of S â© x â (â¨ Î± â© x â â¨ Î² â© x)               â¨ assoc-r-â â©-â¼
                 (â¨ Î¼Of S â© x â â¨ Î± â© x) â â¨ Î² â© x               â¨ â¨ pres-Î¼ {{Î±p}} â© x â refl â©-â¼
                 (â¨ Î± âââ Î± â© x) â â¨ Î¼Of T â© x â â¨ Î² â© x         â¨ assoc-l-â â©-â¼
                 (â¨ Î± âââ Î± â© x) â (â¨ Î¼Of T â© x â â¨ Î² â© x)       â¨ refl â â¨ pres-Î¼ {{Î²p}} â© x â©-â¼
                 (â¨ Î± âââ Î± â© x) â (â¨ Î² âââ Î² â© x â â¨ Î¼Of U â© x) â¨ assoc-r-â â©-â¼
                 ((â¨ Î± âââ Î± â© x) â â¨ Î² âââ Î² â© x) â â¨ Î¼Of U â© x â¨ â¨ interchange-âââ Î± Î² Î± Î² â© x â»Â¹ â refl â©-â¼

                 â¨ (((Î± â-ðð®ð§ð Î²) âââ (Î± â-ðð®ð§ð Î²)) â-ðð®ð§ð Î¼) â© x â


  private
    SubcategoryData-ðð§ð : SubcategoryData (ðð®ð§ð ð ð) (Monad ð)
    SubcategoryData-ðð§ð = subcatdata (Î» x â â² â¨ x â© â²) (Î» {a b} -> isMonadHom {a} {b})

  instance
    isSubcategory:ðð§ð : isSubcategory SubcategoryData-ðð§ð
    isSubcategory.closed-â isSubcategory:ðð§ð = isMonadHom:â
    isSubcategory.closed-id isSubcategory:ðð§ð = isMonadHom:id

  instance
    isCategory:ðð§ð : isCategory (ðð§ð ð)
    isCategory:ðð§ð = isCategory:bySubcategory






