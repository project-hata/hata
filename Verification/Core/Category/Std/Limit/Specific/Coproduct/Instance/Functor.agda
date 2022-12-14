
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor where

open import Verification.Conventions hiding (_โ_)
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

module _ {๐ : ๐ฐ ๐} {{_ : isCategory {๐} ๐}} {{_ : hasCoproducts โฒ ๐ โฒ }} where
-- {{_ : FiniteCoproductCategory ๐ on ๐}} where

  private
    ๐' : Category _
    ๐' = โฒ ๐ โฒ

  map-โ : โ{a b c d : ๐} -> (a โถ b) ร (c โถ d) -> (a โ c โถ b โ d)
  map-โ (f , g) = โฆ f โ ฮนโ , g โ ฮนโ โฆ

  infixl 100 _โโโ_
  _โโโ_ : โ{a b c d : ๐} -> (a โถ b) -> (c โถ d) -> (a โ c โถ b โ d)
  _โโโ_ = ฮปโ map-โ

  private instance
    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:โฆโฆ

  _โโโโโ_ : โ{a b c d : ๐} -> {f g : a โถ b} {h i : c โถ d}
            -> (f โผ g) -> (h โผ i)
            -> (f โโโ h) โผ (g โโโ i)
  _โโโโโ_ {f = f} {g} {h} {i} p q =
    let
        lem-1 : โฆ f โ ฮนโ , h โ ฮนโ โฆ โผ โฆ g โ ฮนโ , i โ ฮนโ โฆ
        lem-1 = cong-โผ ((p โ refl ) , q โ refl)

    in lem-1


  private instance
    isSetoidHom:map-โ : โ{a b c d : ๐} -> isSetoidHom โฒ((a โถ b) ร-๐ฐ (c โถ d))โฒ (a โ c โถ b โ d) (map-โ)
    isSetoidHom:map-โ = record { cong-โผ = ฮป (p , q) โ p โโโโโ q }

  functoriality-id-โ : โ{a b : ๐} -> map-โ (id {a = a} , id {a = b}) โผ id
  functoriality-id-โ {a} {b} = P
    where
      ida : a โถ a
      ida = id

      idb : b โถ b
      idb = id

      idab : (a โ b) โถ (a โ b)
      idab = id

      P = โฆ ida โ ฮนโ , idb โ ฮนโ โฆ    โจ cong-โผ (unit-l-โ โ unit-r-โ โปยน , unit-l-โ โ unit-r-โ โปยน) โฉ-โผ
          โฆ ฮนโ โ idab , ฮนโ โ idab โฆ  โจ expand-ฮนโ,ฮนโ โปยน โฉ-โผ
          idab                       โ

  append-โโโ : โ{a0 a1 b0 b1 x : ๐}
                -> {f0 : a0 โถ a1} -> {f1 : a1 โถ x}
                -> {g0 : b0 โถ b1} -> {g1 : b1 โถ x}
                -> (f0 โโโ g0) โ โฆ f1 , g1 โฆ โผ โฆ f0 โ f1 , g0 โ g1 โฆ
  append-โโโ {f0 = f0} {f1} {g0} {g1} =
    โฆ f0 โ ฮนโ , g0 โ ฮนโ โฆ โ โฆ f1 , g1 โฆ            โจ append-โฆโฆ โฉ-โผ
    โฆ ((f0 โ ฮนโ) โ โฆ f1 , g1 โฆ)
    , ((g0 โ ฮนโ) โ โฆ f1 , g1 โฆ) โฆ                  โจ cong-โผ ( (assoc-l-โ โ (refl โ reduce-ฮนโ))
                                                            , ((assoc-l-โ โ (refl โ reduce-ฮนโ)))) โฉ-โผ
    โฆ f0 โ f1 , g0 โ g1 โฆ                        โ



  functoriality-โ-โ : โ{a0 a1 a2 b0 b1 b2 : ๐}
                      -> {f0 : a0 โถ a1} -> {f1 : a1 โถ a2}
                      -> {g0 : b0 โถ b1} -> {g1 : b1 โถ b2}
                      -> ((f0 โ f1) โโโ (g0 โ g1)) โผ (f0 โโโ g0) โ (f1 โโโ g1)
  functoriality-โ-โ {f0 = f0} {f1} {g0} {g1} =
    ((f0 โ f1) โโโ (g0 โ g1))                  โจ cong-โผ (assoc-l-โ , assoc-l-โ) โฉ-โผ
    โฆ f0 โ (f1 โ ฮนโ) , g0 โ (g1 โ ฮนโ) โฆ        โจ append-โโโ โปยน โฉ-โผ
    (f0 โโโ g0) โ โฆ f1 โ ฮนโ , g1 โ ฮนโ โฆ        โ-โผ

  -- instance
  isFunctor:โ : isFunctor (๐' ร-๐๐๐ญ ๐') ๐' (ฮปโ _โ_)
  isFunctor.map isFunctor:โ               = map-โ
  isFunctor.isSetoidHom:map isFunctor:โ   = isSetoidHom:map-โ
  isFunctor.functoriality-id isFunctor:โ  = functoriality-id-โ
  isFunctor.functoriality-โ isFunctor:โ   = functoriality-โ-โ


  --------------------------------------------------------------
  -- properties

  module _ {a b c d : ๐} {f : a โถ b} {g : c โถ d} where
    module _ {{_ : isEpi f}} {{_ : isEpi g}} where
      isEpi:map-โ : isEpi (map-โ (f , g))
      isEpi.cancel-epi isEpi:map-โ {ฮฑ = ฮฑ} {ฮฒ} p =
        let
          functoriality-id-โ : ฮนโ โ ฮฑ โผ ฮนโ โ ฮฒ
          functoriality-id-โ = p
               โช (refl โ_) โซ
               >> ฮนโ โ (map-โ (f , g) โ ฮฑ) โผ ฮนโ โ (map-โ (f , g) โ ฮฒ) <<
               โช assoc-r-โ โโผโ assoc-r-โ โซ
               >> (ฮนโ โ map-โ (f , g)) โ ฮฑ โผ (ฮนโ โ map-โ (f , g)) โ ฮฒ <<
               โช reduce-ฮนโ โ refl โโผโ reduce-ฮนโ โ refl โซ
               >> (f โ ฮนโ) โ ฮฑ โผ (f โ ฮนโ) โ ฮฒ <<
               โช assoc-l-โ โโผโ assoc-l-โ โซ
               >> f โ (ฮนโ โ ฮฑ) โผ f โ (ฮนโ โ ฮฒ) <<
               โช cancel-epi โซ

          lem-2 : ฮนโ โ ฮฑ โผ ฮนโ โ ฮฒ
          lem-2 = p
               โช (refl โ_) โซ
               >> ฮนโ โ (map-โ (f , g) โ ฮฑ) โผ ฮนโ โ (map-โ (f , g) โ ฮฒ) <<
               โช assoc-r-โ โโผโ assoc-r-โ โซ
               >> (ฮนโ โ map-โ (f , g)) โ ฮฑ โผ (ฮนโ โ map-โ (f , g)) โ ฮฒ <<
               โช reduce-ฮนโ โ refl โโผโ reduce-ฮนโ โ refl โซ
               >> (g โ ฮนโ) โ ฮฑ โผ (g โ ฮนโ) โ ฮฒ <<
               โช assoc-l-โ โโผโ assoc-l-โ โซ
               >> g โ (ฮนโ โ ฮฑ) โผ g โ (ฮนโ โ ฮฒ) <<
               โช cancel-epi โซ

          lem-3 : ฮฑ โผ ฮฒ
          lem-3 = (functoriality-id-โ , lem-2)
                  โช cong-โผ {{isSetoidHom:โฆโฆ}} โซ
                  >> โฆ ฮนโ โ ฮฑ , ฮนโ โ ฮฑ โฆ โผ โฆ ฮนโ โ ฮฒ , ฮนโ โ ฮฒ โฆ <<
                  โช expand-ฮนโ,ฮนโ โปยน โโผโ expand-ฮนโ,ฮนโ โปยน โซ

        in lem-3

  --------------------------------------------------------------
  -- with isos

  open import Verification.Core.Category.Std.Morphism.Iso

  module _ {a b c d : ๐} where
    _โโโ_ : (a โ b) -> (c โ d) -> (a โ c โ b โ d)
    _โโโ_ p q = โจ p โฉ โโโ โจ q โฉ since record
              { inverse-โ = โจ p โฉโปยน โโโ โจ q โฉโปยน
              ; inv-r-โ = functoriality-โ-โ โปยน โ ((inv-r-โ (of p) โโโโโ inv-r-โ (of q)) โ functoriality-id-โ)
              ; inv-l-โ = functoriality-โ-โ โปยน โ ((inv-l-โ (of p) โโโโโ inv-l-โ (of q)) โ functoriality-id-โ)
              }


