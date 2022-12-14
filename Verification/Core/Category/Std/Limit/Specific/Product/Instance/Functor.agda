

module Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition

module _ {๐ : ๐ฐ _} {{_ : FiniteProductCategory ๐ on ๐}} where

  private
    ๐' : Category ๐
    ๐' = โฒ ๐ โฒ

  map-โ : โ{a b c d : ๐} -> (a โถ b) ร (c โถ d) -> (a โ c โถ b โ d)
  map-โ (f , g) = โงผ ฯโ โ f , ฯโ โ g โงฝ

  infixl 100 _โโโ_
  _โโโ_ : โ{a b c d : ๐} -> (a โถ b) -> (c โถ d) -> (a โ c โถ b โ d)
  _โโโ_ = ฮปโ map-โ


  private instance
    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:โงผโงฝ

  private
    lem-1 : โ{a b : ๐} -> map-โ (id {a = a} , id {a = b}) โผ id
    lem-1 {a} {b} = P
      where
        ida : a โถ a
        ida = id

        idb : b โถ b
        idb = id

        idab : (a โ b) โถ (a โ b)
        idab = id

        P = โงผ ฯโ โ ida , ฯโ โ idb โงฝ    โจ cong-โผ (unit-r-โ โ unit-l-โ โปยน , unit-r-โ โ unit-l-โ โปยน) โฉ-โผ
            โงผ idab โ ฯโ , idab โ ฯโ โงฝ  โจ expand-ฯโ,ฯโ โปยน โฉ-โผ
            idab                       โ

  isFunctor:โ : isFunctor (๐' ร-๐๐๐ญ ๐') ๐' โโจ
  isFunctor.map isFunctor:โ               = map-โ
  isFunctor.isSetoidHom:map isFunctor:โ   = record { cong-โผ = ฮป (p , q) โ cong-โผ (refl โ p , refl โ q) }
  isFunctor.functoriality-id isFunctor:โ  = lem-1
  isFunctor.functoriality-โ isFunctor:โ   = {!!}



