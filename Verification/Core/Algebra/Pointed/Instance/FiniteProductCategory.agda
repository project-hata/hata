
module Verification.Core.Algebra.Pointed.Instance.FiniteProductCategory where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Algebra.Pointed.Definition
open import Verification.Core.Algebra.Pointed.Instance.Category


-- ๐๐ญ๐ has products

_ร-๐๐ญ๐แต_ : (A : ๐๐ญ๐ ๐) (B : ๐๐ญ๐ ๐) -> ๐ฐ (๐ ๏ฝค ๐)
_ร-๐๐ญ๐แต_ A B = โจ A โฉ ร โจ B โฉ


-- module _ {A B : ๐๐ญ๐ ๐} where
module _ {Aแต Bแต : ๐ฐ ๐} {{_ : isPointed Aแต}} {{_ : isPointed Bแต}} where

  private
    macro A = #structureOn Aแต
    macro B = #structureOn Bแต

  instance
    isPointed:ร-๐๐ญ๐ : isPointed (A ร-๐๐ญ๐แต B)
    isPointed:ร-๐๐ญ๐ = isPointed:byDefinition (pt , pt)

  ฯโ-๐๐ญ๐ : (A ร B) โถ A
  ฯโ-๐๐ญ๐ = ฯโ since isPointedHom:byDefinition refl-โก

  ฯโ-๐๐ญ๐ : (A ร B) โถ B
  ฯโ-๐๐ญ๐ = ฯโ since isPointedHom:byDefinition refl-โก

  โงผ_โงฝ-๐๐ญ๐ : โ{X : ๐๐ญ๐ ๐} -> (X โถ A) ร (X โถ B) -> (X โถ A ร B)
  โงผ_โงฝ-๐๐ญ๐ (f , g) = โงผ โจ f โฉ , โจ g โฉ โงฝ since isPointedHom:byDefinition (ฮป i โ ptmap i , ptmap i)

  instance
    isProduct:ร-๐๐ญ๐ : isProduct A B (A ร B)
    isProduct.ฯโ isProduct:ร-๐๐ญ๐ = ฯโ-๐๐ญ๐
    isProduct.ฯโ isProduct:ร-๐๐ญ๐ = ฯโ-๐๐ญ๐
    isProduct.โงผ isProduct:ร-๐๐ญ๐ โงฝ = โงผ_โงฝ-๐๐ญ๐
    isProduct.isSetoidHom:โงผโงฝ isProduct:ร-๐๐ญ๐ = {!โงผ_โงฝ-๐๐ญ๐!}
    isProduct.reduce-ฯโ isProduct:ร-๐๐ญ๐ = {!!}
    isProduct.reduce-ฯโ isProduct:ร-๐๐ญ๐ = {!!}
    isProduct.expand-โ isProduct:ร-๐๐ญ๐ = {!!}

_ร-๐๐ญ๐_ : (A B : ๐๐ญ๐ ๐) -> ๐๐ญ๐ _
_ร-๐๐ญ๐_ A B = A ร B


