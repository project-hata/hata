
module Verification.Core.Category.Std.Category.Structured.Monoidal.Definition3 where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Iso
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Properties.Monoidal


module _ {a b c : ๐๐๐ญ ๐} where
  ฮฑ-๐๐๐ญ : ((a ร b) ร-๐๐๐ญ c) โถ (a ร (b ร c))
  ฮฑ-๐๐๐ญ = โจ assoc-l-โ โฉ

record isMonoidal (๐ : Category ๐) : ๐ฐ ๐ where

  field โ[_] : Functor (๐ ร-๐๐๐ญ ๐) ๐
  field Ident : Functor (โค-๐๐๐ญ {๐}) ๐

  field assoc-l-โ : (โ[_] โโโ id-๐๐๐ญ) โ-๐๐๐ญ โ[_] โ (ฮฑ-๐๐๐ญ โ (id-๐๐๐ญ โโโ โ[_]) โ โ[_])
  field unit-r-โ : โงผ id-๐๐๐ญ , (intro-โค โ Ident) โงฝ-๐๐๐ญ โ-๐๐๐ญ โ[_] โ id
  field unit-l-โ : โงผ intro-โค โ Ident , id-๐๐๐ญ โงฝ-๐๐๐ญ โ-๐๐๐ญ โ[_] โ id

  _โ_ : โจ ๐ โฉ -> โจ ๐ โฉ -> โจ ๐ โฉ
  _โ_ a b = โจ โ[_] โฉ (a , b)

  ident : โจ ๐ โฉ
  ident = โจ Ident โฉ (lift tt)

  _โโโ_ : โ{a b c d : โจ ๐ โฉ} -> (f : a โถ c) -> (g : b โถ d) -> a โ b โถ c โ d
  _โโโ_ f g = mapOf โ[_] (f , g)

  infixl 80 _โ_ _โโโ_

  -- iฮฑ : โ(a b c : โจ ๐ โฉ) -> (a โ b) โ c โ a โ (b โ c)
  -- iฮฑ a b c = โจ โจ assoc-l-โ โฉ โฉ ((a , b) , c)

  -- iฯ : โ(a : โจ ๐ โฉ) -> a โ ident โ a
  -- iฯ a = โจ โจ unit-r-โ โฉ โฉ a

  -- iฮป : โ(a : โจ ๐ โฉ) -> ident โ a โ a
  -- iฮป a = โจ โจ unit-l-โ โฉ โฉ a

  fฮฑ : โ(a b c : โจ ๐ โฉ) -> (a โ b) โ c โถ a โ (b โ c)
  fฮฑ a b c = โจ โจ assoc-l-โ โฉ โฉ ((a , b) , c)

  fฯ : โ(a : โจ ๐ โฉ) -> a โ ident โถ a
  fฯ a = โจ โจ unit-r-โ โฉ โฉ a

  fฮป : โ(a : โจ ๐ โฉ) -> ident โ a โถ a
  fฮป a = โจ โจ unit-l-โ โฉ โฉ a

  bฮฑ : โ(a b c : โจ ๐ โฉ) -> a โ (b โ c) โถ (a โ b) โ c
  bฮฑ a b c = โจ โจ assoc-l-โ โฉโปยน โฉ ((a , b) , c)

  bฯ : โ(a : โจ ๐ โฉ) -> a โถ a โ ident
  bฯ a = โจ โจ unit-r-โ โฉโปยน โฉ a

  bฮป : โ(a : โจ ๐ โฉ) -> a โถ ident โ a
  bฮป a = โจ โจ unit-l-โ โฉโปยน โฉ a

  field triangle : โ{A B : โจ ๐ โฉ} -> (fฯ A โโโ id {a = B}) โผ (fฮฑ A ident B โ (id โโโ fฮป B))


module _ ๐ where
  Monoidal = Category ๐ :& isMonoidal

