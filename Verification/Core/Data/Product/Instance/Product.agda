
module Verification.Core.Data.Product.Instance.Product where

open import Verification.Conventions
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Construction.Product
-- open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor

open import Verification.Core.Data.Product.Definition

module _ {A B : ๐ฐ ๐} where
  instance
    isProduct:ร : isProduct A B (A ร B)
    isProduct.ฯโ isProduct:ร = fst
    isProduct.ฯโ isProduct:ร = snd
    isProduct.โงผ isProduct:ร โงฝ = ฮป (f , g) x -> (f x , g x)
    isProduct.isSetoidHom:โงผโงฝ isProduct:ร = record { cong-โผ = ฮป (p , q) โ ฮป i x โ p i x , q i x }
    isProduct.reduce-ฯโ isProduct:ร = refl
    isProduct.reduce-ฯโ isProduct:ร = refl
    isProduct.expand-ฯโ,ฯโ isProduct:ร = refl

instance
  isTerminal:โค-๐ฐ : isTerminal (โค-๐ฐ {๐})
  isTerminal:โค-๐ฐ = record { intro-โค = const tt ; expand-โค = funExt lem-1 }
    where
      lem-1 : โ{A} {f : A -> โค-๐ฐ} -> โ a -> (f a โก tt)
      lem-1 {f = f} a with f a
      ... | tt = refl-โก

  hasTerminal:๐๐ง๐ข๐ฏ : hasTerminal (๐๐ง๐ข๐ฏ ๐)
  hasTerminal:๐๐ง๐ข๐ฏ = record { โค = โค-๐ฐ }

  hasProducts:๐๐ง๐ข๐ฏ : hasProducts (๐๐ง๐ข๐ฏ ๐)
  hasProducts:๐๐ง๐ข๐ฏ = record { _โ_ = _ร-๐ฐ_ }

  hasFiniteProducts:๐๐ง๐ข๐ฏ : hasFiniteProducts (๐๐ง๐ข๐ฏ ๐)
  hasFiniteProducts:๐๐ง๐ข๐ฏ = hasFiniteProducts:default



