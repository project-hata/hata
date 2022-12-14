
module Verification.Core.Category.Std.Monad.KleisliCategory.Construction.Product where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Definition


open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product


module _ {๐ : Category ๐} {T : Monad ๐} {{_ : hasFiniteProducts ๐}} where

  infixl 70 _โ-๐๐ฅ๐ฌ_
  _โ-๐๐ฅ๐ฌ_ : (a b : Kleisli T) -> Kleisli T
  _โ-๐๐ฅ๐ฌ_ a b = incl (โจ a โฉ โ โจ b โฉ)



  module _ {a b : Kleisli T} where

    ฯโ-๐๐ฅ๐ฌ : a โ-๐๐ฅ๐ฌ b โถ a
    ฯโ-๐๐ฅ๐ฌ = incl (ฯโ โ pure)

    ฯโ-๐๐ฅ๐ฌ : a โ-๐๐ฅ๐ฌ b โถ b
    ฯโ-๐๐ฅ๐ฌ = incl (ฯโ โ pure)

    โงผ_โงฝ-๐๐ฅ๐ฌ : โ{x} -> ((x โถ a) ร (x โถ b)) -> x โถ a โ-๐๐ฅ๐ฌ b
    โงผ_โงฝ-๐๐ฅ๐ฌ (f , g) = incl {!!}

    instance
      isProduct:โ-๐๐ฅ๐ฌ : isProduct a b (a โ-๐๐ฅ๐ฌ b)
      isProduct.ฯโ isProduct:โ-๐๐ฅ๐ฌ             = ฯโ-๐๐ฅ๐ฌ
      isProduct.ฯโ isProduct:โ-๐๐ฅ๐ฌ             = ฯโ-๐๐ฅ๐ฌ
      isProduct.โงผ isProduct:โ-๐๐ฅ๐ฌ โงฝ            = โงผ_โงฝ-๐๐ฅ๐ฌ
      isProduct.isSetoidHom:โงผโงฝ isProduct:โ-๐๐ฅ๐ฌ = {!!}
      isProduct.reduce-ฯโ isProduct:โ-๐๐ฅ๐ฌ      = {!!}
      isProduct.reduce-ฯโ isProduct:โ-๐๐ฅ๐ฌ      = {!!}
      isProduct.expand-โ isProduct:โ-๐๐ฅ๐ฌ       = {!!}











