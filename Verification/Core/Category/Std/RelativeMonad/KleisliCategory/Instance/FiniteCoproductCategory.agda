
module Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory where

open import Verification.Conventions hiding (_โ_)

open import Verification.Core.Setoid
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition


module _ {๐ : Category ๐} {{_ : hasFiniteCoproducts ๐}} {๐ : Category ๐} {{_ : hasFiniteCoproducts ๐}} where
  module _ {J : Functor ๐ ๐} {T : RelativeMonad J} {{_ : isFiniteCoproductPreserving J}} where

    infixl 80 _โ-๐๐๐๐ฅ๐ฌ_
    _โ-๐๐๐๐ฅ๐ฌ_ : ๐๐๐๐ฅ๐ฌ T -> ๐๐๐๐ฅ๐ฌ T -> ๐๐๐๐ฅ๐ฌ T
    _โ-๐๐๐๐ฅ๐ฌ_ a b = incl (โจ a โฉ โ โจ b โฉ)

    ฮนโ-๐๐๐๐ฅ๐ฌ : โ{a b : ๐๐๐๐ฅ๐ฌ T} -> a โถ a โ-๐๐๐๐ฅ๐ฌ b
    ฮนโ-๐๐๐๐ฅ๐ฌ = incl (map ฮนโ โ repure)

    ฮนโ-๐๐๐๐ฅ๐ฌ : โ{a b : ๐๐๐๐ฅ๐ฌ T} -> b โถ a โ-๐๐๐๐ฅ๐ฌ b
    ฮนโ-๐๐๐๐ฅ๐ฌ = incl (map ฮนโ โ repure)

    โฆ_โฆ-๐๐๐๐ฅ๐ฌ : โ{a b x : ๐๐๐๐ฅ๐ฌ T} -> (f : (a โถ x) ร (b โถ x)) -> a โ-๐๐๐๐ฅ๐ฌ b โถ x
    โฆ_โฆ-๐๐๐๐ฅ๐ฌ (incl f , incl g) = incl (โจ preserves-โ โฉ โ โฆ f , g โฆ)

    module _ {a b : ๐๐๐๐ฅ๐ฌ T} where
      instance
        isCoproduct:โ-๐๐๐๐ฅ๐ฌ : isCoproduct a b (a โ-๐๐๐๐ฅ๐ฌ b)
        isCoproduct.ฮนโ isCoproduct:โ-๐๐๐๐ฅ๐ฌ             = ฮนโ-๐๐๐๐ฅ๐ฌ
        isCoproduct.ฮนโ isCoproduct:โ-๐๐๐๐ฅ๐ฌ             = ฮนโ-๐๐๐๐ฅ๐ฌ
        isCoproduct.โฆ isCoproduct:โ-๐๐๐๐ฅ๐ฌ โฆ            = โฆ_โฆ-๐๐๐๐ฅ๐ฌ
        isCoproduct.isSetoidHom:โฆโฆ isCoproduct:โ-๐๐๐๐ฅ๐ฌ = {!!}
        isCoproduct.reduce-ฮนโ isCoproduct:โ-๐๐๐๐ฅ๐ฌ      = {!!}
        isCoproduct.reduce-ฮนโ isCoproduct:โ-๐๐๐๐ฅ๐ฌ      = {!!}
        isCoproduct.expand-ฮนโ,ฮนโ isCoproduct:โ-๐๐๐๐ฅ๐ฌ       = {!!}

    โฅ-๐๐๐๐ฅ๐ฌ : ๐๐๐๐ฅ๐ฌ T
    โฅ-๐๐๐๐ฅ๐ฌ = incl โฅ

    instance
      isInitial:โฅ-๐๐๐๐ฅ๐ฌ : isInitial โฅ-๐๐๐๐ฅ๐ฌ
      isInitial:โฅ-๐๐๐๐ฅ๐ฌ = {!!}

    instance
      hasInitial:๐๐๐๐ฅ๐ฌ : hasInitial (๐๐๐๐ฅ๐ฌ T)
      hasInitial.โฅ hasInitial:๐๐๐๐ฅ๐ฌ = โฅ-๐๐๐๐ฅ๐ฌ
      hasInitial.isInitial:โฅ hasInitial:๐๐๐๐ฅ๐ฌ = it

      hasCoproducts:๐๐๐๐ฅ๐ฌ : hasCoproducts (๐๐๐๐ฅ๐ฌ T)
      hasCoproducts._โ_ hasCoproducts:๐๐๐๐ฅ๐ฌ            = _โ-๐๐๐๐ฅ๐ฌ_
      hasCoproducts.isCoproduct:โ hasCoproducts:๐๐๐๐ฅ๐ฌ  = isCoproduct:โ-๐๐๐๐ฅ๐ฌ

    instance
      hasFiniteCoproducts:๐๐๐๐ฅ๐ฌ : hasFiniteCoproducts (๐๐๐๐ฅ๐ฌ T)
      hasFiniteCoproducts.hasInitial:this hasFiniteCoproducts:๐๐๐๐ฅ๐ฌ     = hasInitial:๐๐๐๐ฅ๐ฌ
      hasFiniteCoproducts.hasCoproducts:this hasFiniteCoproducts:๐๐๐๐ฅ๐ฌ  = hasCoproducts:๐๐๐๐ฅ๐ฌ

    --------------------------------------------------------------
    -- By construction now, the functor ฮน-๐๐๐๐ฅ๐ฌ is finite coproduct preserving
    --
    module _ {a b : โจ ๐ โฉ} where
      instance
        preservesCoproduct:ฮน-๐๐๐๐ฅ๐ฌ : preservesCoproduct (ฮน-๐๐๐๐ฅ๐ฌ {T = T}) a b (a โ b)
        preservesCoproduct:ฮน-๐๐๐๐ฅ๐ฌ = record
          { preserve-ฮนโ = refl
          ; preserve-ฮนโ = refl
          }

    instance
      isFiniteCoproductPreserving:ฮน-๐๐๐๐ฅ๐ฌ : isFiniteCoproductPreserving (ฮน-๐๐๐๐ฅ๐ฌ {T = T})
      isFiniteCoproductPreserving.preservesCoproducts:this isFiniteCoproductPreserving:ฮน-๐๐๐๐ฅ๐ฌ = it
      isFiniteCoproductPreserving.preservesInitial:this isFiniteCoproductPreserving:ฮน-๐๐๐๐ฅ๐ฌ = {!!}







