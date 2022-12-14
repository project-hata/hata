
module Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory where

open import Verification.Core.Conventions hiding (_โ_)

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Indexed.Definition


module _ {I : ๐ฐ ๐} {๐ : Category ๐} {{_ : hasFiniteCoproducts ๐}} where

  _โ-๐๐ฑ_ : (a b : ๐๐ฑ I ๐) -> ๐๐ฑ I ๐
  _โ-๐๐ฑ_ a b = indexed (ฮป i โ ix a i โ ix b i)


  module _ {a b : ๐๐ฑ I ๐} where
    instance
      isCoproduct:โ-๐๐ฑ : isCoproduct a b (a โ-๐๐ฑ b)
      isCoproduct.ฮนโ isCoproduct:โ-๐๐ฑ             = ฮป i -> ฮนโ
      isCoproduct.ฮนโ isCoproduct:โ-๐๐ฑ             = ฮป i -> ฮนโ
      isCoproduct.โฆ isCoproduct:โ-๐๐ฑ โฆ            = ฮป (f , g) i โ โฆ f i , g i โฆ
      isCoproduct.isSetoidHom:โฆโฆ isCoproduct:โ-๐๐ฑ = {!!}
      isCoproduct.reduce-ฮนโ isCoproduct:โ-๐๐ฑ      = {!!}
      isCoproduct.reduce-ฮนโ isCoproduct:โ-๐๐ฑ      = {!!}
      isCoproduct.expand-ฮนโ,ฮนโ isCoproduct:โ-๐๐ฑ       = {!!}


  instance
    hasCoproducts:๐๐ฑ : hasCoproducts (๐๐ฑ I ๐)
    hasCoproducts._โ_ hasCoproducts:๐๐ฑ            = _โ-๐๐ฑ_
    hasCoproducts.isCoproduct:โ hasCoproducts:๐๐ฑ  = isCoproduct:โ-๐๐ฑ

  โฅ-๐๐ฑ : ๐๐ฑ I ๐
  โฅ-๐๐ฑ = indexed ฮป _ -> โฅ

  instance
    isInitial:โฅ-๐๐ฑ : isInitial โฅ-๐๐ฑ
    isInitial:โฅ-๐๐ฑ = {!!}

  instance
    hasInitial:๐๐ฑ : hasInitial (๐๐ฑ I ๐)
    hasInitial.โฅ hasInitial:๐๐ฑ = โฅ-๐๐ฑ
    hasInitial.isInitial:โฅ hasInitial:๐๐ฑ = {!!}

  instance
    hasFiniteCoproducts:๐๐ฑ : hasFiniteCoproducts (๐๐ฑ I ๐)
    hasFiniteCoproducts:๐๐ฑ = hasFiniteCoproducts:default



