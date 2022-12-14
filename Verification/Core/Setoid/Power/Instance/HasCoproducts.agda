
module Verification.Core.Setoid.Power.Instance.HasCoproducts where

open import Verification.Core.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition

open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Setoid.Power.Union


----------------------------------------------------------
-- Binary products
----------------------------------------------------------
module _ {A : ๐๐ญ๐ ๐} where

  elim-โฅ-๐ซ-๐๐ญ๐ : โ{U : ๐ซ A} -> โ โถ U
  elim-โฅ-๐ซ-๐๐ญ๐ = incl (ฮป ())

  instance
    isInitial:โง-๐ซ-๐๐ญ๐ : isInitial {๐ = ๐ซ A} โ-๐ซ-๐๐ญ๐
    isInitial:โง-๐ซ-๐๐ญ๐ = record
      { elim-โฅ = elim-โฅ-๐ซ-๐๐ญ๐
      ; expand-โฅ = tt
      }


  instance
    hasInitial:๐ซ-๐๐ญ๐ : hasInitial (๐ซ A)
    hasInitial.โฅ hasInitial:๐ซ-๐๐ญ๐ = โ
    hasInitial.isInitial:โฅ hasInitial:๐ซ-๐๐ญ๐ = it

  module _ {U V : ๐ซ A} where

    ฮนโ-๐ซ-๐๐ญ๐ : U โถ U โช V
    ฮนโ-๐ซ-๐๐ญ๐ = incl (ฮป aโU โ left aโU)

    ฮนโ-๐ซ-๐๐ญ๐ : V โถ U โช V
    ฮนโ-๐ซ-๐๐ญ๐ = incl (ฮป aโV โ right aโV)

    โฆ_โฆ-๐ซ-๐๐ญ๐ : โ{X} -> (U โถ X) ร-๐ฐ (V โถ X) -> U โช V โถ X
    โฆ_โฆ-๐ซ-๐๐ญ๐ (f , g) = incl (ฮป x โ case x of โจ f โฉ โจ g โฉ)

    instance
      isCoproduct:โช-๐ซ-๐๐ญ๐ : isCoproduct U V (U โช V)
      isCoproduct.ฮนโ isCoproduct:โช-๐ซ-๐๐ญ๐ = ฮนโ-๐ซ-๐๐ญ๐
      isCoproduct.ฮนโ isCoproduct:โช-๐ซ-๐๐ญ๐ = ฮนโ-๐ซ-๐๐ญ๐
      isCoproduct.โฆ isCoproduct:โช-๐ซ-๐๐ญ๐ โฆ = โฆ_โฆ-๐ซ-๐๐ญ๐
      isCoproduct.isSetoidHom:โฆโฆ isCoproduct:โช-๐ซ-๐๐ญ๐ = record { cong-โผ = ฮป x โ tt }
      isCoproduct.reduce-ฮนโ isCoproduct:โช-๐ซ-๐๐ญ๐ = tt
      isCoproduct.reduce-ฮนโ isCoproduct:โช-๐ซ-๐๐ญ๐ = tt
      isCoproduct.expand-ฮนโ,ฮนโ isCoproduct:โช-๐ซ-๐๐ญ๐ = tt

  instance
    hasCoproducts:๐ซ-๐๐ญ๐ : hasCoproducts (๐ซ A)
    hasCoproducts:๐ซ-๐๐ญ๐ = record { _โ_ = _ }

  instance
    hasFiniteCoproducts:๐ซ-๐๐ญ๐ : hasFiniteCoproducts (๐ซ A)
    hasFiniteCoproducts:๐ซ-๐๐ญ๐ = hasFiniteCoproducts:default

----------------------------------------------------------
-- Indexed coproducts
----------------------------------------------------------

module _ {A : ๐๐ญ๐ ๐} where

  module _ {I : ๐ฐโ} {Uแตข : I -> ๐ซ A} where
    private
      U = โ-๐ซ-๐๐ญ๐ Uแตข

    ฮนแตข-๐ซ-๐๐ญ๐ : โ i -> Uแตข i โถ U
    ฮนแตข-๐ซ-๐๐ญ๐ i = incl ฮป x โ i , x

    โฆ_โฆแตข-๐ซ-๐๐ญ๐ : โ{V : ๐ซ A} -> (โ i -> Uแตข i โถ V) -> U โถ V
    โฆ_โฆแตข-๐ซ-๐๐ญ๐ fแตข = incl ฮป (i , xโV) โ โจ fแตข i โฉ xโV

    instance
      isIndexedCoproduct:โ-๐ซ-๐๐ญ๐ : isIndexedCoproduct Uแตข U
      isIndexedCoproduct.ฮนแตข isIndexedCoproduct:โ-๐ซ-๐๐ญ๐ = ฮนแตข-๐ซ-๐๐ญ๐
      isIndexedCoproduct.โฆ isIndexedCoproduct:โ-๐ซ-๐๐ญ๐ โฆแตข = โฆ_โฆแตข-๐ซ-๐๐ญ๐
      isIndexedCoproduct.reduce-ฮนแตข isIndexedCoproduct:โ-๐ซ-๐๐ญ๐ = ฮป f i โ tt
      isIndexedCoproduct.expand-ฮนแตข isIndexedCoproduct:โ-๐ซ-๐๐ญ๐ = ฮป f โ tt

  module _ {I : ๐ฐโ} where
    -- instance
    --   hasIndexedCoproducts:๐ซ-๐๐ญ๐ : hasIndexedCoproducts I (๐ซ A)
    --   hasIndexedCoproducts.โจแตข hasIndexedCoproducts:๐ซ-๐๐ญ๐ = โ-๐ซ-๐๐ญ๐
    --   hasIndexedCoproducts.isIndexedCoproduct:โจแตข hasIndexedCoproducts:๐ซ-๐๐ญ๐ = it

  instance
    hasAllIndexedCoproducts:๐ซ-๐๐ญ๐ : hasAllIndexedCoproducts โโ (๐ซ A)
    hasAllIndexedCoproducts.โจแตข hasAllIndexedCoproducts:๐ซ-๐๐ญ๐ = โ-๐ซ-๐๐ญ๐
    hasAllIndexedCoproducts.isIndexedCoproduct:โจแตข hasAllIndexedCoproducts:๐ซ-๐๐ญ๐ = it


