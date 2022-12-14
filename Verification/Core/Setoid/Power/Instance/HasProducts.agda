
module Verification.Core.Setoid.Power.Instance.HasProducts where

open import Verification.Core.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition

open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Setoid.Power.Intersection


----------------------------------------------------------
-- Binary products
----------------------------------------------------------
module _ {A : ๐๐ญ๐ ๐} where

  intro-โค-๐ซ-๐๐ญ๐ : โ{U : ๐ซ A} -> U โถ โง
  intro-โค-๐ซ-๐๐ญ๐ = incl (ฮป aโU โ tt)

  instance
    isTerminal:โง-๐ซ-๐๐ญ๐ : isTerminal {๐ = ๐ซ A} โง-๐ซ-๐๐ญ๐
    isTerminal:โง-๐ซ-๐๐ญ๐ = record
      { intro-โค = intro-โค-๐ซ-๐๐ญ๐
      ; expand-โค = tt
      }

  instance
    hasTerminal:๐ซ-๐๐ญ๐ : hasTerminal (๐ซ A)
    hasTerminal.โค hasTerminal:๐ซ-๐๐ญ๐ = โง
    hasTerminal.isTerminal:โค hasTerminal:๐ซ-๐๐ญ๐ = it

  module _ {U V : ๐ซ A} where

    ฯโ-๐ซ-๐๐ญ๐ : U โฉ V โถ U
    ฯโ-๐ซ-๐๐ญ๐ = incl (ฮป aโUโฉV โ fst aโUโฉV)

    ฯโ-๐ซ-๐๐ญ๐ : U โฉ V โถ V
    ฯโ-๐ซ-๐๐ญ๐ = incl (ฮป aโUโฉV โ snd aโUโฉV)

    โงผ_โงฝ-๐ซ-๐๐ญ๐ : โ{X} -> (X โถ U) ร-๐ฐ (X โถ V) -> X โถ U โฉ V
    โงผ_โงฝ-๐ซ-๐๐ญ๐ (f , g) = incl ฮป xโX โ โจ f โฉ xโX , โจ g โฉ xโX

    instance
      isProduct:โฉ-๐ซ-๐๐ญ๐ : isProduct U V (U โฉ V)
      isProduct.ฯโ isProduct:โฉ-๐ซ-๐๐ญ๐ = ฯโ-๐ซ-๐๐ญ๐
      isProduct.ฯโ isProduct:โฉ-๐ซ-๐๐ญ๐ = ฯโ-๐ซ-๐๐ญ๐
      isProduct.โงผ isProduct:โฉ-๐ซ-๐๐ญ๐ โงฝ = โงผ_โงฝ-๐ซ-๐๐ญ๐
      isProduct.isSetoidHom:โงผโงฝ isProduct:โฉ-๐ซ-๐๐ญ๐ = record { cong-โผ = ฮป x โ tt }
      isProduct.reduce-ฯโ isProduct:โฉ-๐ซ-๐๐ญ๐ = tt
      isProduct.reduce-ฯโ isProduct:โฉ-๐ซ-๐๐ญ๐ = tt
      isProduct.expand-ฯโ,ฯโ isProduct:โฉ-๐ซ-๐๐ญ๐ = tt

  instance
    hasProducts:๐ซ-๐๐ญ๐ : hasProducts (๐ซ A)
    hasProducts:๐ซ-๐๐ญ๐ = record { _โ_ = _ }

  instance
    hasFiniteProducts:๐ซ-๐๐ญ๐ : hasFiniteProducts (๐ซ A)
    hasFiniteProducts:๐ซ-๐๐ญ๐ = hasFiniteProducts:default

----------------------------------------------------------
-- Indexed products
----------------------------------------------------------

module _ {A : ๐๐ญ๐ ๐} where

  module _ {I : ๐ฐโ} {Uแตข : I -> ๐ซ A} where
    private
      U = โ-๐ซ-๐๐ญ๐ Uแตข

    ฯแตข-๐ซ-๐๐ญ๐ : โ i -> U โถ Uแตข i
    ฯแตข-๐ซ-๐๐ญ๐ i = incl (ฮป x โ x i)

    โงผ_โงฝแตข-๐ซ-๐๐ญ๐ : โ{V : ๐ซ A} -> (โ i -> V โถ Uแตข i) -> V โถ U
    โงผ_โงฝแตข-๐ซ-๐๐ญ๐ fแตข = incl ฮป xโV i โ โจ fแตข i โฉ xโV

    instance
      isIndexedProduct:โ-๐ซ-๐๐ญ๐ : isIndexedProduct Uแตข U
      isIndexedProduct.ฯแตข isIndexedProduct:โ-๐ซ-๐๐ญ๐ = ฯแตข-๐ซ-๐๐ญ๐
      isIndexedProduct.โงผ isIndexedProduct:โ-๐ซ-๐๐ญ๐ โงฝแตข = โงผ_โงฝแตข-๐ซ-๐๐ญ๐
      isIndexedProduct.reduce-ฯแตข isIndexedProduct:โ-๐ซ-๐๐ญ๐ = ฮป f i โ tt
      isIndexedProduct.expand-ฯแตข isIndexedProduct:โ-๐ซ-๐๐ญ๐ = ฮป f โ tt

  -- module _ {I : ๐ฐโ} where
  --   instance
  --     hasIndexedProducts:๐ซ-๐๐ญ๐ : hasIndexedProducts I (๐ซ A)
  --     hasIndexedProducts.โจแตข hasIndexedProducts:๐ซ-๐๐ญ๐ = โ-๐ซ-๐๐ญ๐
  --     hasIndexedProducts.isIndexedProduct:โจแตข hasIndexedProducts:๐ซ-๐๐ญ๐ = it
  instance
    hasAllIndexedProducts:๐ซ-๐๐ญ๐ : hasAllIndexedProducts โโ (๐ซ A)
    hasAllIndexedProducts.โจแตข hasAllIndexedProducts:๐ซ-๐๐ญ๐ = โ-๐ซ-๐๐ญ๐
    hasAllIndexedProducts.isIndexedProduct:โจแตข hasAllIndexedProducts:๐ซ-๐๐ญ๐ = it






