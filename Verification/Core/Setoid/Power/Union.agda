
module Verification.Core.Setoid.Power.Union where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Power.Definition


----------------------------------------------------------
-- Finitary intersections
----------------------------------------------------------

module _ {A : ๐๐ญ๐ ๐} where

  module _
         {U : โจ A โฉ -> Prop _} {{_ : isSubsetoid U}}
         {V : โจ A โฉ -> Prop _} {{_ : isSubsetoid V}}
         where
    instance
      isSubsetoid:โช-๐ซ-๐๐ญ๐ : isSubsetoid (U โชแต V)
      isSubsetoid:โช-๐ซ-๐๐ญ๐ = record
        { transp-โผ = ฮป aโผb aโ -> case aโ of
                                         (ฮป aโU -> left (transp-โผ aโผb aโU))
                                         ฮป aโV -> right (transp-โผ aโผb aโV)
        }

  _โช-๐ซ-๐๐ญ๐_ : ๐ซ A -> ๐ซ A -> ๐ซ A
  _โช-๐ซ-๐๐ญ๐_ U V = U โช V



  instance
    isSubsetoid:โ-๐ซ-๐๐ญ๐ : isSubsetoid {X = โจ A โฉ} โ
    isSubsetoid:โ-๐ซ-๐๐ญ๐ = record
      { transp-โผ = ฮป aโผb ()
      }

  โ-๐ซ-๐๐ญ๐ : ๐ซ A
  โ-๐ซ-๐๐ญ๐ = โ


----------------------------------------------------------
-- Indexed intersections
----------------------------------------------------------

module _ {A : ๐๐ญ๐ ๐} {I : ๐ฐโ} where
  -- module _ {Uแตข : I -> โจ A โฉ -> Prop _} {{_ : โ{i} -> isSubsetoid (Uแตข i)}} where
  module _ (Uแตข : I -> ๐ซ A) where
    instance
      isSubsetoid:โ-๐ซ-๐๐ญ๐ : isSubsetoid (โแต Uแตข)
      isSubsetoid:โ-๐ซ-๐๐ญ๐ = record
        { transp-โผ = ฮป aโผb (i , aแตขโU) โ i , transp-โผ {{_}} {{of Uแตข i}} aโผb (aแตขโU)
        }

  โ-๐ซ-๐๐ญ๐ : (Uแตข : I -> ๐ซ A) -> ๐ซ A
  โ-๐ซ-๐๐ญ๐ Uแตข = โแต Uแตข since isSubsetoid:โ-๐ซ-๐๐ญ๐ Uแตข



