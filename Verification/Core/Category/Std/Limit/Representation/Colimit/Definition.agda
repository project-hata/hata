
module Verification.Core.Category.Std.Limit.Representation.Colimit.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Representable2



module _ (๐ฅ : Category ๐) {๐ : Category ๐} where

  Coconst : ๐๐ฎ๐ง๐ ๐ (๐๐ฎ๐ง๐ ๐ฅ ๐ แตแต)
  Coconst = (ฮป x -> const x since isFunctor:const) since {!!}

  Const' : ๐๐ฎ๐ง๐ (๐ แตแต) (๐๐ฎ๐ง๐ ๐ฅ ๐ แตแต)
  Const' = {!!}

  Const'' : ๐๐ฎ๐ง๐ (๐) (๐๐ฎ๐ง๐ ๐ฅ ๐)
  Const'' = Const since isFunctor:Const

  module _ (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) where
    F2 : ๐๐ฎ๐ง๐ (๐๐ฎ๐ง๐ ๐ฅ ๐ แตแต) (๐๐ญ๐ _)
    F2 = โ๐๐ F

module _ {๐ฅ : Category ๐} {๐ : Category ๐} where

  isLimit : (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) -> โจ ๐ โฉ -> ๐ฐ _
  isLimit F x = isRepresented (Const' ๐ฅ โ-๐๐๐ญ โ๐๐ F) x

  isColimit : (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) -> โจ ๐ โฉ -> ๐ฐ _
  isColimit F x = isCorepresented (Const'' ๐ฅ โ-๐๐๐ญ โ๐๐แตแต F) x

  -- hasColimit : (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) -> ๐ฐ _
  -- hasColimit F = โ ฮป (x : โจ ๐ โฉ) -> isCorepresented (Coconst โ-๐๐๐ญ โ๐๐ F) x

--
-- we show that these colimits are the same as the ones
-- defined by cones
--

  open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition
    renaming (isColimit to isConeColimit)

  open import Verification.Core.Category.Std.Limit.Cone.Limit.Definition
    renaming (isLimit to isConeLimit)

  module _ (F : ๐๐ฎ๐ง๐ ๐ฅ ๐) (x : โจ ๐ โฉ) where
    prop-1 : isLimit F x -> isConeLimit F x
    prop-1 P =
      let ฯ : (Const' ๐ฅ โ-๐๐๐ญ โ๐๐ F) โ-Co๐๐๐ก โ๐๐ x
          ฯ = rep P

          ฮฑแต : โ(j : โจ ๐ฅ โฉ) -> x โถ โจ F โฉ j
          ฮฑแต j = let f = โจ inverse-โ-Co๐๐๐ก (of ฯ) โฉ (x)
                 in {!!} -- โจ โจ f โฉ id โฉ j
                 -- โจ f โฉ ({!!} since {!!})
                  -- โจ โจ ฯ โฉ (โจ F โฉ j) โฉ ?

      in record
        { limitCocone = {!!}
        ; limitUniversal = {!!}
        }
{-
-}



