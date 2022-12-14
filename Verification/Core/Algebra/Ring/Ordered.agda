
module Verification.Core.Algebra.Ring.Ordered where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Ring.Domain
open import Verification.Core.Order.Linearorder

module _ {๐ : ๐ ^ 2} where
  record isOrderedRing (๐ : ๐) (R : Ring ๐)  : ๐ฐ (๐ โบ ๏ฝค ๐ โบ) where
    field {{OProof}} : isLinearorder ๐ โฒ โจ R โฉ โฒ
    field stronglyMonotone-l-โ : โ{a b : โจ R โฉ} -> a < b -> โ {c} -> a โ c < b โ c
          preservesPositivity-โ : โ{a b : โจ R โฉ} -> โ < a -> โ < b -> โ < a โ b

  open isOrderedRing {{...}} public

module _ (๐ : ๐ ^ 3) where
  OrderedRing = Ring (๐ โ 0 โฏ 1) :& isOrderedRing (๐ โ 2)


module _ {๐ : ๐ ^ 2} {๐ : ๐} where
  module _ {R : ๐ฐ _} {_ : Ring ๐ on R} {{_ : isOrderedRing ๐ โฒ R โฒ}} where

    stronglyMonotone-r-โ : โ{c} -> โ{a b : R} -> (a < b) -> c โ a < c โ b
    stronglyMonotone-r-โ {c} {a} {b} p =
      c โ a   โจ comm-โ โฉ-โผ-<
      a โ c   โจ stronglyMonotone-l-โ p โฉ-<-โผ
      b โ c   โจ comm-โ โฉ-โผ
      c โ b   โ

    stronglyMonotone-l-โ : โ{a b c : R} -> a < b -> (โ < c) -> a โ c < b โ c
    stronglyMonotone-l-โ {a} {b} {c} p q = Pโ
      where
          Pโ = โ       โจ inv-r-โ โปยน โฉ-โผ-<
              a โ โก a  โจ stronglyMonotone-l-โ p โฉ-<-โผ
              b โ โก a  โ-โผ

          Pโ = โ                โจ preservesPositivity-โ Pโ q โฉ-<-โผ
               (b โ โก a) โ c    โจ distr-r-โ โฉ-โผ
               b โ c โ โก a โ c  โ-โผ

          Pโ = a โ c                      โจ unit-l-โ โปยน โฉ-โผ-<
               โ โ a โ c                  โจ stronglyMonotone-l-โ Pโ โฉ-<-โผ
               (b โ c โ โก a โ c) โ a โ c   โจ assoc-l-โ โฉ-โผ
               b โ c โ (โก a โ c โ a โ c)   โจ refl โโโ (switch-โก-โ-l โปยน โโโ refl) โฉ-โผ
               b โ c โ (โก(a โ c) โ a โ c)  โจ refl โโโ inv-l-โ โฉ-โผ
               b โ c โ โ                  โจ unit-r-โ โฉ-โผ
               b โ c                      โ



  isPositive : {R : ๐ฐ _} {{_ : Ring ๐ on R}} {{_ : isOrderedRing ๐ โฒ R โฒ}} -> R -> ๐ฐ _
  isPositive a = โ < a

  -- isNonNegative : {R : ๐ฐ _} {{_ : Ring ๐ on R}} {{_ : isOrderedRing ๐ โฒ R โฒ}} -> R -> ๐ฐ _
  -- isNonNegative a = โ < a

  -- record isDecidable-OrderedRing (R : Ring ๐ :& isOrderedRing ๐) : ๐ฐ (๐ โบ ๏ฝค ๐ โบ) where
  --   field overlap {{DecOProof}} : (isTotalorder :> isDecidable-Totalorder) โฒ โจ R โฉ โฒ

  module _ {R : Ring ๐}
           -- {{_ : isDomain R}}
           {{_ : isOrderedRing ๐ R}} where
           -- {{_ : isDecidable-OrderedRing โฒ โจ R โฉ โฒ}} where

    -- stronglyMonotone-l-โ

    cancel-โ-<-r : โ{a b c : โจ R โฉ} -> a โ c < b โ c -> isPositive c -> a < b
    cancel-โ-<-r = {!!}

    -- module _ {R : Ring ๐}
    --         -- {{_ : isDomain R}}
    --         {{_ : isOrderedRing ๐ R}} where
    --   instance


    -- NOTE: We do not make this an instance, since not every domain structures comes from an ordered ring structure.
    isDomain:OrderedRing : isDomain R
    isDomain.domain isDomain:OrderedRing = {!!}



{-








{-
  record isDecidable-OrderedRing (R : Ring ๐ :& isOrderedRing ๐) : ๐ฐ (๐ โบ ๏ฝค ๐ โบ) where
    field overlap {{DecOProof}} : (isTotalorder :> isDecidable-Totalorder) โฒ โจ R โฉ โฒ

-- module _ {๐ : ๐ ^ 2} {๐ : \}
  module _ (R : Ring ๐) {{_ : isOrderedRing ๐ R}} {{_ : isDecidable-OrderedRing โฒ โจ R โฉ โฒ}} where

    -- isPositive-โจก : isPositive โจก
    -- isPositive-โจก with compare โ โจก
    -- ... | LT x = {!!}
    -- ... | EQ x = transp-< {!!} {!!} refl-<
    -- ... | GT x = {!!}

-}
-}


