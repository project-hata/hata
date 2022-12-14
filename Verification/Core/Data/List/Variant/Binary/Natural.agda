
module Verification.Core.Data.List.Variant.Binary.Natural where

open import Verification.Core.Conventions renaming (â to Nat)

open import Verification.Core.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Data.List.Variant.Binary
open import Verification.Core.Order.Preorder


äººâáµ : ð°â
äººâáµ = âList â¤-ð°

macro äººâ = #structureOn äººâáµ

Î¹-äººâ : Nat -> äººâ
Î¹-äººâ zero = â
Î¹-äººâ (suc n) = incl tt â Î¹-äººâ n

instance
  fromNatäººâ : HasFromNat äººâ
  fromNatäººâ = record { Constraint = Î» _ â ð-ð° ; fromNat = Î» n -> Î¹-äººâ n }


record _â¤-äººâ_ (a b : äººâ) : ð°â where
  constructor _,_
  field fst : äººâ
  field snd : a â fst â¼ b

open _â¤-äººâ_ public

reflexive-äººâ : â{a} -> a â¤-äººâ a
reflexive-äººâ = â , unit-r-â

_â¡-äººâ_ : â{a b c} -> a â¤-äººâ b -> b â¤-äººâ c -> a â¤-äººâ c
_â¡-äººâ_ {a} {b} {c} (b-a , p) (c-b , q) = (b-a â c-b) , r
  where
    r : a â (b-a â c-b) â¼ c
    r = a â (b-a â c-b)  â¨ assoc-r-â â©-â¼
        (a â b-a) â c-b  â¨ p âââ refl â©-â¼
        b â c-b          â¨ q â©-â¼
        c                â


instance
  isPreorder:â®â : isPreorder _ äººâ
  isPreorder:â®â = record { _â¤_ = _â¤-äººâ_ ; reflexive = reflexive-äººâ ; _â¡_ = _â¡-äººâ_ ; transp-â¤ = {!!} }


private
  lem-1 : â{a : äººâ} {t : â¤-ð°} -> incl t â a â¼ a â incl t
  lem-1 {incl tt} {tt} = refl
  lem-1 {a â-â§ b} {t} = p
    where
      p : incl t â (a â b) â¼ (a â b) â incl t
      p = incl t â (a â b) â¨ assoc-r-â â©-â¼
          (incl t â a) â b â¨ lem-1 âââ refl â©-â¼
          a â incl t â b   â¨ assoc-l-â â©-â¼
          a â (incl t â b) â¨ refl âââ lem-1 â©-â¼
          a â (b â incl t) â¨ assoc-r-â â©-â¼
          a â b â incl t   â

  lem-1 {â-â§} {t} = unit-r-â â unit-l-â â»Â¹

comm-â-äººâ : â{a b : äººâ} -> (a â b) â¼ b â a
comm-â-äººâ {incl x} {b} = lem-1
comm-â-äººâ {a â-â§ b} {c} = p â»Â¹
  where
    p : c â (a â b) â¼ (a â b) â c
    p = c â (a â b) â¨ assoc-r-â â©-â¼
        (c â a) â b â¨ comm-â-äººâ âââ refl â©-â¼
        a â c â b   â¨ assoc-l-â â©-â¼
        a â (c â b) â¨ refl âââ comm-â-äººâ â©-â¼
        a â (b â c) â¨ assoc-r-â â©-â¼
        a â b â c   â
comm-â-äººâ {â-â§} {b} = unit-l-â â unit-r-â â»Â¹

instance
  isCommutative:äººâ : isCommutative äººâ
  isCommutative:äººâ = record { comm-â = comm-â-äººâ }


-- instance
--   isPreorder:äººâ : isPreorder _ äººâ
--   isPreorder._â¤'_ isPreorder:äººâ = {!!}
--   isPreorder.reflexive isPreorder:äººâ = {!!}
--   isPreorder._â¡_ isPreorder:äººâ = {!!}
--   isPreorder.transp-â¤ isPreorder:äººâ = {!!}


monotone-l-â-äººâ : â{a b c : äººâ} -> a â¤ b -> c â a â¤ c â b
monotone-l-â-äººâ {a} {b} {c} (b-a , bap) = (b-a , p)
  where
    p : (c â a) â b-a â¼ c â b
    p = (c â a) â b-a â¨ assoc-l-â â©-â¼
        c â (a â b-a) â¨ refl âââ bap â©-â¼
        c â b         â


