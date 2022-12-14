
module Verification.Core.Data.Int.Instance.Order where

open import Verification.Core.Conventions hiding (â)

open import Verification.Core.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder
open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Instance.Order
open import Verification.Core.Data.Nat.Instance.Monoid
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Int.Instance.Monoid
open import Verification.Core.Data.Int.Instance.Ring

--------------------------------------------------------------------
-- Ordering

data _<-âĪ_ : Int -> Int -> ð°â where
  pos : â{m n} -> m <-â n -> pos m <-âĪ pos n
  negsuc : â{m n} -> m <-â n -> negsuc n <-âĪ negsuc m
  negsucpos : â{m n} -> negsuc m <-âĪ pos n

data _âĪ-âĪ_ : Int -> Int -> ð°â where
  pos : â{m n} -> m âĪ n -> pos m âĪ-âĪ pos n
  negsuc : â{m n} -> m âĪ n -> negsuc n âĪ-âĪ negsuc m
  negsucpos : â{m n} -> negsuc m âĪ-âĪ pos n



-- pos n <-âĪ pos m = n <-â m
-- pos n <-âĪ negsuc m = ð-ð°
-- negsuc n <-âĪ pos m = ð-ð°
-- negsuc n <-âĪ negsuc m = m <-â n

-- _<-âĪ_ : Int -> Int -> ð° _
-- pos n <-âĪ pos m = n <-â m
-- pos n <-âĪ negsuc m = ð-ð°
-- negsuc n <-âĪ pos m = ð-ð°
-- negsuc n <-âĪ negsuc m = m <-â n

-- compare-<-â : {a c : â} -> (Base< _<-â_ a c) -> (b : â) -> (Base< _<-â_ a b) +-ð° (Base< _<-â_ b c)
-- compare-<-â {a} {c} p b with compare-â a b | compare-â b c
-- ... | lt x | Y = left (incl x)
-- ... | eq refl-StrId | Y = right p
-- ... | gt x | lt y = right (incl y)
-- ... | gt x | eq refl-StrId = left p
-- ... | gt x | gt y = ð-rec (ÂŽm<m (<-trans (<-trans (Base<.Proof p) y) x))


-- compare-<-âĪ : {a c : âĪ} -> (Base< _<-âĪ_ a c) -> (b : âĪ) -> (Base< _<-âĪ_ a b) +-ð° (Base< _<-âĪ_ b c)
-- compare-<-âĪ {.(pos _)} {.(pos _)} (incl (pos x)) (pos n) with compare-<-â (incl x) n
-- ... | left (incl q) = left (incl (pos q))
-- ... | just (incl q) = right (incl (pos q))
-- compare-<-âĪ {.(pos _)} {.(pos _)} (incl (pos x)) (negsuc n) = right (incl negsucpos)
-- compare-<-âĪ {.(negsuc _)} {.(negsuc _)} (incl (negsuc x)) (pos n) = left (incl negsucpos)
-- compare-<-âĪ {.(negsuc _)} {.(negsuc _)} (incl (negsuc x)) (negsuc n) with compare-<-â (incl x) n
-- ... | left (incl q) = right (incl (negsuc q))
-- ... | just (incl q) = left (incl (negsuc q))
-- compare-<-âĪ {.(negsuc _)} {.(pos _)} (incl negsucpos) (pos n) = left (incl negsucpos)
-- compare-<-âĪ {.(negsuc _)} {.(pos _)} (incl negsucpos) (negsuc n) = right (incl negsucpos)


instance
  isPreorder:âĪ : isPreorder _ âĪ
  isPreorder:âĪ = record
    { _âĪ_ = âĪ-Base _âĪ-âĪ_
    ; reflexive = lem-10
    ; _âĄ_ = lem-20
    ; transp-âĪ = lem-30
    }
    where
      _âĪ1_ : âĪ -> âĪ -> ð° _
      _âĪ1_ = âĪ-Base _âĪ-âĪ_

      lem-10 : â{a : âĪ} -> a âĪ1 a
      lem-10 {pos n} = incl (pos reflexive)
      lem-10 {negsuc n} = incl (negsuc reflexive)

      lem-20 : â{a b c : âĪ} -> a âĪ1 b -> b âĪ1 c -> a âĪ1 c
      lem-20 (incl (pos p)) (incl (pos q)) = incl (pos (p âĄ q))
      lem-20 (incl (negsuc p)) (incl (negsuc q)) = incl (negsuc (q âĄ p))
      lem-20 (incl (negsuc p)) (incl negsucpos) = incl negsucpos
      lem-20 (incl negsucpos) (incl (pos q)) = incl negsucpos

      lem-30 : â{a0 a1 b0 b1 : âĪ} -> a0 âž a1 -> b0 âž b1 -> a0 âĪ1 b0 -> a1 âĪ1 b1
      lem-30 (refl-StrId) (refl-StrId) r = r

instance
  isPartialorder:âĪ : isPartialorder âĪ
  isPartialorder:âĪ = record
    { antisym = lem-10
    }
    where
      _âĪ1_ : âĪ -> âĪ -> ð° _
      _âĪ1_ = âĪ-Base _âĪ-âĪ_

      lem-10 : â{a b} -> a âĪ1 b -> b âĪ1 a -> a âž b
      lem-10 (incl (pos p)) (incl (pos q)) = (cong-Str pos (antisym p q))
      lem-10 (incl (negsuc p)) (incl (negsuc q)) = (cong-Str negsuc (antisym q p))

instance
  isTotalorderâš:âĪ : isTotalorderâš âĪ
  isTotalorderâš:âĪ = record
    { totalâš = lem-10
    }
    where
      _âĪ1_ : âĪ -> âĪ -> ð° _
      _âĪ1_ = âĪ-Base _âĪ-âĪ_

      lem-10 : â(a b : âĪ) -> Trichotomy' âĪ a b
      lem-10 (pos m) (pos n) with totalâš m n
      ... | lt (x , p) = lt ((incl (pos x)) , Îŧ {(refl-StrId) â p (refl-StrId)})
      ... | eq (refl-StrId) = eq (refl-StrId)
      ... | gt (x , p) = gt ((incl (pos x)) , Îŧ {(refl-StrId) â p (refl-StrId)})
      lem-10 (pos n) (negsuc nâ) = gt ((incl negsucpos) , (Îŧ ()))
      lem-10 (negsuc n) (pos nâ) = lt ((incl negsucpos) , (Îŧ ()))
      lem-10 (negsuc m) (negsuc n) with totalâš m n
      ... | lt (x , p) = gt ((incl (negsuc x)) , Îŧ {(refl-StrId) â p (refl-StrId)})
      ... | eq (refl-StrId) = eq (refl-StrId)
      ... | gt (x , p) = lt ((incl (negsuc x)) , Îŧ {(refl-StrId) â p (refl-StrId)})


instance
  isLinearorder:âĪ : isLinearorder _ âĪ
  isLinearorder:âĪ = isLinearorder:Totalorderâš âĪ

instance
  isOrderedRing:âĪ : isOrderedRing _ âĪ
  isOrderedRing.OProof isOrderedRing:âĪ = isLinearorder:âĪ
  isOrderedRing.stronglyMonotone-l-â isOrderedRing:âĪ = {!!}
  isOrderedRing.preservesPositivity-â isOrderedRing:âĪ = {!!}
