
module Verification.Core.Order.DedekindCompletion.Definition3 where

open import Verification.Conventions
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Rational.Definition

open import Verification.Core.Setoid
open import Verification.Core.Order.Linearorder

-- mostly from https://ncatlab.org/nlab/show/real+number
-- and https://ncatlab.org/nlab/show/Dedekind+cut


-- record isSubsetoid' {š : š ^ 2} {A : Setoid š} (P : āØ A ā© -> š° š) : š° (š ļ½¤ š) where
record isSubsetoid' {š : š ^ 2} {A} {{_ : Setoid š on A}} (P : A -> Prop š) : š° (š ļ½¤ š) where
  field transp-ā¼' : ā{a b : A} -> a ā¼ b -> a ā P -> b ā P

open isSubsetoid' {{...}} public

Subsetoid' : {š : š ^ 2} (X : Setoid š) (š : š) -> š° _
Subsetoid' X š = (āØ X ā© -> Prop š):& isSubsetoid'

-- instance
--   isEquivRel:ā«' : ā{š : š ^ 2} {š : š} -> ā{A : Setoid š} -> isEquivRel (ā¼-Base (Ī» (P Q : Subsetoid' A š) -> āØ P ā© ā« āØ Q ā©))
--   isEquivRel.refl isEquivRel:ā«' = incl ((Ī» x -> x) , (Ī» x -> x))
--   isEquivRel.sym isEquivRel:ā«' (incl (P , Q)) = incl (Q , P)
--   isEquivRel._ā_ isEquivRel:ā«' (incl (Pā , Qā)) (incl (Pā , Qā)) = incl ((Ī» x -> Pā (Pā x)) , (Ī» x -> Qā (Qā x)))

instance
  isSetoid:Subsetoid' : ā{š : š ^ 2} {š : š} -> {X : Setoid š} -> isSetoid _ (Subsetoid' X š)
  isSetoid._ā¼'_ isSetoid:Subsetoid' A B = āØ A ā© ā¼ āØ B ā©
  isSetoid.isEquivRel:ā¼ isSetoid:Subsetoid' = {!!}
  -- isSetoid.myRel isSetoid:Subsetoid A B = āØ A ā© ā« āØ B ā©


module _ {š : š ^ 3} (X : Linearorder š) (š : š) where

  record isCut (L U : Subsetoid' ā² āØ X ā© ā² š) : š° (š ļ½¤ š) where
    constructor iscut
    field inhabited-ā© : ā¦ āØ L ā© ā¦
    field inhabited-ā© : ā¦ āØ U ā© ā¦
    field open-ā© : ā{a : āØ X ā©} -> a ā L -> ā Ī» (b : ā¦ āØ L ā© ā¦) -> a < āØ b ā©
    field open-ā© : ā{b : āØ X ā©} -> b ā U -> ā Ī» (a : ā¦ āØ U ā© ā¦) -> āØ a ā© < b
    field compare-Cut : ā{a b : āØ X ā©} -> a < b -> (a ā L) +-š° (b ā U)
    field by-ā©ā©-< : ā{a b : āØ X ā©} -> a ā L -> b ā U -> a < b

  open isCut {{...}} public

  record Cut : š° (((š .fst) āŗ) ā š ā 1 ā š ā 2 ā (š āŗ)) where
    constructor _,_
    field ā© : Subsetoid' ā² āØ X ā© ā² š
    field ā© : Subsetoid' ā² āØ X ā© ā² š
    field {{isCutProof}} : isCut ā© ā©

  open Cut public



module _ {š : š ^ 3} {X : Linearorder š} {š : š} where
  _<L_ : āØ X ā© -> Cut X š -> š° _
  _<L_ a (L , U) = a ā L

  _U<_ : Cut X š -> āØ X ā© -> š° _
  _U<_ (L , U) b = b ā U

  infix 40 _U<_ _<L_ _<-Cut_

  _<-Cut_ : Cut X š -> Cut X š -> š° _
  _<-Cut_ x y = ā Ī» a -> (x U< a Ć-š° a <L y)

  instance
    isSetoid:Cut : isSetoid āā (Cut X š)
    isSetoid:Cut = {!!}
    -- isSetoid._ā¼'_ isSetoid:Cut (Lā , Uā) (Lā , Uā) = (Lā ā¼ Lā) Ć-š° (Uā ā¼ Uā)
    -- isEquivRel.refl (isSetoid.isEquivRel:ā¼ isSetoid:Cut) = incl (refl , refl)
    -- isEquivRel.sym (isSetoid.isEquivRel:ā¼ isSetoid:Cut) (incl (p , q)) = incl (sym p , sym q)
    -- isEquivRel._ā_ (isSetoid.isEquivRel:ā¼ isSetoid:Cut) (incl (p0 , q0)) (incl (p1 , q1)) = incl (p0 ā p1 , q0 ā q1)


  disjoint-ā©ā© : ā{ā©a ā©a} -> {{_ : isCut X š ā©a ā©a}} -> ā{x : āØ X ā©} -> x ā ā©a -> x ā ā©a -> š-š°
  disjoint-ā©ā© p q = irrefl-< (by-ā©ā©-< p q)

  closed-ā© : ā{ā©a ā©a} -> {{_ : isCut X š ā©a ā©a}} -> ā{x y : āØ X ā©} -> (x < y) -> y ā ā©a -> x ā ā©a
  closed-ā© {ā©a} {ā©a} {x} {y} x<y y-ā©a = case compare-Cut x<y of
                   (Ī» (p : x ā ā©a) -> p)
                   (Ī» (p : y ā ā©a) -> š-rec (disjoint-ā©ā© y-ā©a p))

  closed-ā© : ā{ā©a ā©a} -> {{_ : isCut X š ā©a ā©a}} -> ā{x y : āØ X ā©} -> (x < y) -> x ā ā©a -> y ā ā©a
  closed-ā© {ā©a} {ā©a} {x} {y} x<y x-ā©a = case compare-Cut x<y of
                   (Ī» (p : x ā ā©a) -> š-rec (disjoint-ā©ā© p x-ā©a))
                   (Ī» (p : y ā ā©a) -> p)




{-
{-
-}

-}
