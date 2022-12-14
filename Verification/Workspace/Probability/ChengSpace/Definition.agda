
module Verification.Workspace.Probability.ChengSpace.Definition where

open import Verification.Conventions hiding (_โ_)
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Imports
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Definition
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.Category
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.HasCoproducts
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.HasProducts

module _ {X : ๐๐ญ๐ ๐} where
  infix 120 โซ_
  โซ_ : ๐๐ข๐ฌ๐๐๐ข๐ซ (๐ซ X) -> ๐๐ข๐ฌ๐๐๐ข๐ซ (๐ซ X)
  โซ_ (a , b because f) = b , a because (incl ฮป (a , b) โ โจ f โฉ (b , a))

  private
    testlem1 : โ{a} -> โซ โซ a โฃ a
    testlem1 = refl-โฃ

    testlem2 : โ{U V : ๐๐ข๐ฌ๐๐๐ข๐ซ (๐ซ X)} -> โซ (U โ V) โ (โซ U) โ (โซ V)
    testlem2 {U} {V} = f since record { inverse-โ = g ; inv-r-โ = tt ; inv-l-โ = tt }
      where
        f : โซ (U โ V) โถ (โซ U) โ (โซ V)
        f = id , id

        g : (โซ U) โ (โซ V) โถ โซ (U โ V)
        g = id , id


record isChengSpace (X : ๐๐ญ๐ ๐) : ๐ฐ (๐ โบ โบ) where
  field isComplementedPair : ๐๐ข๐ฌ๐๐๐ข๐ซ (๐ซ X) -> ๐ฐ ๐
  field closed-โฅ : isComplementedPair โฅ
  field closed-โซ : โ (P : ๐๐ข๐ฌ๐๐๐ข๐ซ (๐ซ X)) -> isComplementedPair P -> isComplementedPair (โซ P)
  field closed-โจ : (P : โ -> ๐๐ข๐ฌ๐๐๐ข๐ซ (๐ซ X)) -> (โ i -> isComplementedPair (P i)) -> isComplementedPair (โจแตข P)

  Compl : ๐ฐ _
  Compl = โ isComplementedPair

open isChengSpace {{...}} hiding (Compl) public
open isChengSpace using (Compl) public

module _ (X : ๐๐ญ๐ ๐) where
  isChengSpace:byDiscrete : isChengSpace X
  isChengSpace:byDiscrete = record
                              { isComplementedPair = ฮป x โ โค-๐ฐ
                              ; closed-โฅ = tt
                              ; closed-โซ = ฮป P x โ tt
                              ; closed-โจ = ฮป P x โ tt
                              }

module _ ๐ where
  ChengSpace = ๐๐ญ๐ ๐ :& isChengSpace

module _ {X : ChengSpace ๐} where
  isFull : ๐ซ (โณ X) -> ๐ฐ _
  isFull S = โ ฮป (P : Compl (of X)) -> fst (fst P) โ snd (fst P) โถ S


open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Ring.Domain
open import Verification.Core.Order.Linearorder

record Measure (R : OrderedRing ๐) (X : ChengSpace ๐) : ๐ฐ (๐ โบ โบ ๏ฝค ๐) where
  field ฮผ : Compl (of X) -> โจ R โฉ
  field M1 : โ{P : Compl (of X)} -> isFull {X = X} (snd (fst P)) -> ฮผ P โผ โ
  field M2 : โ{P Q : Compl (of X)} -> ฮผ P โ ฮผ Q โผ ฮผ (fst P โ fst Q , {!!}) โ ฮผ (fst P โ fst Q , {!!})

open Measure {{...}} public


----------------------------------------------------------
-- for security, we have

module _
      (R : OrderedRing ๐)
      (M : ChengSpace ๐)
      {{MM : Measure R M}}
      where

  postulate instance
    _ : isSetoid {fst ๐} โจ M โฉ

  singleMsg : โจ M โฉ -> Compl (of M)
  singleMsg m = (((ฮป m' -> โฃ m' โผ m โฃ) since {!!}) , {!!} because {!!}) , {!!}

  attacker : (m : โจ M โฉ) -> ฮผ (singleMsg m) โผ {!!}
  attacker = {!!}






