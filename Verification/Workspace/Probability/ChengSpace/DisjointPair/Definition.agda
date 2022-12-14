
module Verification.Workspace.Probability.ChengSpace.DisjointPair.Definition where

open import Verification.Conventions hiding (_β_)
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Imports

-- Mostly following https://ncatlab.org/nlab/show/Cheng+space

-- CDL = Complete distributive lattice


record isCompleteLatticeCategory (π : Category π) : π° (π βΊ) where
  field {{hasIndexedProducts-CDL}}   : hasAllIndexedProducts ββ π
  field {{hasProducts-CDL}}          : hasFiniteProducts π
  field {{hasIndexedCoproducts-CDL}} : hasAllIndexedCoproducts ββ π
  field {{hasCoproducts-CDL}}        : hasFiniteCoproducts π

open isCompleteLatticeCategory {{...}} public

module _ π where
  CompleteLatticeCategory = Category π :& isCompleteLatticeCategory

record isDispairDistributive (π : CompleteLatticeCategory π) : π° (π βΊ) where
  -- field codist : β{a b c : β¨ π β©} -> a β (b β c) β (a β b) β (a β c)
  field dist : β{a b c : β¨ π β©} -> a β (b β c) β a β b β a β c
  field distα΅’ : β{I : π°β} {a : β¨ π β©} {b : I -> β¨ π β©} -> a β (β¨α΅’ b) β β¨[ i ] a β b i

open isDispairDistributive {{...}} public

module _ π where
  DCLC = Category π :& isCompleteLatticeCategory :& isDispairDistributive

module _ {A : ππ­π π} where
  instance
    isCompleteLatticeCategory:π«-ππ­π : isCompleteLatticeCategory (π« A)
    isCompleteLatticeCategory:π«-ππ­π = record {}

  instance
    isDispairDistributive:π«-ππ­π : isDispairDistributive (π« A)
    isDispairDistributive:π«-ππ­π = record { dist = lem1 ; distα΅’ = lem3 }


module _ (π : DCLC π) where
  record DisjointPair : π° (π βΊ) where
    constructor _,_because_
    field fst : β¨ π β©
    field snd : β¨ π β©
    field dis : fst β snd βΆ β₯

  open DisjointPair public

  macro ππ’π¬πππ’π« = #structureOn DisjointPair




