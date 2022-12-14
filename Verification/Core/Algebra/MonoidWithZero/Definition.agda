
module Verification.Core.Algebra.MonoidWithZero.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Decidable
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition


record hasZero (A : Monoid π) : π° π where
  field β : β¨ A β©
  field absorb-r-β : β{a : β¨ A β©} -> a β β βΌ β
  field absorb-l-β : β{a : β¨ A β©} -> β β a βΌ β
  field decide-β : (a : β¨ A β©) -> isDecidable (a βΌ β)
open hasZero {{...}} public

Monoidβ : β π -> π° _
Monoidβ π = Monoid π :& hasZero

module _ (π) where
  macro ππ¨π§β = #structureOn (Monoidβ π)

-- record zeroIsDecidable (A : Monoidβ π) : π° π where
--   field decide-β : (a : β¨ A β©) -> isDecidable (a βΌ β)
-- open zeroIsDecidable {{...}} public




