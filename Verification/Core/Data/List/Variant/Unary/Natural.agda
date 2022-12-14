
module Verification.Core.Data.List.Variant.Unary.Natural where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
-- open import Verification.Core.Data.Nat.Definition


-- [Remark]
-- | Lists of the type |List â¤-ð°|, where every element has to
--   be given by the only constructor |tt| of |â¤-ð°|, are fully
--   determined by their length. An isomorphism |â â List â¤-ð°|
--   can be easily shown (NOTE: is this foreshadowing allowed?).
--   When using other list based constructions (such as?), it is then
--   easier to also use these as the definition of natural numbers,
--   for instance for specifying the length of a list.
-- | We give these lists a special name.

â®âáµ : ð°â
â®âáµ = List â¤-ð°

-- #Notation/Rewrite# â®âáµ = âáµ
-- //

-- [Hide]
macro â®â = #structureOn â®âáµ

Î¹-â®â : â -> â®â
Î¹-â®â zero = []
Î¹-â®â (suc n) = tt â· Î¹-â®â n

instance
  fromNatâ®â : HasFromNat â®â
  fromNatâ®â = record { Constraint = Î» _ â ð-ð° ; fromNat = Î» n -> Î¹-â®â n }

instance
  isSetoid:â®â : isSetoid â®â
  isSetoid:â®â = isSetoid:byId
-- //


