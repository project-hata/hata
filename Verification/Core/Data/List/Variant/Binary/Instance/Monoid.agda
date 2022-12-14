
module Verification.Core.Data.List.Variant.Binary.Instance.Monoid where

open import Verification.Core.Conventions hiding (β)

open import Verification.Core.Set.Decidable
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid




-- [Hide]
module _ {A : π° π} where
  private
    lem-1 : β{a c d : βList A} ->  (q : RST _βΌ-βList_ c d) -> RST _βΌ-βList_ (a β-β§ c) (a β-β§ d)
    lem-1 (incl x) = incl (cong-r-β-β§ x)
    lem-1 refl-RST = refl-RST
    lem-1 (sym-RST q) = sym-RST (lem-1 q)
    lem-1 (p β-RST q) = lem-1 p β-RST lem-1 q

  cong-β-β§ : β{a b c d : βList A} -> (p : RST _βΌ-βList_ a b) (q : RST _βΌ-βList_ c d) -> RST _βΌ-βList_ (a β-β§ c) (b β-β§ d)
  cong-β-β§ (incl x) q     = incl (cong-l-β-β§ x) β-RST lem-1 q
  cong-β-β§ refl-RST q     = lem-1 q
  cong-β-β§ (sym-RST p) q  = sym-RST (cong-β-β§ p (sym-RST q))
  cong-β-β§ (p β-RST p') q = cong-β-β§ p q β-RST cong-β-β§ p' refl-RST
-- //


-- [Lemma]
-- | Let [..] be a type.
module _ {A : π° π} where
  -- |> Then |βList A| is a monoid.
  instance
    isMonoid:βList : isMonoid (π₯ππΎπΎ-ππ¨π§ A)
    isMonoid:βList = record
      { _β_        = _β-β§_
      ; β          = β-β§
      ; unit-l-β   = incl unit-l-β-β§
      ; unit-r-β   = incl unit-r-β-β§
      ; assoc-l-β  = incl assoc-l-β-β§
      ; _βββ_      = cong-β-β§
      }

-- //

