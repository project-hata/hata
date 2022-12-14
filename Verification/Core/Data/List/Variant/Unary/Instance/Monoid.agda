
module Verification.Core.Data.List.Variant.Unary.Instance.Monoid where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Variant.Unary.Definition

-- [Lemma]
-- | The type |List A| has a monoid structure,
--   where |as β bs| is given by appending the lists.

-- //

-- [Hide]
module _ {A : π° π} where
  module ListProofs where

    -- | The |<>| operation on lists is unital.
    lem-1 : β{a : List A} -> a <> [] β£ a
    lem-1 {[]} = refl-β£
    lem-1 {x β· a} = congβ-Str _β·_ refl-β£ lem-1

    -- | And it is associative.
    lem-2 : β{a b c : List A} -> (a <> b) <> c β£ a <> (b <> c)
    lem-2 {[]} = refl-β£
    lem-2 {x β· a} = congβ-Str _β·_ refl-β£ (lem-2 {a})

  open ListProofs

    -- | This means that lists are a monoid.

  instance
    isMonoid:List : isMonoid β²(List A)β²
    isMonoid:List = record
                      { _β_ = _<>_
                      ; β = []
                      ; unit-l-β = refl
                      ; unit-r-β = lem-1
                      ; assoc-l-β = Ξ» {a} {b} {c} -> lem-2 {a} {b} {c}
                      ; _βββ_ = {!!}
                      }


module _ {A : π° π} {B : π° _} {{_ : B is Monoid π}} where
  rec-List : (f : A -> B) -> List A -> B
  rec-List f [] = β
  rec-List f (a β· as) = f a β rec-List f as

  instance
    Notation:hasRec:List : Notation:hasRec (A -> B) (List A -> B)
    Notation:hasRec:List = record { rec = rec-List }

-- //

