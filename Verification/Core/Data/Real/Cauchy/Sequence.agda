
module Verification.Core.Data.Real.Cauchy.Sequence where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Int.Definition

open import Verification.Core.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Algebra.Ring.Localization
open import Verification.Core.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Core.Algebra.Ring.Localization.Instance.OrderedRing
open import Verification.Core.Algebra.Field.Definition
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder
open import Verification.Core.Data.Rational.Definition
open import Verification.Core.Data.Rational.Inclusion

open AbelianMonoidNotation


record Sequence (A : ð° ð) : ð° ð where
  field ix : â -> A

open Sequence public

module _ {A : ð° ð} where
  instance
    Index-Notation:Sequence : Index-Notation (Sequence A) (const â) (Î» _ -> â¤-ð° {ââ}) (const A)
    Index-Notation:Sequence = record { _â_ = Î» x i â ix x i }

  instance
    hasU:Sequence : hasU (Sequence A) _ _
    hasU:Sequence = hasU:Base (Sequence A)


record isRegular (x : Sequence â) : ð°â where
  field reg : â(m n : â) -> â£ ((x â m) + - (x â n)) â£ < â(Î¹ (suc m)) + â(Î¹ (suc n))

Realá¶ : ð° _
Realá¶ = _ :& isRegular

macro âá¶ = #structureOn Realá¶

instance
  Index-Notation:Realá¶ : Index-Notation (Realá¶) (const â) (Î» _ -> â¤-ð° {ââ}) (const â)
  Index-Notation:Realá¶ = record { _â_ = Î» x i â ix â¨ x â© i }

record _â¼-âá¶_ (x y : âá¶) : ð°â where
  constructor incl
  field sim-âá¶ : â(n : â) -> â£ (x â n) + - (y â n) â£ < 2 â â(Î¹ (suc n))

open _â¼-âá¶_ public

private
  lem-1 : â{x : âá¶} -> x â¼-âá¶ x
  lem-1 = {!!}
  -- â¨ lem-1 â© n = {!!}

  lem-2 : â{x y : âá¶} -> x â¼-âá¶ y -> y â¼-âá¶ x
  lem-2 = {!!}

  lem-3 : â{x y z : âá¶} -> x â¼-âá¶ y -> y â¼-âá¶ z -> x â¼-âá¶ z
  lem-3 = {!!}

instance
  isSetoid:âá¶ : isSetoid âá¶
  isSetoid:âá¶ = isSetoid:byDef _â¼-âá¶_ lem-1 lem-2 lem-3

instance
  isMonoid:âá¶ : isMonoid âá¶
  isMonoid:âá¶ = {!!}

instance
  isGroup:âá¶ : isGroup âá¶
  isGroup:âá¶ = {!!}

instance
  isCommutative:âá¶ : isCommutative âá¶
  isCommutative:âá¶ = {!!}

instance
  isSemiring:âá¶ : isSemiring âá¶
  isSemiring:âá¶ = {!!}

instance
  isRing:âá¶ : isRing âá¶
  isRing:âá¶ = record {}

instance
  isField:âá¶ : isField âá¶
  isField:âá¶ = {!!}

instance
  isOrderedRing:âá¶ : isOrderedRing ââ âá¶
  isOrderedRing:âá¶ = {!!}

-- NOTE: this should actually be derived from ordered ring
instance
  isPreorder:âá¶ : isPreorder ââ âá¶
  isPreorder:âá¶ = {!!}


