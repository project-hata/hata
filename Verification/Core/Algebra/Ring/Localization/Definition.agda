
module Verification.Core.Algebra.Ring.Localization.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
-- open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition

-- Multiplicatively closed set

record isMCS {๐ : ๐ ^ 2} (R : CRing ๐) (A : ๐ซ โจ R โฉ :& isSubsetoid) : ๐ฐ ๐ where
  field closed-โ : โ{a b : โจ R โฉ} -> a โ A -> b โ A -> (a โ b) โ โจ A โฉ
  field closed-โจก : โจก โ A
open isMCS {{...}} public

MCS : CRing ๐ -> ๐ฐ _
MCS R = ๐ซ โจ R โฉ :& isSubsetoid :& isMCS R

module _ {๐ : ๐ ^ 2} {R : CRing ๐} where
  record hasNotZero-MCS (M : MCS R) : ๐ฐ ๐ where
    field isNotZero-MCS : โ{a : โจ R โฉ} -> a โ M -> a โ โ

  open hasNotZero-MCS {{...}} public

-- record Localize {๐ : ๐ ^ 2} (R : CRing ๐) (M : MCS R) : ๐ฐ ๐ where
--   no-eta-equality
--   pattern
--   constructor _/_
--   field locโ : โจ R โฉ
--   field locโ : โฆ โจ M โฉ โฆ
-- open Localize public

data Localize {๐ : ๐ ^ 2} (R : CRing ๐) (M : MCS R) : ๐ฐ ๐ where
  _/_ : โจ R โฉ -> โฆ โจ M โฉ โฆ -> Localize R M

module _ {๐ : ๐ ^ 2} {R : CRing ๐} {M : MCS R} where
  locโ : Localize R M -> โจ R โฉ
  locโ (a / b) = a

  locโ : Localize R M -> โฆ โจ M โฉ โฆ
  locโ (a / b) = b

module _ {๐ : ๐ ^ 2} {R : ๐ฐ _} {M : ๐ซ R} {{_ : CRing ๐ on R}} {{_ : MCS โฒ R โฒ on M}} where
  _โ-MCS_ : โฆ M โฆ -> โฆ M โฆ -> โฆ M โฆ
  _โ-MCS_ (a โข aP) (b โข bP) = ((a โ b) โข closed-โ aP bP)
  โจก-MCS : โฆ M โฆ
  โจก-MCS = โจก โข closed-โจก

module _ {๐ : ๐ ^ 2} {R : CRing ๐} {M : MCS R} where
  embed-Localize : โจ R โฉ -> Localize R M
  embed-Localize r = r / โจก-MCS

