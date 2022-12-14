
module Verification.Core.Algebra.Ring.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Abelian.Definition

module AbelianMonoidNotation where
  infixl 50 _+_
  infix 100 -_
  _+_ = _โ_
  -_ = โก_

open AbelianMonoidNotation

record isSemiring {๐ : ๐ ^ 2} (A : Monoid ๐ :& isCommutative) : ๐ฐ ๐ where
  field _โ_ : โจ A โฉ -> โจ A โฉ -> โจ A โฉ
        โจก : โจ A โฉ
        unit-l-โ : โ{a} -> โจก โ a โผ a
        unit-r-โ : โ{a} -> a โ โจก โผ a
        assoc-l-โ : โ{a b c} -> (a โ b) โ c โผ a โ (b โ c)
        distr-l-โ : โ{a b c : โจ A โฉ} -> a โ (b โ c) โผ a โ b โ a โ c
        distr-r-โ : โ{a b c : โจ A โฉ} -> (b โ c) โ a โผ b โ a โ c โ a
        _`cong-โ`_ : โ{aโ aโ bโ bโ} -> aโ โผ aโ -> bโ โผ bโ -> aโ โ bโ โผ aโ โ bโ
  _โโโ_ = _`cong-โ`_
  infixl 80 _โ_ _`cong-โ`_ _โโโ_
open isSemiring {{...}} public

Semiring : (๐ : ๐ ^ 2) -> ๐ฐ _
Semiring ๐ = (Monoid ๐ :& isCommutative) :& isSemiring


record isRing {๐ : ๐ ^ 2}(A : Monoid ๐ :& (isCommutative :> isSemiring) :, isGroup) : ๐ฐ ๐ where

Ring : (๐ : ๐ ^ 2) -> ๐ฐ _
Ring ๐ = (Monoid ๐ :& (isCommutative :> isSemiring) :, isGroup) :& isRing

-- instance
--   isRing:Any : โ{A : Monoid ๐ :& (isCommutative :> isSemiring) :, isGroup} -> isRing A
--   isRing:Any = record {}

record isCRing {๐ : ๐ ^ 2} (R : Ring ๐) : ๐ฐ ๐ where
  field comm-โ : โ{a b : โจ R โฉ} -> a โ b โผ b โ a
open isCRing {{...}} public

CRing : (๐ : ๐ ^ 2) -> ๐ฐ _
CRing ๐ = (Ring ๐) :& isCRing



module _ {๐ : ๐ ^ 2} {R : ๐ฐ _} {{_ : Ring ๐ on R}} where
-- module _ {๐ : ๐ ^ 2} {R' : Ring ๐} where
--   private
--     R = โจ R' โฉ

  infix 200 _ยฒ
  _ยฒ : R -> R
  _ยฒ a = a โ a

  assoc-r-โ : โ{a b c : R} -> a โ (b โ c) โผ a โ b โ c
  assoc-r-โ = assoc-l-โ โปยน

  reduce-โโ-r : โ{a : R} -> a โ โ โผ โ
  reduce-โโ-r {a} = cancel-โ-l P
    where P : a โ โ โ a โ โ โผ a โ โ โ โ
          P = a โ โ โ a โ โ     โฃโจ distr-l-โ โปยน โฉ
              a โ (โ โ โ)      โฃโจ refl `cong-โ` unit-r-โ โฉ
              a โ โ            โฃโจ unit-r-โ โปยน โฉ
              a โ โ โ โ        โ

  reduce-โโ-l : โ{a : R} -> โ โ a โผ โ
  reduce-โโ-l {a} = cancel-โ-l P
    where P : โ โ a โ โ โ a โผ โ โ a โ โ
          P = โ โ a โ โ โ a โฃโจ distr-r-โ โปยน โฉ
              (โ โ โ) โ a   โฃโจ unit-r-โ `cong-โ` refl โฉ
              โ โ a         โฃโจ unit-r-โ โปยน โฉ
              โ โ a โ โ     โ

  switch-โก-โ-l : โ{a b : R} -> โก (a โ b) โผ โก a โ b
  switch-โก-โ-l {a} {b} = unique-inverse-โ-r Pโ
    where Pโ : (a โ b) โ (โก a โ b) โผ โ
          Pโ = (a โ b) โ (โก a โ b) โฃโจ distr-r-โ โปยน โฉ
              (a โ โก a) โ b       โฃโจ inv-r-โ `cong-โ` refl โฉ
              โ โ b              โฃโจ reduce-โโ-l โฉ
              โ                  โ

  switch-โก-โ-r : โ{a b : R} -> โก (a โ b) โผ a โ โก b
  switch-โก-โ-r {a} {b} = unique-inverse-โ-r Pโ
    where Pโ : (a โ b) โ (a โ โก b) โผ โ
          Pโ = (a โ b) โ (a โ โก b)    โฃโจ distr-l-โ โปยน โฉ
              a โ (b โ โก b)         โฃโจ refl `cong-โ` inv-r-โ โฉ
              a โ โ                 โฃโจ reduce-โโ-r โฉ
              โ                     โ

{-

module _ {๐ : ๐ ^ 2} {R : ๐ฐ _} {{_ : CRing ๐ on R}} where
  binomial-2 : โ{a b : R} -> (a + b)ยฒ โผ a ยฒ + ((โจก + โจก) โ (a โ b)) + b ยฒ
  binomial-2 {a} {b} =
    (a + b) โ (a + b)                        โจ distr-l-โ โฉ-โผ
    (a + b) โ a + (a + b) โ b                โจ distr-r-โ โโโ distr-r-โ โฉ-โผ
    (a ยฒ + b โ a) + (a โ b + b ยฒ)            โจ assoc-r-โ โฉ-โผ
    (a ยฒ + b โ a) + a โ b + b ยฒ              โจ assoc-l-โ โโโ refl โฉ-โผ
    a ยฒ + (b โ a + a โ b) + b ยฒ              โจ refl โโโ (comm-โ โโโ refl) โโโ refl โฉ-โผ
    a ยฒ + (a โ b + a โ b) + b ยฒ              โจ refl โโโ (unit-l-โ โปยน โโโ unit-l-โ โปยน) โโโ refl โฉ-โผ
    a ยฒ + (โจก โ (a โ b) + โจก โ (a โ b)) + b ยฒ   โจ refl โโโ (distr-r-โ โปยน) โโโ refl โฉ-โผ
    a ยฒ + ((โจก + โจก) โ (a โ b)) + b ยฒ          โ


--------------------------------------------------------------------------------
-- Ideals


-- record isIdeal {A} {{_ : Ring ๐ on A}} (P : ๐ซ A :& isSubsetoid :& isSubmonoid :& isSubgroup :& isSubabelian {A = โฒ A โฒ}) : ๐ฐ ๐ where
record isIdeal {๐ : ๐ ^ 2} {A : Ring ๐} (P : ๐ซ โจ A โฉ :& isSubsetoid :& isSubmonoid :& isSubgroup :& isSubabelian {A = โฒ โจ A โฉ โฒ}) : ๐ฐ ๐ where
  field ideal-l-โ : โ{a b} -> โจ โจ P โฉ b โฉ -> โจ โจ P โฉ (a โ b) โฉ
        ideal-r-โ : โ{a b} -> โจ โจ P โฉ a โฉ -> โจ โจ P โฉ (a โ b) โฉ
open isIdeal {{...}} public

Ideal : (R : Ring ๐) -> ๐ฐ _
Ideal R = Subabelian โฒ โจ R โฉ โฒ :& isIdeal {A = R}

module _ {๐ : ๐ ^ 2} {R : Ring ๐} where
  RelIdeal : Ideal R -> โจ R โฉ -> โจ R โฉ -> ๐ฐ _
  RelIdeal I = RelSubgroup โฒ โจ I โฉ โฒ



record isPrime {๐ : ๐ ^ 2} {R : Ring ๐} (I : Ideal R) : ๐ฐ ๐ where
  field prime : โ{a b} -> โจ โจ I โฉ (a โ b) โฉ -> โจ โจ I โฉ a โฉ +-๐ฐ โจ โจ I โฉ b โฉ


-}


