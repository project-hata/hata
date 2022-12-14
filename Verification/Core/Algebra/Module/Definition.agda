
module Verification.Core.Algebra.Module.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition


record isModule {๐ ๐} (R : Ring ๐) (A : Abelian ๐) : ๐ฐ (๐ ๏ฝค ๐) where
  infixr 70 _โท_
  field
    _โท_ : โจ R โฉ -> โจ A โฉ -> โจ A โฉ
    assoc-l-โท : โ{r s a} -> r โ s โท a โผ r โท s โท a
    zero-โท : โ{a} -> โ โท a โผ โ
    distr-l-โท : โ{r s a} -> (r โ s) โท a โผ r โท a โ s โท a
    distr-r-โท : โ{r a b} -> r โท (a โ b) โผ r โท a โ r โท b

open isModule {{...}} public

Module : Ring ๐ -> โ ๐ -> ๐ฐ _
Module R ๐ = _ :& isModule {๐} R


module _ (R : Ring ๐) (A : Setoid ๐) where
  data Free-๐๐จ๐แต : ๐ฐ (๐ ๏ฝค ๐) where
    :โ : Free-๐๐จ๐แต
    _:โ_ : โจ R โฉ -> โจ A โฉ -> Free-๐๐จ๐แต
    _:โ_ : Free-๐๐จ๐แต -> Free-๐๐จ๐แต -> Free-๐๐จ๐แต

  macro Free-๐๐จ๐ = #structureOn Free-๐๐จ๐แต

module _ (R : Ring ๐) (A : Setoid ๐) where
  data _โผ-Free-๐๐จ๐_ : (m n : Free-๐๐จ๐ R A) -> ๐ฐ (๐ ๏ฝค ๐) where
    :cong : โ{r s a b} -> r โผ s -> a โผ b -> (r :โ a) โผ-Free-๐๐จ๐ (s :โ b)
    :assoc-l-:โ : โ{m n o} -> ((m :โ n) :โ o) โผ-Free-๐๐จ๐ (m :โ (n :โ o))
    :unit-l-:โ : โ{m} -> (:โ :โ m) โผ-Free-๐๐จ๐ m
    :unit-r-:โ : โ{m} -> (m :โ :โ) โผ-Free-๐๐จ๐ m
    :comm-:โ : โ{m n} -> (m :โ n) โผ-Free-๐๐จ๐ (n :โ m)
    :distr-l : โ{r s a} -> ((r โ s) :โ a) โผ-Free-๐๐จ๐ ((r :โ a) :โ (s :โ a))


  instance
    isSetoid:Free-๐๐จ๐ : isSetoid (Free-๐๐จ๐ R A)
    isSetoid:Free-๐๐จ๐ = isSetoid:byFree _โผ-Free-๐๐จ๐_


  instance
    isMonoid:Free-๐๐จ๐ : isMonoid (Free-๐๐จ๐ R A)
    isMonoid:Free-๐๐จ๐ = record
                          { _โ_ = _:โ_
                          ; โ = :โ
                          ; unit-l-โ = incl :unit-l-:โ
                          ; unit-r-โ = incl :unit-r-:โ
                          ; assoc-l-โ = incl :assoc-l-:โ
                          ; _โโโ_ = {!ฮป p q -> incl (:cong ? ?)!}
                          }

