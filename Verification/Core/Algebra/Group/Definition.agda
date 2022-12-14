
module Verification.Core.Algebra.Group.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition


record isGroup {๐ : ๐ ^ 2} (A : Monoid ๐) : ๐ฐ ๐ where
  field โก_ : โจ A โฉ -> โจ A โฉ
        inv-l-โ : โ{a} -> โก a โ a โผ โ
        inv-r-โ : โ{a} -> a โ โก a โผ โ
        cong-โก_ : โ{aโ aโ} -> aโ โผ aโ -> โก aโ โผ โก aโ
  โกโ_ = cong-โก_
  infix 100 โก_ โกโ_
open isGroup {{...}} public

Group : (๐ : ๐ ^ 2) -> ๐ฐ _
Group ๐ = Monoid ๐ :& isGroup


record isSubgroup {๐ : ๐ ^ 2} {A} {{_ : Group ๐ on A}} (P : ๐ซ-๐ฐ A :& isSubsetoid :& isSubmonoid) : ๐ฐ ๐ where
  field closed-โก : โ{a} -> โจ โจ P โฉ a โฉ -> โจ โจ P โฉ (โก a) โฉ
open isSubgroup {{...}} public


Subgroup : (G : Group ๐) -> ๐ฐ _
Subgroup G = ๐ซ-๐ฐ โจ G โฉ :& isSubsetoid :& isSubmonoid :& isSubgroup


data RelSubgroup {๐ : ๐ ^ 2} {G : Group ๐} (H : Subgroup G) (a : โจ G โฉ) (b : โจ G โฉ) : ๐ฐ (๐ โ 0) where
  incl : โจ โจ H โฉ (a โ โก b) โฉ -> RelSubgroup H a b






module _ {๐ ๐ : ๐} {A : ๐ฐ ๐} {{_ : Group (๐ , ๐) on A}} where
  cancel-โ-l : โ{a b c : A} -> a โ b โผ a โ c -> b โผ c
  cancel-โ-l {a} {b} {c} p =
      b             โฃโจ unit-l-โ โปยน โฉ
      โ โ b         โฃโจ inv-l-โ โปยน โโโ refl โฉ
      (โก a โ a) โ b โฃโจ assoc-l-โ โฉ
      โก a โ (a โ b) โฃโจ refl โโโ p โฉ
      โก a โ (a โ c) โฃโจ assoc-r-โ โฉ
      (โก a โ a) โ c โฃโจ inv-l-โ โโโ refl โฉ
      โ โ c         โฃโจ unit-l-โ โฉ
      c             โ

  distr-โ-โก : โ{a b : A} -> โก (a โ b) โผ โก b โ โก a
  distr-โ-โก {a} {b} = cancel-โ-l $
    (a โ b) โ โก (a โ b)   โฃโจ inv-r-โ โฉ
    โ                     โฃโจ inv-r-โ โปยน โฉ
    a โ โก a               โฃโจ unit-r-โ โปยน โโโ refl โฉ
    (a โ โ) โ โก a         โฃโจ (refl โโโ inv-r-โ โปยน) โโโ refl โฉ
    (a โ (b โ โก b)) โ โก a โฃโจ assoc-r-โ โโโ refl โฉ
    ((a โ b) โ โก b) โ โก a โฃโจ assoc-l-โ โฉ
    (a โ b) โ (โก b โ โก a) โ

  double-โก : โ{a : A} -> โก โก a โผ a
  double-โก {a} = cancel-โ-l $
    โก a โ โก โก a โฃโจ inv-r-โ โฉ
    โ           โฃโจ inv-l-โ โปยน โฉ
    โก a โ a     โ

  unique-inverse-โ-r : โ{a b : A} -> a โ b โผ โ -> โก a โผ b
  unique-inverse-โ-r {a} {b} p =
    let Pโ : a โ b โผ a โ โก a
        Pโ = a โ b   โฃโจ p โฉ
             โ       โฃโจ inv-r-โ โปยน โฉ
             a โ โก a โ
    in sym (cancel-โ-l Pโ)

  reduce-โกโ : โก โ โผ โ
  reduce-โกโ = โก โ     โฃโจ unit-r-โ โปยน โฉ
              โก โ โ โ โฃโจ inv-l-โ โฉ
              โ       โ




