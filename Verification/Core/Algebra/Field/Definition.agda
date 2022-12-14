
module Verification.Core.Algebra.Field.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition


๐ญ = โจก

module _ {A : ๐ฐ _} {{_ : Monoid ๐ on A}} where
  record not-โ (a : A) : ๐ฐ ๐ where
    constructor incl
    field โจ_โฉ : a โ โ

  open not-โ public

record isField (R : Ring ๐) : ๐ฐ ๐ where
  field โ : (a : โจ R โฉ) -> {{not-โ a}} -> โจ R โฉ
  field inv-l-โ : โ{a : โจ R โฉ} -> {{_ : not-โ a}} -> โ a โ a โผ ๐ญ
  field inv-r-โ : โ{a} -> {{_ : not-โ a}} -> a โ โ a โผ ๐ญ
  field nontrivial-Field : โ โ ๐ญ

open isField {{...}} public

Field : โ ๐ -> ๐ฐ _
Field ๐ = Ring ๐ :& isField






