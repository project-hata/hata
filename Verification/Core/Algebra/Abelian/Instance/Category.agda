
module Verification.Core.Algebra.Abelian.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Category.Std.Category.Definition

module _ 𝑖 where
  macro
    𝐀𝐛 = #structureOn (Abelian 𝑖)

module _ (A : Abelian 𝑖) (B : Abelian 𝑗) where
  AbelianHom = MonoidHom (↳ A) (↳ B)
  -- isAbelianHom (f : MonoidHom (↳ A) (↳ B)) -> 𝒰 _ -- (𝑖 ､ 𝑗)
  -- isAbelianHom f = isMonoidHom f 

  -- record isAbelianHom (f : MonoidHom (↳ A) (↳ B)) : 𝒰 (𝑖 ､ 𝑗) where


-- instance
--   isCategory:𝐀𝐛 : isCategory (𝐀𝐛 𝑖)
--   isCategory:𝐀𝐛 = {!!}

