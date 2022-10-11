
module Verification.Core.Space.Affine.Variant.Direct.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Instance.Category
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Algebra.Module.Definition
open import Verification.Core.Algebra.Module.Instance.Category
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Torsor.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Subcategory.Full2



record isDirectAffine {𝑗 𝑖} (R : Ring 𝑖) (M : Module R 𝑗) : 𝒰 (𝑖 ､ 𝑗 ⁺) where

module _ (R : Ring 𝑖) 𝑗 where
  DirectAffine = _ :& isDirectAffine {𝑗} R

module _ {R : Ring 𝑖} where
  module _ (A B : DirectAffine R 𝑗) where
    record isDirectAffineHom (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
      field modhom : (↳ A) ⟶ (↳ B)
      field constpart : ⟨ B ⟩
      field isaff : ∀{a : ⟨ A ⟩} -> ⟨ modhom ⟩ a ⋆ constpart ∼ f a





