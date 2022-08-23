
module Verification.Core.Space.Affine.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Instance.Category
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Algebra.Module.Definition
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Torsor.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Subcategory.Full2




module _ {R : Ring 𝑖} (M : Module R 𝑗) where
  private
    M' : Abelian _
    M' = ↳ M

    M'' : Monoid _
    M'' = ↳ (↳ M)

  Affine : ∀ 𝑘 -> 𝒰 _
  Affine 𝑘 = Torsor M'' 𝑘

module _ (R : Ring 𝑖) where

  module _ 𝑗 𝑘 where
    record 𝐀𝐟𝐟ᵘ : 𝒰 (𝑖 ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
      constructor _,_
      field fst : Module R 𝑗
      field snd : Affine fst 𝑘

    macro 𝐀𝐟𝐟 = #structureOn 𝐀𝐟𝐟ᵘ

  ιᵘ-𝐀𝐟𝐟 : 𝐀𝐟𝐟ᵘ 𝑗 𝑘 -> 𝐓𝐨𝐫𝐬 _ _
  ιᵘ-𝐀𝐟𝐟 (M , A) = ↳ (↳ M) , A

  instance
    isCategory:𝐀𝐟𝐟 : isCategory (𝐀𝐟𝐟 𝑗 𝑘)
    isCategory:𝐀𝐟𝐟 = isCategory:FullSubcategory (ιᵘ-𝐀𝐟𝐟)





