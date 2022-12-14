
module Verification.Core.Space.Affine.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
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



module _ {R : Ring ๐} (M : Module R ๐) where
  private
    M' : Abelian _
    M' = โณ M

    M'' : Monoid _
    M'' = โณ (โณ M)

  Affine : โ ๐ -> ๐ฐ _
  Affine ๐ = Torsor M'' ๐

module _ (R : Ring ๐) where

  module _ ๐ ๐ where
    record ๐๐๐แต : ๐ฐ (๐ ๏ฝค ๐ โบ ๏ฝค ๐ โบ) where
      constructor _,_
      field fst : Module R ๐
      field snd : Affine fst ๐

    macro ๐๐๐ = #structureOn ๐๐๐แต

  ฮนแต-๐๐๐ : ๐๐๐แต ๐ ๐ -> ๐๐จ๐ซ๐ฌ _ _
  ฮนแต-๐๐๐ (M , A) = โณ (โณ M) , A

  instance
    isCategory:๐๐๐ : isCategory (๐๐๐ ๐ ๐)
    isCategory:๐๐๐ = isCategory:FullSubcategory (ฮนแต-๐๐๐)





