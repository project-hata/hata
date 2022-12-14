
module Verification.Core.Data.Renaming.Shift where

open import Verification.Core.Conventions hiding (_โ_)

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct
open import Verification.Core.Category.Std.Morphism.EpiMono

open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.NormalFiniteIndexed.Definition

open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal


module _ {A : ๐ฐ ๐} {{_ : isDiscrete A}} where

  shiftโ-โฎ๐๐๐ง : (x : List A) -> โฎ๐๐๐ง A -> โฎ๐๐๐ง A
  shiftโ-โฎ๐๐๐ง x a = incl (incl x) โ a

  module _ (x : List A) where
    macro
      ๐ โ๐๐๐กโ-โฎ๐๐๐ง = #structureOn (shiftโ-โฎ๐๐๐ง x)

  map-shiftโ-โฎ๐๐๐ง : (x : List A) {a b : โฎ๐๐๐ง A} -> a โถ b -> shiftโ-โฎ๐๐๐ง x a โถ shiftโ-โฎ๐๐๐ง x b
  map-shiftโ-โฎ๐๐๐ง x f = map-โ-โฎ๐๐๐ง (id , f)

  instance
    isFunctor:๐ โ๐๐๐กโ-โฎ๐๐๐ง : โ{x} -> isFunctor (โฎ๐๐๐ง A) (โฎ๐๐๐ง A) (๐ โ๐๐๐กโ-โฎ๐๐๐ง x)
    isFunctor:๐ โ๐๐๐กโ-โฎ๐๐๐ง = {!!}




