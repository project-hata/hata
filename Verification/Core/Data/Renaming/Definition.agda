
module Verification.Core.Data.Renaming.Definition where

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
open import Verification.Core.Data.List.Variant.Binary.Element.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct
open import Verification.Core.Category.Std.Morphism.EpiMono

open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.NormalFiniteIndexed.Definition


module _ (A : ๐ฐ ๐) where
  โฎRenaming : ๐ฐ _
  โฎRenaming = ๐๐ฎ๐โโโโ (โฎ๐๐ข๐ง๐๐ฑ A)

  macro
    โฎ๐๐๐ง = #structureOn โฎRenaming

  Renaming : ๐ฐ _
  Renaming = ๐๐ฎ๐โโโโ (๐๐ข๐ง๐๐ฑ A)

  macro
    ๐๐๐ง = #structureOn Renaming





