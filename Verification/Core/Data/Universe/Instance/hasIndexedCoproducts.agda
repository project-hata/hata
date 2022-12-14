
module Verification.Core.Data.Universe.Instance.hasIndexedCoproducts where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.Universe.Instance.Category
-- open import Verification.Core.Category.Std.Natural.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition
-- open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.Monoid
-- open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct


module _ {I : ๐ฐ ๐} {x : I -> ๐ฐ ๐} where

  instance
    isIndexedCoproduct:โ : isIndexedCoproduct x (โ x)
    isIndexedCoproduct:โ = record
      { ฮนแตข = ฮป i x โ i , x
      ; โฆ_โฆแตข = ฮป f (i , x) โ f i x
      ; reduce-ฮนแตข = ฮป f i โ refl-โก
      ; expand-ฮนแตข = ฮป f โ refl-โก
      }

instance
  hasIndexedCoproducts:๐๐ง๐ข๐ฏ : hasIndexedCoproducts (๐๐ง๐ข๐ฏ ๐)
  hasIndexedCoproducts:๐๐ง๐ข๐ฏ = record { โจแตข = โ_ }


