
module Verification.Core.Data.List.Variant.Binary.Definition where


open import Verification.Core.Conventions hiding (β)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Set.Decidable
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Free
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Instance.Monoid
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Instance.Monoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Set.Contradiction


----------------------------------------------------------
-- The free encoding

-- [Definition]
-- | The type [..] is defined as a data type with the following
-- constructors:
data βList (A : π° π) : π° π where
  -- | - An inclusion [..].
  incl : A -> βList A

  -- | - Free multiplication [..].
  _β-β§_ : (a b : βList A) -> βList A

  -- | - Free unit [..].
  β-β§ : βList A
-- //

-- [Hide]

{-# DISPLAY _β-β§_ a b = a β b #-}
{-# DISPLAY β-β§ = β #-}


macro
  π₯ππΎπΎ-ππ¨π§ : (A : π° π) -> SomeStructure
  π₯ππΎπΎ-ππ¨π§ A = #structureOn (βList A)

-- //

