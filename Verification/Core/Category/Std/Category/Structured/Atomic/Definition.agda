
module Verification.Core.Category.Std.Category.Structured.Atomic.Definition where

open import Verification.Conventions hiding (_โ_)
open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Verification.Core.Category.Std.Limit.Cone.Colimit.Preservation
open import Verification.Core.Category.Std.Functor.Representable2

--
-- Definition from https://nlab-pages.s3.us-east-2.amazonaws.com/nlab/show/atom
--

module _ {C : ๐ฐ ๐} {{_ : isCategory {๐โ} C}} (๐ : ๐ ^ 3) where
  isAtom : (e : C) -> ๐ฐ _
  isAtom e = preservesAllColimits (โ๐๐แตแต e) ๐






