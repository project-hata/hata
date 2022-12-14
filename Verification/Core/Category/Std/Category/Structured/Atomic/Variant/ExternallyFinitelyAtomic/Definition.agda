
module Verification.Core.Category.Std.Category.Structured.Atomic.Variant.ExternallyFinitelyAtomic.Definition where

open import Verification.Conventions hiding (_โ_)
open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Verification.Core.Category.Std.Limit.Cone.Colimit.Preservation
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Functor.Representable2

--
-- Definition from https://nlab-pages.s3.us-east-2.amazonaws.com/nlab/show/atom
--
-- but changed, currently only asks for finite coproducts to be preserved.
--

module _ {๐ : Category ๐} {๐ : Category ๐} where
  record isFiniteCoproductPreserving (F : Functor ๐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
    field preserve-isCoproduct : โ{a b x : โจ ๐ โฉ} -> isCoproduct a b x -> isCoproduct (โจ F โฉ a) (โจ F โฉ b) (โจ F โฉ x)

  open isFiniteCoproductPreserving public

module _ {C : ๐ฐ ๐} {{_ : isCategory {๐โ} C}} (๐ : ๐ ^ 3) where
  isAtom : (e : C) -> ๐ฐ _
  isAtom e = isFiniteCoproductPreserving (โ๐๐แตแต e)
  -- preservesAllColimits (โ๐๐แตแต e) ๐



