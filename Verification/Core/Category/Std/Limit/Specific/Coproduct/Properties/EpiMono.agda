
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.EpiMono where

open import Verification.Conventions hiding (_โ_)
open import Verification.Core.Setoid
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.Mono.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition


module _ {๐ : Category ๐} where
  module _ {a b x : โจ ๐ โฉ} {{_ : isCoproduct a b x}} where

    mono-ฮนโ : isMono ฮนโ
    mono-ฮนโ = {!!}


