
module Verification.Core.Category.Std.Category.Opposite.Instance.FiniteCoproductCategory where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite.Definition

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product

module _ {๐ : Category ๐} {{_ : hasProducts ๐}} where

  instance
    hasCoproducts:แตแต-๐๐๐ญ : hasCoproducts (๐ แตแตโฏ)
    hasCoproducts:แตแต-๐๐๐ญ = {!!}

  instance
    hasFiniteCoproducts:แตแต-๐๐๐ญ : hasFiniteCoproducts (๐ แตแตโฏ)
    hasFiniteCoproducts:แตแต-๐๐๐ญ = {!!}





