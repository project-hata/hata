
module Verification.Core.Category.Std.Category.Opposite.Instance.Monoid where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite.Definition
open import Verification.Core.Category.Std.Morphism.Iso


module _ {๐ : Category ๐} where
  private instance
    _ : isSetoid โจ ๐ โฉ
    _ = isSetoid:byCategory

    _ : isSetoid (๐ แตแตโฏ)
    _ = isSetoid:byCategory

  module _ {{_ : isMonoid โฒ โจ ๐ โฉ โฒ}} where

    instance
      isMonoid:แตแต : isMonoid (๐ แตแตโฏ)
      isMonoid:แตแต = record
                      { _โ_ = ฮป a b -> incl (โจ a โฉ โ โจ b โฉ)
                      ; โ = incl โ
                      ; unit-l-โ = {!!}
                      ; unit-r-โ = {!!}
                      ; assoc-l-โ = {!!}
                      ; _โโโ_ = {!!}
                      }



