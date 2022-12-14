
module Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.As.Monoid where

open import Verification.Conventions hiding (_โ_)
open import Verification.Core.Setoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct



module _ {๐ : ๐ฐ _} {{_ : ๐ is FiniteCoproductCategory ๐}} where

  private instance
    _ : isSetoid ๐
    _ = isSetoid:byCategory


  private
    ๐แตแต : Category _
    ๐แตแต = โฒ ๐ โฒ แตแต
    instance
      _ : isMonoid (๐ since isSetoid:byCategory {{of ๐แตแต}})
      _ = isMonoid:byHasFiniteProducts

  isMonoid:byHasFiniteCoproducts : isMonoid โฒ ๐ โฒ
  isMonoid:byHasFiniteCoproducts = isMonoid:byแตแต


module _ {๐ : ๐ฐ _} {{P : ๐ is FiniteCoproductCategory ๐}} where
  private instance
    _ : isSetoid ๐
    _ = isSetoid:byCategory

    _ : isMonoid โฒ ๐ โฒ
    _ = isMonoid:byHasFiniteCoproducts {{P}}

  unit-l-โ : โ{a : ๐} -> โฅ โ a โผ a
  unit-l-โ = unit-l-โ

  unit-r-โ : โ{a : ๐} -> a โ โฅ โผ a
  unit-r-โ = unit-r-โ

  assoc-l-โ : โ{a b c : ๐} -> (a โ b) โ c โผ a โ (b โ c)
  assoc-l-โ = assoc-l-โ





