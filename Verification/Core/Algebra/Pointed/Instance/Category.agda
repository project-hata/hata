
module Verification.Core.Algebra.Pointed.Instance.Category where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Algebra.Pointed.Definition


instance
  isCategory:Pointed : isCategory (Pointed 𝑖)
  isCategory.Hom isCategory:Pointed = PointedHom
  isCategory.isSetoid:Hom isCategory:Pointed = isSetoid:PointedHom
  isCategory.id isCategory:Pointed = {!!}
  isCategory._◆_ isCategory:Pointed = {!!}
  isCategory.unit-l-◆ isCategory:Pointed = {!!}
  isCategory.unit-r-◆ isCategory:Pointed = {!!}
  isCategory.unit-2-◆ isCategory:Pointed = {!!}
  isCategory.assoc-l-◆ isCategory:Pointed = {!!}
  isCategory.assoc-r-◆ isCategory:Pointed = {!!}
  isCategory._◈_ isCategory:Pointed = {!!}

