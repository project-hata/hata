
module Verification.Core.Category.Std.Category.As.Monoid.Special where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Special
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Category.As.Monoid.Definition

module _ {π : π° _} {{_ : SizedCategory π on π}} where


  Special-PathMon : Submonoid (π―πΊπππ¬ππ β² π β²)
  Special-PathMon = β² S β²
    where
      S : π―πΊπππ¬ππ β² π β² -> Prop _
      S [] = β€
      S idp = β€
      S (arrow {a} {b} f) = β£ Lift (sizeO b βͺ sizeO a) β£

      instance
        isSubsetoid:S : isSubsetoid S
        isSubsetoid:S = {!!}

      instance
        isSubmonoid:S : isSubmonoid β² S β²
        isSubmonoid:S = {!!}


  instance
    hasSpecial:PathMon : hasSpecial (π―πΊπππ¬ππ β² π β²)
    hasSpecial:PathMon = record { Special = Special-PathMon }






