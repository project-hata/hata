
module Verification.Core.Algebra.MonoidWithZero.Special where

open import Verification.Conventions

open import Verification.Core.Set.Decidable
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition


record hasSpecial (M : ๐๐จ๐งโ ๐) : ๐ฐ (๐ โบ) where
  field Special : Submonoid โฒ โจ M โฉ โฒ

open hasSpecial {{...}} public




