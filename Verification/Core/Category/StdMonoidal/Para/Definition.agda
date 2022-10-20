
module Verification.Core.Category.StdMonoidal.Para.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition

open import Verification.Core.Category.StdMonoidal.Category.Definition



module _ (𝒞 : Monoidal 𝑖) where
  record Para : 𝒰 𝑖 where
    field El : ⟨ 𝒞 ⟩



