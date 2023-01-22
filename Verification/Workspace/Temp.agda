
module Verification.Workspace.Temp where

open import Verification.Conventions hiding (Bool)

data Bool 𝑗 : 𝒰 𝑗 where
  true : Bool 𝑗
  false : Bool 𝑗

negate : Bool 𝑗 -> Bool 𝑗
negate true = false
negate false = true

a = negate (negate (negate (true)))

theorem1 : a ≣ false
theorem1 = refl-StrId

theorem2 : (a : Bool 𝑗) -> negate (negate a) ≣ a
theorem2 true = refl-StrId
theorem2 false = refl-StrId







