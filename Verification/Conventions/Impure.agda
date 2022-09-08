
module Verification.Conventions.Impure where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta

postulate
  FilePath : 𝒰₀

{-# COMPILE GHC FilePath as FilePath #-}


-----------------------------------------
-- reflection related

postulate
  FQName : 𝒰₀
  stringToFQName : String -> FQName

{-# COMPILE GHC FQName as Text #-}


getFQName : Name -> FQName
get
