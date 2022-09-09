
module Verification.Impure.Program.HataCmd.Edittime where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term
open import Verification.Impure.Program.HataCmd.Common

call-ET-writeGeneratedHaskellFile : Text -> Text -> TC Text
call-ET-writeGeneratedHaskellFile mod content =
  call-hatacmd ("ET:writeGeneratedHaskellFile" ∷ "--module" ∷ mod ∷ "--content" ∷ content ∷ [])



