
module Hata.Program.HataCmd.Edittime where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term
open import Hata.Program.HataCmd.Common

call-ET-writeGeneratedHaskellFile : Text -> Text -> TC Text
call-ET-writeGeneratedHaskellFile mod content =
  call-hatacmd ("ET:writeGeneratedHaskellFile" ∷ "--module" ∷ mod ∷ "--content" ∷ content ∷ [])

call-ET-updateAgdaDatatypeSourceFile : Text -> Text -> Text -> TC Text
call-ET-updateAgdaDatatypeSourceFile mod rspart content =
  call-hatacmd ("ET:updateAgdaDatatypeSourceFile" ∷ "--module" ∷ mod ∷ "--rspart" ∷ rspart ∷ "--content" ∷ content ∷ [])




