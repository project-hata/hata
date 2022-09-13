
module Impure.Program.HataCmd.HataSystemInterface where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term
open import Impure.Program.HataCmd.Common


call-hsi-getNameFromFQ : Name -> TC Text
call-hsi-getNameFromFQ n = call-hatacmd ("hsi:getNameFromFQ" ∷ "--name" ∷ primShowQName n ∷ [])

call-hsi-getModuleFromFQ : Name -> TC Text
call-hsi-getModuleFromFQ n = call-hatacmd ("hsi:getModuleFromFQ" ∷ "--name" ∷ primShowQName n ∷ [])


