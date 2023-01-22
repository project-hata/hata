
module Hata.Base.TCMEXEC.Definition where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term
open import Hata.Program.HataCmd.Common public

-- postulate
--   execTC : (exe : Text) (args : List Text) (stdIn : Text)
--          → TC (Σ ℕ (λ _ → Σ Text (λ _ → Text)))

-- {-# BUILTIN AGDATCMEXEC execTC #-}



