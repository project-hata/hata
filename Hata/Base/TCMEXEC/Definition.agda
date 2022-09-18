
module Hata.Base.TCMEXEC.Definition where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term

postulate
  execTC : (exe : Text) (args : List Text) (stdIn : Text)
         → TC (Σ ℕ (λ _ → Σ Text (λ _ → Text)))

{-# BUILTIN AGDATCMEXEC execTC #-}


call-program : Text -> List Text -> TC Text
call-program prog args = do
    (exitCode , (stdOut , stdErr)) ← execTC prog args ""
    if exitCode ≟ 0
      then (return stdOut)
      else (typeError (strErr "Got error: " ∷ strErr stdErr ∷ []))



