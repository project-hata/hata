
module Verification.Application.CompGen.Meta.Macro where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term

postulate
  execTC : (exe : String) (args : List String) (stdIn : String)
         → TC (Σ ℕ (λ _ → Σ String (λ _ → String)))

{-# BUILTIN AGDATCMEXEC execTC #-}

macro
  echo : String → Term → TC 𝟙-𝒰
  echo mytext hole = do
    (exitCode , (stdOut , stdErr)) ← execTC "hata-cmd" ("echo" ∷ "--text" ∷ mytext ∷ []) ""
    unify hole (lit (string mytext))

-- _ : echo ("hello") ≡ "hello world\n"
-- _ = refl-≡




bla = echo "hello! this or"



