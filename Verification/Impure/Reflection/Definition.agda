
module Verification.Impure.Reflection.Definition where

open import Verification.Conventions
open import Verification.Impure.Builtin
open import Verification.Conventions.Meta.Term

-- reflection targets
open import Verification.Core.Theory.FirstOrderTerm.Signature.Record



macro
  #generate-haskell : Name -> Term → TC 𝟙-𝒰
  #generate-haskell t s = do
    Σ <- reflectIntoRecordSignature t

    unify s (lit (string ""))




