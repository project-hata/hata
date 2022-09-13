
module Verification.Impure.Base.HIO.EvalIO where

open import Verification.Impure.SpecialConventions
open import Verification.Impure.Base.HIO.Definition

open import Verification.Impure.IO.Definition

evalIO : ∀{A} -> HIO A -> IO A
evalIO (HIO.putStrLn x) = Verification.Impure.IO.Definition.putStrLn x



