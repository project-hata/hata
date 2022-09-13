
module Impure.Base.HIO.EvalIO where

open import Impure.Conventions
open import Impure.Base.HIO.Definition

open import Impure.IO.Definition

evalIO : ∀{A} -> HIO A -> IO A
evalIO (HIO.putStrLn x) = Impure.IO.Definition.putStrLn x



