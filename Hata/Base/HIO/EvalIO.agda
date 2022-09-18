
module Hata.Base.HIO.EvalIO where

open import Hata.Conventions
open import Hata.Base.HIO.Definition

open import Hata.IO.Definition

evalIO : ∀{A} -> HIO A -> IO A
evalIO (HIO.putStrLn x) = Hata.IO.Definition.putStrLn x



