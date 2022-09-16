
module Impure.Base.HIO.Translate.IO where

open import Impure.Conventions
open import Impure.Base.HIO.Definition

open import Impure.Base.IO.Definition



runIO : ∀{A} -> HIO A -> IO A
runIO (return-HIO x) = return x
runIO (echoLn x) = putStrLn x
runIO (writeFile x x₁) = {!!}
runIO (editFile x x₁ x₂ x₃) = {!!}


