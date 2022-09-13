
module Impure.Base.HIO.Translate.TC where

open import Impure.Conventions
open import Impure.Base.HIO.Definition
open import Verification.Conventions.Meta.Term

open import Impure.Base.TCMEXEC.Definition






runTC : ∀{A} -> HIO A -> TC A
runTC (return-HIO x) = {!!}
runTC (echoLn x) = {!!}
runTC (writeFile x x₁) = {!!}
runTC (editFile x x₁ x₂ x₃) = {!!}



