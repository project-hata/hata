
module Hata.Base.HIO.Translate.TC where

open import Hata.Conventions
open import Hata.Base.HIO.Definition
open import Verification.Conventions.Meta.Term

open import Hata.Base.TCMEXEC.Definition






runTC : ∀{A} -> HIO A -> TC A
runTC (return-HIO x) = {!!}
runTC (echoLn x) = {!!}
runTC (writeFile x x₁) = {!!}
runTC (editFile x x₁ x₂ x₃) = {!!}



