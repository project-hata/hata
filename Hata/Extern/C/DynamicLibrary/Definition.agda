
module Hata.Extern.C.DynamicLibrary.Definition where

open import Verification.Conventions
open import Hata.IO.Definition
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element



record DynamicLibrary : 𝒰₀ where
  field name : String
  field functions : List String

open DynamicLibrary public


call : (dl : DynamicLibrary) -> (fn : String) -> functions dl ∍♮ fn -> IO (⊤-𝒰 {ℓ₀})
call = {!!}


