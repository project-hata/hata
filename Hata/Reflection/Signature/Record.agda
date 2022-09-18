
module Hata.Reflection.Signature.Record where

open import Hata.Conventions
-- open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum


module _ {A : 𝒰₀} (sorts : List A) where
  NamedFOField : 𝒰₀
  NamedFOField = (Text × ♮Element sorts)

record RecordFOSignature : 𝒰₀ where
  field modulePath : Text
  field sort : Text
  field fields : List (Text × Text) -- name , type
  -- field externalSorts : List Text
  -- field fields : List (NamedFOField externalSorts)

open RecordFOSignature public






