
module Verification.Core.Theory.FirstOrderTerm.Signature.Record where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum


module _ {A : 𝒰₀} (sorts : List A) where
  NamedFOField : 𝒰₀
  NamedFOField = (String ×-𝒰 ♮Element sorts)

record RecordFOSignature : 𝒰₀ where
  field sort : String
  field externalSorts : List String
  field fields : List (NamedFOField externalSorts)

open RecordFOSignature public


-------------
-- reflection

open import Verification.Conventions.Meta.Term

reflectIntoRecordSignature : Definition -> TC RecordFOSignature
reflectIntoRecordSignature (record-type c fs) = return $ record
  { sort = {!!}
  ; externalSorts = {!!}
  ; fields = {!!}
  }
reflectIntoRecordSignature xs = typeError (strErr "Expected a record definition." ∷ [])




