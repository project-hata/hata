
module Verification.Core.Theory.FirstOrderTerm.Signature.Datatype where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum


module _ {A : 𝒰₀} (sorts : List A) where
  NamedFOCtor : 𝒰₀
  NamedFOCtor = (String ×-𝒰 List (Maybe (♮Element sorts)))

record DatatypeFOSignature : 𝒰₀ where
  field sort : String
  field externalSorts : List String
  field ctors : List (NamedFOCtor externalSorts)

open DatatypeFOSignature public




