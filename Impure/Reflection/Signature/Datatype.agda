
module Impure.Reflection.Signature.Datatype where

open import Impure.Conventions
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum


-- module _ {A : 𝒰₀} (sorts : List A) where
--   NamedFOCtor : 𝒰₀
--   NamedFOCtor = (Text × List (Maybe (♮Element sorts)))

record DatatypeFOSignature : 𝒰₀ where
  field sort : Text
  field modulePath : Text
  -- field externalSorts : List Text
  field ctors : List (Text × List Text) -- name, types of args

open DatatypeFOSignature public





