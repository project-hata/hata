
module Verification.Impure.Extern.Haskell.Generate where

open import Verification.Conventions
open import Verification.Core.Theory.FirstOrderTerm.Signature.Named
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum


intercalate : String -> List String -> String
intercalate i ⦋⦌ = ""
intercalate i (x ∷ ⦋⦌) = x
intercalate i (x ∷ y ∷ ys) = x <> i <> intercalate i (y ∷ ys)


module _ (Σ : NamedFOSignature) where
  private
    genCtor : String -> (NamedFOCtor (externalSorts Σ)) -> String
    genCtor sort (name , inputs) = name <> " :: " <> intercalate " -> " (map-List f inputs) <> " -> " <> sort
      where
        f : Maybe (♮Element (externalSorts Σ)) -> String
        f nothing = sort
        f (just (el , _)) = el

  generateDataType : List String
  generateDataType = {!!}




