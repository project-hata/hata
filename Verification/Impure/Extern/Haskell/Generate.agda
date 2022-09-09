
module Verification.Impure.Extern.Haskell.Generate where

open import Verification.Conventions
open import Verification.Core.Theory.FirstOrderTerm.Signature.Record
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum

open import Agda.Builtin.Char


intercalate : Text -> List Text -> Text
intercalate i ⦋⦌ = ""
intercalate i (x ∷ ⦋⦌) = x
intercalate i (x ∷ y ∷ ys) = x <> i <> intercalate i (y ∷ ys)

indent : List Text -> List Text
indent = map-List ("  " <>_)

hList : (Text ×-𝒰 Text) -> List Text -> List Text
hList (a , b) [] = (a <> b) ∷ []
hList (a , b) (x ∷ xs) = ((a <> " " <> x) ∷ map-List (", " <>_) xs) <> (b ∷ [])


replace : Char -> Char -> List Char -> List Char
replace a b [] = []
replace a b (x ∷ xs) = (if x ≟ a then b else x) ∷ replace a b xs

replaceT : Char -> Char -> Text -> Text
replaceT a b xs = primStringFromList (replace a b (primStringToList xs))


convertNameToHaskell : Text -> Text
convertNameToHaskell xs = replaceT '-' '_' xs


generateRecord : RecordFOSignature -> List Text
generateRecord Σ =
  "data " <> sort Σ <> " = " <> sort Σ
  ∷ indent (hList ("{" , "}") (map-List genField (fields Σ)))
  where
    genField = λ (name , type) → convertNameToHaskell name <> " :: " <> convertNameToHaskell type

generateRecordWithDecorations : RecordFOSignature -> List Text
generateRecordWithDecorations Σ = generateRecord Σ <>
  (
  "  deriving (Show, Generic)"
  ∷ ("instance ToJSON " <> sort Σ)
  ∷ ("instance FromJSON " <> sort Σ)
  ∷ []
  )

generateRecordFile : RecordFOSignature -> Text
generateRecordFile Σ = intercalate "\n" $
  ("module HataGeneratedModules.Types." <> modulePath Σ <> " where")
  ∷ ""
  ∷ "import GHC.Generics"
  ∷ "import Data.Aeson"
  ∷ ""
  ∷ generateRecordWithDecorations Σ

-- module _ (Σ : DatatypeFOSignature) where
--   private
--     genCtor : Text -> (DatatypeFOCtor (externalSorts Σ)) -> Text
--     genCtor sort (name , inputs) = name <> " :: " <> intercalate " -> " (map-List f inputs) <> " -> " <> sort
--       where
--         f : Maybe (♮Element (externalSorts Σ)) -> Text
--         f nothing = sort
--         f (just (el , _)) = el

--   generateDataType : List Text
--   generateDataType = {!!}




