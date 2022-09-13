
module Impure.Extern.Haskell.Generate where

-- open import Verification.Conventions
open import Impure.SpecialConventions
open import Verification.Core.Theory.FirstOrderTerm.Signature.Record
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum



generateRecord : RecordFOSignature -> List Text
generateRecord Σ =
  "data " <> convertNameToHaskell (sort Σ) <> " = " <> sort Σ
  ∷ indent (hList ("{" , "}") (map-List genField (fields Σ)))
  where
    genField = λ (name , type) → convertNameToHaskell name <> " :: " <> convertNameToHaskell type

generateRecordWithDecorations : RecordFOSignature -> List Text
generateRecordWithDecorations Σ =
  let n = convertNameToHaskell (sort Σ)
  in generateRecord Σ <>
    (
    "  deriving (Show, Generic)"
    ∷ ("instance ToJSON " <> n)
    ∷ ("instance FromJSON " <> n)
    ∷ ""
    ∷ "toJSON_" <> n <> " :: " <> n <> " -> Text"
    ∷ "toJSON_" <> n <> " = toStrict . f . decodeUtf8' . encode"
    ∷ "  where f (Left e) = \"error\""
    ∷ "        f (Right r) = r"
    ∷ []
    )

generateRecordFile : RecordFOSignature -> Text
generateRecordFile Σ = intercalate "\n" $
  ("module HataGeneratedModules.Types." <> modulePath Σ <> " where")
  ∷ ""
  ∷ "import GHC.Generics"
  ∷ "import Data.Aeson"
  ∷ "import Data.Text as T"
  ∷ "import Data.Text.Lazy.Encoding"
  ∷ "import Data.Text.Lazy (toStrict)"
  ∷ ""
  ∷ generateRecordWithDecorations Σ


---------------------------------------------------------------------

generateHaskellBindings : RecordFOSignature -> Text
generateHaskellBindings Σ =
  intercalate "\n" (genTypeBinding ∷ genFunBinding)
  where
    name' = sort Σ
    -- genField = λ (name , type) -> convertNameToHaskell name
    genTypeBinding =
      "{-# COMPILE GHC " <> sort Σ <> " = data " <> convertNameToHaskell (sort Σ)
      <> " ("
      <> convertNameToHaskell (sort Σ)
      -- <> intercalate " | " (map-List genField (fields Σ))
      <> ") #-}"

    genFunBinding =
      "postulate"
      ∷ ("  toJSON-" <> name' <> " : " <> name' <> " -> Text")
      ∷ ("{-# COMPILE GHC " <> "toJSON-" <> name' <> " = " <> "toJSON_" <> convertNameToHaskell name' <> " #-}")
      ∷ []





