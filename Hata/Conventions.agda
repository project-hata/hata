
module Hata.Conventions where

open import Verification.Conventions
  hiding (Path)
  renaming (_×-𝒰_ to _×_ ; ⊥-𝒰 to ⊥ ; ⊤-𝒰 to ⊤)
  public
open import Hata.Builtin public
open import Agda.Builtin.Char public

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum


intercalate : Text -> List Text -> Text
intercalate i ⦋⦌ = ""
intercalate i (x ∷ ⦋⦌) = x
intercalate i (x ∷ y ∷ ys) = x <> i <> intercalate i (y ∷ ys)

indent : List Text -> List Text
indent = map-List ("  " <>_)

hList : (Text × Text) -> List Text -> List Text
hList (a , b) [] = (a <> b) ∷ []
hList (a , b) (x ∷ xs) = ((a <> " " <> x) ∷ map-List (", " <>_) xs) <> (b ∷ [])


replace : Char -> Char -> List Char -> List Char
replace a b [] = []
replace a b (x ∷ xs) = (if x ≟ a then b else x) ∷ replace a b xs

replaceT : Char -> Char -> Text -> Text
replaceT a b xs = primStringFromList (replace a b (primStringToList xs))


convertNameToHaskell : Text -> Text
convertNameToHaskell xs = replaceT '-' '_' xs

data Error : 𝒰₀ where
  error : Text -> Error


