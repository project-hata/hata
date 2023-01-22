
{-# OPTIONS --type-in-type #-}

module Hata.Base.HIO.Definition where

open import Hata.Conventions


data HIO : 𝒰₀ -> 𝒰₀ where
  return-HIO : ∀{A} -> A -> HIO A
  echoLn : Text -> HIO ⊤
  writeFile : Text -> Text -> HIO ⊤
  editFile : Text -> Text -> Text -> Text -> HIO ⊤
  runCommand-HIO : Text -> List Text -> HIO Text
  _>>=_ : ∀{A B} -> HIO A -> (A -> HIO B) -> HIO B

_>>_ : ∀{A B} -> HIO A -> HIO B -> HIO B
_>>_ x y = x >>= (λ _ -> y)



