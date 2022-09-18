
{-# OPTIONS --type-in-type #-}

module Hata.Base.HIO.Definition where

open import Hata.Conventions


data HIO : 𝒰₀ -> 𝒰₀ where
  return-HIO : ∀{A} -> A -> HIO A
  echoLn : Text -> HIO ⊤-𝒰
  writeFile : FilePath -> Text -> HIO ⊤-𝒰
  editFile : FilePath -> Text -> Text -> Text -> HIO ⊤-𝒰



