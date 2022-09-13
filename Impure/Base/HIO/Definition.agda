
{-# OPTIONS --type-in-type #-}

module Impure.Base.HIO.Definition where

open import Impure.SpecialConventions


data HIO : 𝒰₀ -> 𝒰₀ where
  putStrLn : Text -> HIO ⊤-𝒰




