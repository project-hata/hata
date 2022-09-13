
{-# OPTIONS --type-in-type #-}

module Verification.Impure.Base.HIO.Definition where

open import Verification.Impure.SpecialConventions


data HIO : 𝒰₀ -> 𝒰₀ where
  putStrLn : Text -> HIO ⊤-𝒰




