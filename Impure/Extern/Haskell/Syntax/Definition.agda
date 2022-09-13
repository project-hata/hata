
module Impure.Extern.Haskell.Syntax.Definition where

open import Impure.Conventions
open import Impure.Abstract.Generation.Definition


data HsBuiltin : 𝒰₀ where
  HsText HsFilepath : HsBuiltin

pHsBuiltin : Parser HsBuiltin
pHsBuiltin = {!!}

data HsType : 𝒰₀ where
  HsArr : HsType -> HsType -> HsType
  HsList : HsType -> HsType

instance
  isGeneratable:HsType : isGeneratable HsType
  isGeneratable:HsType = record { generate = f }
    where
      f : HsType -> Text
      f (HsArr x y) = "(" <> f x <> " -> " <> f y <> ")"
      f (HsList x) = "[" <> f x <> "]"



