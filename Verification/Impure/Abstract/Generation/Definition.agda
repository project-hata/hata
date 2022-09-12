
module Verification.Impure.Abstract.Generation.Definition where

open import Verification.Conventions.Meta.Term
open import Verification.Impure.SpecialConventions

record isGeneratable (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field generate : A -> Text

open isGeneratable {{...}} public

Parser : 𝒰 𝑖 -> 𝒰 𝑖
Parser A = Term -> Error +-𝒰 A

pName : Text -> Parser 𝟙-𝒰
pName t (var x args) = {!!}
pName t (con c args) = {!!}
pName t (def f args) = {!!}
pName t (lam v t₁) = {!!}
pName t (pat-lam cs args) = {!!}
pName t (pi a b) = {!!}
pName t (agda-sort s) = {!!}
pName t (lit l) = {!!}
pName t (meta x x₁) = {!!}
pName t unknown = {!!}

