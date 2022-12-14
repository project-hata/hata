
module Hata.Abstract.Generation.Definition where

open import Verification.Conventions.Meta.Term
open import Hata.Conventions

record isGeneratable (A : ğ° ğ) : ğ° ğ where
  field generate : A -> Text

open isGeneratable {{...}} public

Parser : ğ° ğ -> ğ° ğ
Parser A = Term -> Error +-ğ° A

pName : Text -> Parser ğ-ğ°
pName t (var x args) = {!!}
pName t (con c args) = {!!}
pName t (def f args) = {!!}
pName t (lam v tâ) = {!!}
pName t (pat-lam cs args) = {!!}
pName t (pi a b) = {!!}
pName t (agda-sort s) = {!!}
pName t (lit l) = {!!}
pName t (meta x xâ) = {!!}
pName t unknown = {!!}

