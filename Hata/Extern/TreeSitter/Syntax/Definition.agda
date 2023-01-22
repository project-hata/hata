
module Hata.Extern.TreeSitter.Syntax.Definition where

open import Hata.Conventions
open import Hata.Reflection.Signature.Record
open import Hata.Reflection.Signature.Datatype
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum


module _ (N : 𝒰₀) where
  data Token : 𝒰₀ where
    lit : Text -> Token
    next : N -> Token
    seq : List Token -> Token
    choice : List Token -> Token

  data Rule : 𝒰₀ where
    _↦_ : N -> Token -> Rule

  infix 300 _↦_

record Grammar : 𝒰₁ where
  field Nonterminal : 𝒰₀
  field toplevel : Nonterminal
  field rules : List (Rule Nonterminal)
  field {{IShow:Nonterminal}} : IShow Nonterminal

open Grammar public



