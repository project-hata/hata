
module Hata.Extern.TreeSitter.Generate where

open import Hata.Conventions
open import Hata.Reflection.Signature.Record
open import Hata.Reflection.Signature.Datatype
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.ElementSum
open import Hata.Extern.TreeSitter.Syntax.Definition

module _ {N : 𝒰₀} {{_ : IShow N}} where

  mutual
    generateTokenList : List (Token N) -> Text
    generateTokenList xs = let singles = map-List generateToken xs
                               singles = intercalate ",\n" singles
                            in singles

    {-# TERMINATING #-}
    generateToken : Token N -> Text
    generateToken (lit x) = ("'" <> x <> "'")
    generateToken (next x) = "$." <> show x
    generateToken (seq x) = let singles = generateTokenList x
                            in "seq(\n" <> singles <> "\n)"
    generateToken (choice x) = let singles = generateTokenList x
                               in "choice(\n" <> singles <> "\n)"


  generateRule : Rule N -> Text
  generateRule (name ↦ pat) = show name <> ": $ => " <> generateToken pat <> ",\n"

  generateRules : List (Rule N) -> Text
  generateRules rules = intercalate "\n" (map-List generateRule rules)

generateGrammar : Grammar -> Text
generateGrammar G =
  ("source_file: $ => " <> "$." <> show (toplevel G) <> ",\n")
  <>
  generateRules (rules G)


generate : (name : Text) -> (G : Grammar) -> Text
generate name G =
  "module.exports = grammar({\n\
  \  name: '" <> name <> "', \n\
  \\n\
  \  rules: {\n"
  <> generateGrammar G <>
  "  }\n\
  \});\n"



