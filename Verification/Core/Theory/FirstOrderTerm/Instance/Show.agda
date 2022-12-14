
module Verification.Core.Theory.FirstOrderTerm.Instance.Show where

open import Verification.Conventions

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Theory.FirstOrderTerm
open import Verification.Core.Theory.FirstOrderTerm.Signature
open import Verification.Core.Theory.FirstOrderTerm.Substitution.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

module _ {a : FOSignature π} {{_ : β{xs} {x} -> IShow (Con a xs x)}} where
  private
    mutual
      lem-1s : β{Ξ Ξ} -> (FOTerms a Ξ Ξ) -> Text
      lem-1s β-β§ = "β"
      lem-1s (incl x) = lem-1 x
      lem-1s (ts β-β§ tsβ) = lem-1s ts <> ", " <> lem-1s tsβ

      lem-1 : β{Ξ : βList (Sort a)} {Ο : Sort a} -> (FOTerm a Ξ Ο) -> Text
      lem-1 (var x) = "var"
      lem-1 (con c x) = show c <> "(" <> lem-1s x <> ")"

  instance
    Show:FOTerm : β{Ξ : βList (Sort a)} {Ο : Sort a} -> IShow (FOTerm a Ξ Ο)
    Show:FOTerm = record { show = lem-1 }
