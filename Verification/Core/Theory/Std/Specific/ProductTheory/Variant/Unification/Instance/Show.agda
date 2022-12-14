
module Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.Show where

open import Verification.Conventions

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition


module _ {a : πΓ π} {{_ : β{xs} {x} -> IShow (Con a xs x)}} where
  private
    mutual
      lem-1s : β{Ξ Ξ} -> (Terms-πΓ a Ξ Ξ) -> Text
      lem-1s β-β§ = "β"
      lem-1s (incl x) = lem-1 x
      lem-1s (ts β-β§ tsβ) = lem-1s ts <> ", " <> lem-1s tsβ

      lem-1 : β{Ξ : βList (Type-πΓ a)} {Ο : Type-πΓ a} -> (Termβ-πΓ a Ξ Ο) -> Text
      lem-1 (var x) = "var"
      lem-1 (con c x) = show c <> "(" <> lem-1s x <> ")"

  instance
    Show:FOTerm : β{Ξ : βList (Type-πΓ a)} {Ο : Type-πΓ a} -> IShow (Termβ-πΓ a Ξ Ο)
    Show:FOTerm = record { show = lem-1 }


