
module Verification.Core.Theory.FirstOrderTerm.Instance.Show where

open import Verification.Conventions

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Theory.FirstOrderTerm
open import Verification.Core.Theory.FirstOrderTerm.Signature
open import Verification.Core.Theory.FirstOrderTerm.Substitution.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

module _ {a : FOSignature 𝑖} {{_ : ∀{xs} {x} -> IShow (Con a xs x)}} where
  private
    mutual
      lem-1s : ∀{Γ Δ} -> (FOTerms a Γ Δ) -> Text
      lem-1s ◌-⧜ = "◌"
      lem-1s (incl x) = lem-1 x
      lem-1s (ts ⋆-⧜ ts₁) = lem-1s ts <> ", " <> lem-1s ts₁

      lem-1 : ∀{Γ : ⋆List (Sort a)} {τ : Sort a} -> (FOTerm a Γ τ) -> Text
      lem-1 (var x) = "var"
      lem-1 (con c x) = show c <> "(" <> lem-1s x <> ")"

  instance
    Show:FOTerm : ∀{Γ : ⋆List (Sort a)} {τ : Sort a} -> IShow (FOTerm a Γ τ)
    Show:FOTerm = record { show = lem-1 }
