
module Verification.Core.Theory.FirstOrderTerm.Element where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.FirstOrderTerm.Signature
open import Verification.Core.Theory.FirstOrderTerm
open import Verification.Core.Theory.FirstOrderTerm.Substitution.Definition



-- [Definition]
-- | Let [..] be a parametrization.
module _ (𝓅 : FOSignature 𝑖) where
-- |> Similar to occurences of variables in lists, we define
--    the type of occurences of variables in multisorted terms.
  mutual
    data VarPath-FOTerms : ∀{Γ Δ : ⋆List (Sort 𝓅)} -> (t : FOTerms 𝓅 Δ Γ) -> {s : Sort 𝓅} -> (Γ ∍ s) -> 𝒰 𝑖 where
      left-Path : ∀{Γ Δ Δ'} -> {t : FOTerms 𝓅 Δ Γ} -> {t' : FOTerms 𝓅 Δ' Γ} -> {s : Sort 𝓅} -> {v : Γ ∍ s}
                  -> (p : VarPath-FOTerms t v) -> VarPath-FOTerms (t ⋆-⧜ t') v

      right-Path : ∀{Γ Δ Δ'} -> {t : FOTerms 𝓅 Δ Γ} -> {t' : FOTerms 𝓅 Δ' Γ} -> {s : Sort 𝓅} -> {v : Γ ∍ s}
                  -> (p : VarPath-FOTerms t v) -> VarPath-FOTerms (t' ⋆-⧜ t) v

      incl : ∀{Γ τ} -> {t : FOTerm 𝓅 Γ τ} -> {s : Sort 𝓅} -> {v : Γ ∍ s}
                  -> (p : VarPath-Term-𝕋× t v) -> VarPath-FOTerms (incl t) v

    data VarPath-Term-𝕋× : ∀{Γ τ} -> (t : FOTerm 𝓅 Γ τ) -> {s : Sort 𝓅} -> (Γ ∍ s) -> 𝒰 𝑖 where
      var : ∀{Γ s} -> (x : Γ ∍ s) -> VarPath-Term-𝕋× (var x) x
      con : ∀{Γ αs α s} {x : Γ ∍ s} -> (c : Con 𝓅 αs α) -> {ts : FOTerms 𝓅 (ι αs) Γ }
            -> VarPath-FOTerms ts x
            -> VarPath-Term-𝕋× (con c ts) x
-- //





