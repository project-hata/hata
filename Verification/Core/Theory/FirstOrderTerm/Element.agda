
module Verification.Core.Theory.FirstOrderTerm.Element where

open import Verification.Conventions hiding (_β_)

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
module _ (π : FOSignature π) where
-- |> Similar to occurences of variables in lists, we define
--    the type of occurences of variables in multisorted terms.
  mutual
    data VarPath-FOTerms : β{Ξ Ξ : βList (Sort π)} -> (t : FOTerms π Ξ Ξ) -> {s : Sort π} -> (Ξ β s) -> π° π where
      left-Path : β{Ξ Ξ Ξ'} -> {t : FOTerms π Ξ Ξ} -> {t' : FOTerms π Ξ' Ξ} -> {s : Sort π} -> {v : Ξ β s}
                  -> (p : VarPath-FOTerms t v) -> VarPath-FOTerms (t β-β§ t') v

      right-Path : β{Ξ Ξ Ξ'} -> {t : FOTerms π Ξ Ξ} -> {t' : FOTerms π Ξ' Ξ} -> {s : Sort π} -> {v : Ξ β s}
                  -> (p : VarPath-FOTerms t v) -> VarPath-FOTerms (t' β-β§ t) v

      incl : β{Ξ Ο} -> {t : FOTerm π Ξ Ο} -> {s : Sort π} -> {v : Ξ β s}
                  -> (p : VarPath-Term-πΓ t v) -> VarPath-FOTerms (incl t) v

    data VarPath-Term-πΓ : β{Ξ Ο} -> (t : FOTerm π Ξ Ο) -> {s : Sort π} -> (Ξ β s) -> π° π where
      var : β{Ξ s} -> (x : Ξ β s) -> VarPath-Term-πΓ (var x) x
      con : β{Ξ Ξ±s Ξ± s} {x : Ξ β s} -> (c : Con π Ξ±s Ξ±) -> {ts : FOTerms π (ΞΉ Ξ±s) Ξ }
            -> VarPath-FOTerms ts x
            -> VarPath-Term-πΓ (con c ts) x
-- //





