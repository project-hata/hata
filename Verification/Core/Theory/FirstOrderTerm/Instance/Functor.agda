
module Verification.Core.Theory.FirstOrderTerm.Instance.Functor where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete
open import Verification.Core.Setoid.Definition

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.FirstOrderTerm.Signature
open import Verification.Core.Theory.FirstOrderTerm
open import Verification.Core.Theory.FirstOrderTerm.Substitution

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

module _ {𝓅 : FOSignature 𝑖} where
  mutual
    map-FOTerms : ∀{αs} -> {a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> (a ⟶ b) -> FOTerms 𝓅 αs ⟨ a ⟩ ⟶ FOTerms 𝓅 αs ⟨ b ⟩
    map-FOTerms f ◌-⧜ = ◌-⧜
    map-FOTerms f (x ⋆-⧜ y) = map-FOTerms f x ⋆-⧜ map-FOTerms f y
    map-FOTerms f (incl x) = incl (map-FOTerm f _ x)

    map-FOTerm : {a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> (a ⟶ b) -> term-FO 𝓅 a ⟶ term-FO 𝓅 b
    map-FOTerm f τ (var x) = var (⟨ f ⟩ τ x)
    map-FOTerm f τ (con c ts) = con c (map-FOTerms f ts)

  -- [Hide]
  -- | The |map-FOTerm| function is a setoid hom.
  private
    mutual
      lem-1s : ∀{αs} -> ∀{a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> {f g : a ⟶ b} -> f ∼ g -> map-FOTerms {αs} f ≡ map-FOTerms {αs} g
      lem-1s p i ◌-⧜ = ◌-⧜
      lem-1s p i (incl x) = incl (lem-1 p _ i x)
      lem-1s p i (x ⋆-⧜ y) = (lem-1s p i x) ⋆-⧜ (lem-1s p i y)

      lem-1 : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> {f g : a ⟶ b} -> f ∼ g -> map-FOTerm f ∼ map-FOTerm g
      lem-1 p τ i (var x) = var ((⟨ p ⟩ τ i) x)
      lem-1 p τ i (con c ts) = con c (lem-1s p i ts)

  instance
    isSetoidHom:map-FOTerm : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> isSetoidHom (a ⟶ b) (term-FO 𝓅 a ⟶ term-FO 𝓅 b) map-FOTerm
    isSetoidHom:map-FOTerm = record { cong-∼ = lem-1 }
  -- //

  -- [Hide]
  -- | The |map-FOTerm| respects the categorical structures.
  private

    -- | It respects the identity.
    mutual
      lem-2s : ∀{αs} -> ∀{a : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> map-FOTerms {αs} {a = a} id ≡ id-𝒰
      lem-2s i ◌-⧜ = ◌-⧜
      lem-2s i (incl x) = incl (lem-2 _ i x)
      lem-2s i (x ⋆-⧜ y) = lem-2s i x ⋆-⧜ lem-2s i y

      lem-2 : ∀{a : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> map-FOTerm {a = a} id ∼ id
      lem-2 τ i (var x) = var x
      lem-2 τ i (con x ts) = con x (lem-2s i ts)

    -- | It respects composition.
    module _ {a b c : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} {f : a ⟶ b} {g : b ⟶ c} where
      mutual
        lem-3s : ∀{αs} -> map-FOTerms {αs} (f ◆ g) ≡ map-FOTerms f ◆ map-FOTerms g
        lem-3s i ◌-⧜ = ◌-⧜
        lem-3s i (incl x) = incl (lem-3 _ i x)
        lem-3s i (x ⋆-⧜ y) = lem-3s i x ⋆-⧜ lem-3s i y

        lem-3 : map-FOTerm (f ◆ g) ∼ map-FOTerm f ◆ map-FOTerm g
        lem-3 τ i (var x) = var (⟨ g ⟩ τ (⟨ f ⟩ τ x))
        lem-3 τ i (con x ts) = con x (lem-3s i ts)
  -- //

  -- [Lemma]
  -- | The function |term-FO| is a functor.
  instance
    isFunctor:FOTerm : isFunctor (𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)) (𝐈𝐱 (Sort 𝓅) (𝐔𝐧𝐢𝐯 𝑖)) (term-FO 𝓅)
    isFunctor.map isFunctor:FOTerm = map-FOTerm
    isFunctor.isSetoidHom:map isFunctor:FOTerm = isSetoidHom:map-FOTerm
    isFunctor.functoriality-id isFunctor:FOTerm = lem-2
    isFunctor.functoriality-◆ isFunctor:FOTerm = lem-3

  -- //


