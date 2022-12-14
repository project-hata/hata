
module Verification.Core.Theory.FirstOrderTerm.Instance.Functor where

open import Verification.Conventions hiding (_â_)

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

module _ {ð : FOSignature ð} where
  mutual
    map-FOTerms : â{Îąs} -> {a b : ððĒð§ððą (Sort ð)} -> (a âķ b) -> FOTerms ð Îąs âĻ a âĐ âķ FOTerms ð Îąs âĻ b âĐ
    map-FOTerms f â-â§ = â-â§
    map-FOTerms f (x â-â§ y) = map-FOTerms f x â-â§ map-FOTerms f y
    map-FOTerms f (incl x) = incl (map-FOTerm f _ x)

    map-FOTerm : {a b : ððĒð§ððą (Sort ð)} -> (a âķ b) -> term-FO ð a âķ term-FO ð b
    map-FOTerm f Ï (var x) = var (âĻ f âĐ Ï x)
    map-FOTerm f Ï (con c ts) = con c (map-FOTerms f ts)

  -- [Hide]
  -- | The |map-FOTerm| function is a setoid hom.
  private
    mutual
      lem-1s : â{Îąs} -> â{a b : ððĒð§ððą (Sort ð)} -> {f g : a âķ b} -> f âž g -> map-FOTerms {Îąs} f âĄ map-FOTerms {Îąs} g
      lem-1s p i â-â§ = â-â§
      lem-1s p i (incl x) = incl (lem-1 p _ i x)
      lem-1s p i (x â-â§ y) = (lem-1s p i x) â-â§ (lem-1s p i y)

      lem-1 : â{a b : ððĒð§ððą (Sort ð)} -> {f g : a âķ b} -> f âž g -> map-FOTerm f âž map-FOTerm g
      lem-1 p Ï i (var x) = var ((âĻ p âĐ Ï i) x)
      lem-1 p Ï i (con c ts) = con c (lem-1s p i ts)

  instance
    isSetoidHom:map-FOTerm : â{a b : ððĒð§ððą (Sort ð)} -> isSetoidHom (a âķ b) (term-FO ð a âķ term-FO ð b) map-FOTerm
    isSetoidHom:map-FOTerm = record { cong-âž = lem-1 }
  -- //

  -- [Hide]
  -- | The |map-FOTerm| respects the categorical structures.
  private

    -- | It respects the identity.
    mutual
      lem-2s : â{Îąs} -> â{a : ððĒð§ððą (Sort ð)} -> map-FOTerms {Îąs} {a = a} id âĄ id-ð°
      lem-2s i â-â§ = â-â§
      lem-2s i (incl x) = incl (lem-2 _ i x)
      lem-2s i (x â-â§ y) = lem-2s i x â-â§ lem-2s i y

      lem-2 : â{a : ððĒð§ððą (Sort ð)} -> map-FOTerm {a = a} id âž id
      lem-2 Ï i (var x) = var x
      lem-2 Ï i (con x ts) = con x (lem-2s i ts)

    -- | It respects composition.
    module _ {a b c : ððĒð§ððą (Sort ð)} {f : a âķ b} {g : b âķ c} where
      mutual
        lem-3s : â{Îąs} -> map-FOTerms {Îąs} (f â g) âĄ map-FOTerms f â map-FOTerms g
        lem-3s i â-â§ = â-â§
        lem-3s i (incl x) = incl (lem-3 _ i x)
        lem-3s i (x â-â§ y) = lem-3s i x â-â§ lem-3s i y

        lem-3 : map-FOTerm (f â g) âž map-FOTerm f â map-FOTerm g
        lem-3 Ï i (var x) = var (âĻ g âĐ Ï (âĻ f âĐ Ï x))
        lem-3 Ï i (con x ts) = con x (lem-3s i ts)
  -- //

  -- [Lemma]
  -- | The function |term-FO| is a functor.
  instance
    isFunctor:FOTerm : isFunctor (ððĒð§ððą (Sort ð)) (ððą (Sort ð) (ðð§ðĒðŊ ð)) (term-FO ð)
    isFunctor.map isFunctor:FOTerm = map-FOTerm
    isFunctor.isSetoidHom:map isFunctor:FOTerm = isSetoidHom:map-FOTerm
    isFunctor.functoriality-id isFunctor:FOTerm = lem-2
    isFunctor.functoriality-â isFunctor:FOTerm = lem-3

  -- //


