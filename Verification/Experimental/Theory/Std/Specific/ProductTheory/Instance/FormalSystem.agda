
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FormalSystem where

open import Verification.Conventions

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
-- open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition



module _ {𝑨 : 𝕋× 𝑖} where
  mutual
    map-Terms-𝕋× : ∀{αs} -> {a b : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)} -> (a ⟶ b) -> Terms-𝕋× 𝑨 αs a ⟶ Terms-𝕋× 𝑨 αs b
    map-Terms-𝕋× f ◌-⧜ = ◌-⧜
    map-Terms-𝕋× f (x ⋆-⧜ y) = map-Terms-𝕋× f x ⋆-⧜ map-Terms-𝕋× f y
    map-Terms-𝕋× f (incl x) = incl (map-Term-𝕋× f _ x)

    map-Term-𝕋× : {a b : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)} -> (a ⟶ b) -> Term-𝕋× 𝑨 a ⟶ Term-𝕋× 𝑨 b
    map-Term-𝕋× f τ (var x) = var (⟨ f ⟩ τ x)
    map-Term-𝕋× f τ (con c x) = con c (map-Terms-𝕋× f x)

  instance
    isFunctor:Term-𝕋× : isFunctor (𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) (𝐈𝐱 (Type-𝕋× 𝑨) (𝐔𝐧𝐢𝐯 𝑖)) (Term-𝕋× 𝑨)
    isFunctor.map isFunctor:Term-𝕋× = map-Term-𝕋×
    isFunctor.isSetoidHom:map isFunctor:Term-𝕋× = {!!}
    isFunctor.functoriality-id isFunctor:Term-𝕋× = {!!}
    isFunctor.functoriality-◆ isFunctor:Term-𝕋× = {!!}

  repure-Term-𝕋× : ∀{a} -> 𝑓𝑖𝑛 (Type-𝕋× 𝑨) a ⟶ Term-𝕋× 𝑨 a
  repure-Term-𝕋× i x = var x

  mutual
    reext-Terms-𝕋× : ∀{a b αs} -> 𝑓𝑖𝑛 (Type-𝕋× 𝑨) a ⟶ Term-𝕋× 𝑨 b -> Terms-𝕋× 𝑨 αs a ⟶ Terms-𝕋× 𝑨 αs b
    reext-Terms-𝕋× f ◌-⧜ = ◌-⧜
    reext-Terms-𝕋× f (x ⋆-⧜ y) = reext-Terms-𝕋× f x ⋆-⧜ reext-Terms-𝕋× f y
    reext-Terms-𝕋× f (incl x) = incl (reext-Term-𝕋× f _ x)

    reext-Term-𝕋× : ∀{a b} -> 𝑓𝑖𝑛 (Type-𝕋× 𝑨) a ⟶ Term-𝕋× 𝑨 b -> Term-𝕋× 𝑨 a ⟶ Term-𝕋× 𝑨 b
    reext-Term-𝕋× f i (var x) = f i x
    reext-Term-𝕋× f i (con c x) = con c (reext-Terms-𝕋× f x)

  instance
    isRelativeMonad:Term-𝕋× : isRelativeMonad (𝑓𝑖𝑛 (Type-𝕋× 𝑨)) ′(Term-𝕋× 𝑨)′
    isRelativeMonad.repure isRelativeMonad:Term-𝕋× = repure-Term-𝕋×
    isRelativeMonad.reext isRelativeMonad:Term-𝕋× = reext-Term-𝕋×
    isRelativeMonad.reunit-l isRelativeMonad:Term-𝕋× = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:Term-𝕋× = {!!}
    isRelativeMonad.reassoc isRelativeMonad:Term-𝕋× = {!!}


instance
  isFormalSystem:ProductTheory : isFormalSystem (𝕋× 𝑖)
  isFormalSystem.Type isFormalSystem:ProductTheory = Type-𝕋×
  isFormalSystem.Termsᵘ isFormalSystem:ProductTheory = Term-𝕋×
  isFormalSystem.isFunctor:Terms isFormalSystem:ProductTheory = isFunctor:Term-𝕋×
  isFormalSystem.isRelativeMonad:Terms isFormalSystem:ProductTheory = isRelativeMonad:Term-𝕋×


module _ {𝑨 : 𝕋× 𝑖} where
  retro-Terms-𝕋× : ∀{a b : 𝐂𝐭𝐱 𝑨} -> (a ⟶ b) ≅ (Terms-𝕋× 𝑨 (incl (⟨ a ⟩)) (incl (⟨ b ⟩)))
  retro-Terms-𝕋× {a} {b} = f since P
    where
      f : ∀{a b : 𝐂𝐭𝐱 𝑨} -> (a ⟶ b) -> (Terms-𝕋× 𝑨 (incl (⟨ a ⟩)) (incl (⟨ b ⟩)))
      f ◌-⧜ = ◌-⧜
      f (incl x) = incl x
      f (t ⋆-⧜ s) = f t ⋆-⧜ f s

      P = {!!}
