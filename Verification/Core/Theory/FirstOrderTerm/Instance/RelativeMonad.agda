
module Verification.Core.Theory.FirstOrderTerm.Instance.RelativeMonad where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete
open import Verification.Core.Setoid.Definition

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition

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
open import Verification.Core.Theory.FirstOrderTerm.Instance.Functor

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

module _ {𝓅 : FOSignature 𝑖} where
  repure-term-FO : ∀{a} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ term-FO 𝓅 a
  repure-term-FO i x = var x

  mutual
    reext-FOTerms : ∀{a b αs} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ term-FO 𝓅 b -> FOTerms 𝓅 αs ⟨ a ⟩ ⟶ FOTerms 𝓅 αs ⟨ b ⟩
    reext-FOTerms f ◌-⧜ = ◌-⧜
    reext-FOTerms f (x ⋆-⧜ y) = reext-FOTerms f x ⋆-⧜ reext-FOTerms f y
    reext-FOTerms f (incl x) = incl (reext-term-FO f _ x)

    reext-term-FO : ∀{a b} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ term-FO 𝓅 b -> term-FO 𝓅 a ⟶ term-FO 𝓅 b
    reext-term-FO f i (var x) = f i x
    reext-term-FO f i (con c x) = con c (reext-FOTerms f x)

  instance
    isRelativeMonad:term-FO : isRelativeMonad (𝑓𝑖𝑛 (Sort 𝓅)) (term-FO 𝓅)
    isRelativeMonad.repure isRelativeMonad:term-FO = repure-term-FO
    isRelativeMonad.reext isRelativeMonad:term-FO = reext-term-FO
    isRelativeMonad.reunit-l isRelativeMonad:term-FO = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:term-FO = {!!}
    isRelativeMonad.reassoc isRelativeMonad:term-FO = {!!}


module _ {Σ : FOSignature 𝑖} where
  simpleVar : ∀{Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (term-FO Σ )} {τ : Sort Σ} -> (⟨ Γ ⟩ ∍ τ) -> incl (incl τ) ⟶ Γ
  simpleVar v = ⧜subst (incl (repure _ v))


--------------------------------------
-- named definitions for the category
module _ (𝓅 : FOSignature 𝑖) where
  open import Verification.Core.Data.Substitution.Variant.Base.Definition
  open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

  macro 𝐒𝐮𝐛𝐬𝐭-Sim = #structureOn (InductiveSubstitution (term-FO 𝓅))

  module Overwrite:isCategory:𝐒𝐮𝐛𝐬𝐭-Sim where
    open isCategory (isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = term-FO 𝓅}) public

  module Overwrite:hasCoproducts:𝐒𝐮𝐛𝐬𝐭-Sim where
    open hasCoproducts (hasCoproducts:⧜𝐒𝐮𝐛𝐬𝐭 {T = term-FO 𝓅}) public

  module Overwrite:isCoproduct:𝐒𝐮𝐛𝐬𝐭-Sim {a b : 𝐒𝐮𝐛𝐬𝐭-Sim} where
    open isCoproduct (isCoproduct:⊔-⧜𝐒𝐮𝐛𝐬𝐭 {T = term-FO 𝓅} {a = a} {b = b}) public

  module Overwrite:hasInitial:𝐒𝐮𝐛𝐬𝐭-Sim where
    open hasInitial (hasInitial:⧜𝐒𝐮𝐛𝐬𝐭 {T = term-FO 𝓅}) public

  module Overwrite:isInitial:𝐒𝐮𝐛𝐬𝐭-Sim where
    open isInitial (isInitial:⊥-⧜𝐒𝐮𝐛𝐬𝐭 {T = term-FO 𝓅}) public

  module Overwrite:hasFiniteCoproducts:𝐒𝐮𝐛𝐬𝐭-Sim where
    open hasFiniteCoproducts (hasFiniteCoproducts:⧜𝐒𝐮𝐛𝐬𝐭 {T = term-FO 𝓅}) public

module _ {Σ : FOSignature 𝑖} where
  module §-reext-Terms-𝕋× where
    prop-1 : ∀{a b x} -> (α β : 𝑓𝑖𝑛 (Sort Σ) (incl a) ⟶  term-FO Σ b) -> (t : FOTerm Σ a x) -> reext α _ t ≡ reext β _ t -> ∀ i s -> α i s ≡ β i s
    prop-1 α β (var x) p i s = {!!}
    prop-1 α β (con c x) p i s = {!!}

    prop-2 : ∀{x y : ⧜𝐒𝐮𝐛𝐬𝐭 (term-FO Σ)} {αsx : ⋆List (Sort Σ)} -> (h : y ⟶ x)
             -> (tsx : CtxHom (FOTerm Σ) (αsx) ⟨ y ⟩)
             -> (reext-FOTerms (sub-⧜𝐒𝐮𝐛𝐬𝐭 h) tsx)
               ≣
               (tsx ◆-⧜𝐒𝐮𝐛𝐬𝐭' h)
    prop-2 {x} {y} h ◌-⧜ = refl-≣
    prop-2 {x} {y} h (incl x₁) = refl-≣
    prop-2 {x} {y} h (tsx ⋆-⧜ tsy) = cong₂-Str _⋆-⧜_ (prop-2 h tsx) (prop-2 h tsy)




