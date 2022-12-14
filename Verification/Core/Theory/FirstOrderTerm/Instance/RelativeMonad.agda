
module Verification.Core.Theory.FirstOrderTerm.Instance.RelativeMonad where

open import Verification.Conventions hiding (_â_)

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

module _ {ð : FOSignature ð} where
  repure-term-FO : â{a} -> ððð (Sort ð) a âķ term-FO ð a
  repure-term-FO i x = var x

  mutual
    reext-FOTerms : â{a b Îąs} -> ððð (Sort ð) a âķ term-FO ð b -> FOTerms ð Îąs âĻ a âĐ âķ FOTerms ð Îąs âĻ b âĐ
    reext-FOTerms f â-â§ = â-â§
    reext-FOTerms f (x â-â§ y) = reext-FOTerms f x â-â§ reext-FOTerms f y
    reext-FOTerms f (incl x) = incl (reext-term-FO f _ x)

    reext-term-FO : â{a b} -> ððð (Sort ð) a âķ term-FO ð b -> term-FO ð a âķ term-FO ð b
    reext-term-FO f i (var x) = f i x
    reext-term-FO f i (con c x) = con c (reext-FOTerms f x)

  instance
    isRelativeMonad:term-FO : isRelativeMonad (ððð (Sort ð)) (term-FO ð)
    isRelativeMonad.repure isRelativeMonad:term-FO = repure-term-FO
    isRelativeMonad.reext isRelativeMonad:term-FO = reext-term-FO
    isRelativeMonad.reunit-l isRelativeMonad:term-FO = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:term-FO = {!!}
    isRelativeMonad.reassoc isRelativeMonad:term-FO = {!!}


module _ {ÎĢ : FOSignature ð} where
  simpleVar : â{Î : â§ððŪððŽð­ (term-FO ÎĢ )} {Ï : Sort ÎĢ} -> (âĻ Î âĐ â Ï) -> incl (incl Ï) âķ Î
  simpleVar v = â§subst (incl (repure _ v))


--------------------------------------
-- named definitions for the category
module _ (ð : FOSignature ð) where
  open import Verification.Core.Data.Substitution.Variant.Base.Definition
  open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

  macro ððŪððŽð­-Sim = #structureOn (InductiveSubstitution (term-FO ð))

  module Overwrite:isCategory:ððŪððŽð­-Sim where
    open isCategory (isCategory:â§ððŪððŽð­ {T = term-FO ð}) public

  module Overwrite:hasCoproducts:ððŪððŽð­-Sim where
    open hasCoproducts (hasCoproducts:â§ððŪððŽð­ {T = term-FO ð}) public

  module Overwrite:isCoproduct:ððŪððŽð­-Sim {a b : ððŪððŽð­-Sim} where
    open isCoproduct (isCoproduct:â-â§ððŪððŽð­ {T = term-FO ð} {a = a} {b = b}) public

  module Overwrite:hasInitial:ððŪððŽð­-Sim where
    open hasInitial (hasInitial:â§ððŪððŽð­ {T = term-FO ð}) public

  module Overwrite:isInitial:ððŪððŽð­-Sim where
    open isInitial (isInitial:âĨ-â§ððŪððŽð­ {T = term-FO ð}) public

  module Overwrite:hasFiniteCoproducts:ððŪððŽð­-Sim where
    open hasFiniteCoproducts (hasFiniteCoproducts:â§ððŪððŽð­ {T = term-FO ð}) public

module _ {ÎĢ : FOSignature ð} where
  module Â§-reext-Terms-ðÃ where
    prop-1 : â{a b x} -> (Îą Îē : ððð (Sort ÎĢ) (incl a) âķ  term-FO ÎĢ b) -> (t : FOTerm ÎĢ a x) -> reext Îą _ t âĄ reext Îē _ t -> â i s -> Îą i s âĄ Îē i s
    prop-1 Îą Îē (var x) p i s = {!!}
    prop-1 Îą Îē (con c x) p i s = {!!}

    prop-2 : â{x y : â§ððŪððŽð­ (term-FO ÎĢ)} {Îąsx : âList (Sort ÎĢ)} -> (h : y âķ x)
             -> (tsx : CtxHom (FOTerm ÎĢ) (Îąsx) âĻ y âĐ)
             -> (reext-FOTerms (sub-â§ððŪððŽð­ h) tsx)
               âĢ
               (tsx â-â§ððŪððŽð­' h)
    prop-2 {x} {y} h â-â§ = refl-âĢ
    prop-2 {x} {y} h (incl xâ) = refl-âĢ
    prop-2 {x} {y} h (tsx â-â§ tsy) = congâ-Str _â-â§_ (prop-2 h tsx) (prop-2 h tsy)




