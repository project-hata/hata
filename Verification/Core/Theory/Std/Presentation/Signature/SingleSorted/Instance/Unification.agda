
module Verification.Core.Theory.Presentation.Signature.SingleSorted.Instance.Unification where

open import Verification.Conventions

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Setoid
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Set.Decidable
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.As.Monoid
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Core.Theory.Computation.Unification.Definition
-- open import Verification.Core.Theory.Computation.Unification.Monoidic.ToCoequalizer
-- open import Verification.Core.Theory.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Core.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Core.Theory.Presentation.Signature.SingleSorted.Definition
open import Verification.Core.Theory.Presentation.Signature.SingleSorted.Instance.Setoid
open import Verification.Core.Theory.Presentation.Signature.SingleSorted.Instance.Functor
open import Verification.Core.Theory.Presentation.Signature.SingleSorted.Instance.Monad

Obj = _:&_.⟨_⟩


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  const : B -> A -> B
  const b _ = b

  module _ {{_ : isSetoid 𝑘 A}} {{_ : isSetoid 𝑙 B}} where
    instance
      isSetoidHom:const : ∀ {b} -> isSetoidHom ′(A)′ ′(B)′ (const b)
      isSetoidHom:const = {!!}

module _ {σ : Signature} where
  private
    ι : ℕ -> Kleisli ′ TermF (ℓ₀ , ℓ₀) σ ′
    ι n = incl ′(Fin n)′

  𝓢ubs : Category (ℓ₀ , _ , _)
  𝓢ubs = ′ FullSubcategory ι ′

  private
    module _ {b : Obj 𝓢ubs} (f : incl 1 ⟶ b) (i : Fin ⟨ b ⟩) where
      private
        -- g' : Fin ⟨ a ⟩ -> Term σ (Fin ⟨ b ⟩)
        -- g' = const (var i)
        a : Obj 𝓢ubs
        a = incl 1

        g : a ⟶ b
        g = incl (incl (incl (′ const (var i) ′)))

        -- postulate
        --   P₀ : 

        lem-10 : isDecidable (hasCoequalizer f g)
        lem-10 = {!!}


  -- instance
  --   hasUnification:𝓢ubs : hasUnification 𝓢ubs
  --   hasUnification.unify hasUnification:𝓢ubs f g =
  --     let G : Submonoid ′ PathMon (𝓢ubs) ′
  --         G = _
  --         -- PZ : PrincipalFamilyCat ′(𝓢ubs)′
  --         PZ = record
  --                { SizeC = {!!}
  --                ; isBase = {!!}
  --                ; sizeC = {!!}
  --                ; size0 = {!!}
  --                ; initial-size0 = {!!}
  --                }
  --         PY = by-PrincipalCat-Principal (𝓢ubs) {{_}} {{_}} {{PZ}}
  --         PX = isPrincipal:Family ′ PathMon 𝓢ubs ′ G _ _ {{PY}} _ (just (_ , _ , f , g)) refl
  --     in by-Principal-Unification.proof f g {G = G} PX



