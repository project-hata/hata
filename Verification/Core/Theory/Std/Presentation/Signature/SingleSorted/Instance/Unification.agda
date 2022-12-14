
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

Obj = _:&_.â¨_â©


module _ {A : ð° ð} {B : ð° ð} where
  const : B -> A -> B
  const b _ = b

  module _ {{_ : isSetoid ð A}} {{_ : isSetoid ð B}} where
    instance
      isSetoidHom:const : â {b} -> isSetoidHom â²(A)â² â²(B)â² (const b)
      isSetoidHom:const = {!!}

module _ {Ï : Signature} where
  private
    Î¹ : â -> Kleisli â² TermF (ââ , ââ) Ï â²
    Î¹ n = incl â²(Fin n)â²

  ð¢ubs : Category (ââ , _ , _)
  ð¢ubs = â² FullSubcategory Î¹ â²

  private
    module _ {b : Obj ð¢ubs} (f : incl 1 â¶ b) (i : Fin â¨ b â©) where
      private
        -- g' : Fin â¨ a â© -> Term Ï (Fin â¨ b â©)
        -- g' = const (var i)
        a : Obj ð¢ubs
        a = incl 1

        g : a â¶ b
        g = incl (incl (incl (â² const (var i) â²)))

        -- postulate
        --   Pâ : 

        lem-10 : isDecidable (hasCoequalizer f g)
        lem-10 = {!!}


  -- instance
  --   hasUnification:ð¢ubs : hasUnification ð¢ubs
  --   hasUnification.unify hasUnification:ð¢ubs f g =
  --     let G : Submonoid â² PathMon (ð¢ubs) â²
  --         G = _
  --         -- PZ : PrincipalFamilyCat â²(ð¢ubs)â²
  --         PZ = record
  --                { SizeC = {!!}
  --                ; isBase = {!!}
  --                ; sizeC = {!!}
  --                ; size0 = {!!}
  --                ; initial-size0 = {!!}
  --                }
  --         PY = by-PrincipalCat-Principal (ð¢ubs) {{_}} {{_}} {{PZ}}
  --         PX = isPrincipal:Family â² PathMon ð¢ubs â² G _ _ {{PY}} _ (just (_ , _ , f , g)) refl
  --     in by-Principal-Unification.proof f g {G = G} PX



