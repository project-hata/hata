

module Verification.Core.Set.Finite.Old.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.HeytingAlgebra
open import Verification.Core.Set.Finite.Old.Reach


record isFinite (A : π° π :& isDiscrete') : π° (π βΊ) where
  field reach : β (p q : π«-Dec β¨ A β©) -> (s : β¨ p β© β€ β¨ q β©) -> Reachable β¨ p β© β¨ q β© s
open isFinite {{...}} public

Finite : (π : π) -> π° _
Finite π = π° π :& isDiscrete' :& isFinite

module _ {A B : π° _} {{_ : Finite π on A}} {{_ : Finite π on B}} where
  instance
    isFinite:+ : isFinite (β² A β¨ B β²)
    isFinite.reach isFinite:+ P Q a =
      let Pβ = reach (P β£ left) (Q β£ left) (monotone a)

          Pβ' : Reachable (β¨ P β© β§ Im left) (β¨ Q β© β§ Im left) _
          Pβ' = pb-Reach left β¨ P β© β¨ Q β© Pβ

          Pβ = reach (P β£ right) (Q β£ right) (monotone a)

          Pβ' : Reachable (β¨ P β© β§ Im right) (β¨ Q β© β§ Im right) _
          Pβ' = pb-Reach right β¨ P β© β¨ Q β© Pβ

      in {!!}

-- size : Finite π -> β
-- size A = f β¨ A β© (β₯ , {!!}) {!!} {!!} (reach _ _ _)
--   where f : β(A : π° π) (P Q : π«-Dec A) -> (R : β¨ P β© β€ β¨ Q β©) -> Reachable R -> β
--         f A P (.(β¨ P β©) , Proofβ) (incl .(isPreorder.reflexive isPreorder:Prop)) refl-Reach = 0
--         f A P Q R (step-Reach .R x Y r) = suc (f _ _ _ _ r)


