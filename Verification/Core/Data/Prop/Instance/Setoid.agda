
module Verification.Core.Data.Prop.Instance.Setoid where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Universe.Definition

record _∼-Setoid_ (A B : Prop 𝑖) : 𝒰 𝑖 where
  constructor _,_
  field ⟨_⟩ : ⟨ A ⟩ -> ⟨ B ⟩
        inv-∼-Setoid : Prop.⟨_⟩ B -> Prop.⟨_⟩ A
open _∼-Setoid_ public
-- _∼-Setoid_ A B = (⟨ A ⟩ -> ⟨ B ⟩) ×-𝒰 (⟨ B ⟩ -> ⟨ A ⟩)

-- instance
--   isEquivRel:∼-Setoid : isEquivRel (∼-Base (_∼-Setoid_ {𝑖}))
--   is
  -- isEquivRel.refl isEquivRel:∼-Setoid = incl (id-𝒰 , id-𝒰)
  -- isEquivRel.sym isEquivRel:∼-Setoid (incl (p , q)) = incl (q , p)
  -- isEquivRel._∙_ isEquivRel:∼-Setoid (incl (p , q)) (incl (v , w)) = incl (p ◆-𝒰 v , w ◆-𝒰 q)

instance
  isSetoid:Prop : isSetoid (Prop 𝑖)
  isSetoid:Prop = isSetoid:byDef _∼-Setoid_
    (id-𝒰 , id-𝒰)
    (λ (p , q) -> (q , p))
    (λ (p , q) (v , w) -> (p ◆-𝒰 v , w ◆-𝒰 q))
  -- isSetoid._∼'_ isSetoid:Prop = _∼-Setoid_

  -- isSetoid.isEquivRel:∼ isSetoid:Prop = {!!}
  -- isSetoid._∼'_ isSetoid:Prop A B = (⟨ A ⟩ -> ⟨ B ⟩) ×-𝒰 (⟨ B ⟩ -> ⟨ A ⟩)
  -- isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:Prop) = incl (id-𝒰 , id-𝒰)
  -- isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:Prop) (incl (p , q)) = incl (q , p)
  -- isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:Prop) (incl (p , q)) (incl (v , w)) = incl (p ◆-𝒰 v , w ◆-𝒰 q)



