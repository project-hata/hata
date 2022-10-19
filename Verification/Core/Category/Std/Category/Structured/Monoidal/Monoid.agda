
-- {-# OPTIONS --syntactic-equality=1 --experimental-lossy-unification #-}


module Verification.Core.Category.Std.Category.Structured.Monoidal.Monoid where


open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
-- open import Verification.Core.Category.Std.Category.Construction.Product
-- open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
-- open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
-- open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
-- open import Verification.Core.Category.Std.Category.Instance.2Category
-- open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Functor.Constant
-- open import Verification.Core.Category.Std.Functor.Instance.Category
-- open import Verification.Core.Category.Std.Natural.Definition
-- open import Verification.Core.Category.Std.Natural.Iso
-- open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Product.Properties.Monoidal
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition4


open isMonoidal {{...}} public





module _ (𝒞 : Monoidal 𝑖) where

  record Mon : 𝒰 (𝑖 ､ 𝑗) where
    field El : ⟨ 𝒞 ⟩
    field mult : El ⊗ El ⟶ El
    field unit : ident ⟶ El
    field unit-l-mult : bλ El ◆ (unit ⇃⊗⇂ id) ◆ mult ∼ id
    field unit-r-mult : bρ El ◆ (id ⇃⊗⇂ unit) ◆ mult ∼ id
    field assoc-mult : (mult ⇃⊗⇂ id) ◆ mult ∼ fα El El El ◆ (id ⇃⊗⇂ mult) ◆ mult

    -- field unit-l-mult2 : bλ El ◆ (unit ⇃⊗⇂ id) ◆ mult ∼ id
    -- field unit-r-mult2 : bρ El ◆ (id ⇃⊗⇂ unit) ◆ mult ∼ id
    -- field assoc-mult2 : (mult ⇃⊗⇂ id) ◆ mult ∼ fα El El El ◆ (id ⇃⊗⇂ mult) ◆ mult
    -- field unit-l-mult3 : bλ El ◆ (unit ⇃⊗⇂ id) ◆ mult ∼ id
    -- field unit-r-mult3 : bρ El ◆ (id ⇃⊗⇂ unit) ◆ mult ∼ id
    -- field assoc-mult3 : (mult ⇃⊗⇂ id) ◆ mult ∼ fα El El El ◆ (id ⇃⊗⇂ mult) ◆ mult
{-
    -}
    -- field unit-l-mult2 : bλ El ◆ (unit ⇃⊗⇂ id) ◆ mult ∼ id
    -- field unit-r-mult2 : bρ El ◆ (id ⇃⊗⇂ unit) ◆ mult ∼ id
    -- field assoc-mult2 : (mult ⇃⊗⇂ id) ◆ mult ∼ fα El El El ◆ (id ⇃⊗⇂ mult) ◆ mult
    -- field unit-l-mult3 : bλ El ◆ (unit ⇃⊗⇂ id) ◆ mult ∼ id
    -- field unit-r-mult3 : bρ El ◆ (id ⇃⊗⇂ unit) ◆ mult ∼ id
    -- field assoc-mult3 : (mult ⇃⊗⇂ id) ◆ mult ∼ fα El El El ◆ (id ⇃⊗⇂ mult) ◆ mult


