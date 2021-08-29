
module Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
-- open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermsCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Computation.Unification.Definition



record isFormalSystem {𝑗} {𝑖} (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
  field Type : A -> 𝒰 𝑗
  field Termsᵘ : (a : A) -> 𝐅𝐢𝐧𝐈𝐱 (Type a) -> 𝐈𝐱 (Type a) (𝐔𝐧𝐢𝐯 𝑗)
  field {{isFunctor:Terms}} : ∀{a} -> isFunctor (𝐅𝐢𝐧𝐈𝐱 (Type a)) (𝐈𝐱 (Type a) (𝐔𝐧𝐢𝐯 𝑗)) (Termsᵘ a)
  field {{isRelativeMonad:Terms}} : ∀{a : A} -> isRelativeMonad (𝑓𝑖𝑛 (Type a)) (′ Termsᵘ a ′)

  macro
    Terms : ∀(a : A) -> SomeStructure
    Terms a = #structureOn (Termsᵘ a)

open isFormalSystem {{...}} public

FormalSystem : ∀ (𝑗 : 𝔏 ^ 2) -> 𝒰 _
FormalSystem 𝑗 = 𝒰 (𝑗 ⌄ 0) :& isFormalSystem {𝑗 ⌄ 1}






module _ {𝒮 : 𝒰 𝑖} {{_ : isFormalSystem {𝑗} 𝒮}} (𝑨 : 𝒮) where
  𝐂𝐭𝐱ᵘ : 𝒰 _
  𝐂𝐭𝐱ᵘ = ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
  macro 𝐂𝐭𝐱 = #structureOn 𝐂𝐭𝐱ᵘ

-- module _ {𝒮 : FormalSystem 𝑖} {a : ⟨ 𝒮 ⟩} where
module _ {𝒮 : 𝒰 𝑖} {{_ : isFormalSystem {𝑗} 𝒮}} {𝑨 : 𝒮} where
  -- _⊢_ : 人List (Type 𝑨) -> Type 𝑨 -> 𝒰 _
  -- _⊢_ Γ τ = τ' ⟶ Γ'
  --   where
  --     Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
  --     Γ' = incl (Γ)

  --     τ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
  --     τ' = incl (incl τ)

  _⊢_ : 𝐂𝐭𝐱 𝑨 -> Type 𝑨 -> 𝒰 _
  _⊢_ Γ τ = τ' ⟶ Γ
    where
      τ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
      τ' = incl (incl τ)

  _at_ : ∀{Γ Δ : 𝐂𝐭𝐱 𝑨} -> {α : Type 𝑨} -> (Γ ⟶ Δ) -> ⟨ Γ ⟩ ∍ α -> Δ ⊢ α
  _at_ x t = {!!}


record hasFullUnification (𝒮 : FormalSystem 𝑖) : 𝒰 𝑖 where
  field {{hasUnification:this}} : ∀{𝑨 : ⟨ 𝒮 ⟩} -> hasUnification (𝐂𝐭𝐱 𝑨)



record hasVariablesᴬ {𝑖} (𝒮 : FormalSystem 𝑖) (𝑨 : ⟨ 𝒮 ⟩) : 𝒰 (𝑖 ⁺) where
  -- field variableᵘ : ∀{𝑨 : ⟨ 𝒮 ⟩} -> ⟨ 𝒱 ⟩ -> 𝐂𝐭𝐱 𝑨
  -- field {{isFunctor:variable}} : ∀{𝑨 : ⟨ 𝒮 ⟩} -> isFunctor 𝒱 (𝐂𝐭𝐱 𝑨) variableᵘ

  field isVariable : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> Γ ⊢ τ -> 𝒰 (𝑖 ⌄ 1)
  field VariablePath : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ α : Type 𝑨} -> Γ ⊢ τ -> ⟨ Γ ⟩ ∍ α -> 𝒰 (𝑖 ⌄ 1)
  field Width : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> Γ ⊢ τ -> 𝒰 (𝑖 ⌄ 1)
  field VariableByWidth : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> (t : Γ ⊢ τ) -> isVariable {Γ} {τ} t ↔ (Width {Γ} {τ} t ≅ ⊥)
  field WidthBySubst : ∀{Γ Δ : 𝐂𝐭𝐱 𝑨} {τ α : Type 𝑨} -> (t : Γ ⊢ τ) -> (σ : Γ ⟶ Δ)
                       -> Width (t ◆ σ) ≅ Width t ⊔ (∑ λ (x : ⟨ Γ ⟩ ∍ α) -> ∑ λ (p : VariablePath t x) -> Width (σ at x))



