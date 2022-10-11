
module Verification.Research.StateCalculus.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Category.Std.Category.Construction.Coproduct
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Data.List.Variant.Unary.Definition

module _ (𝒞 : Category 𝑖) where
  HomOf : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩ -> 𝒰 _
  HomOf a b = a ⟶ b

module _ (𝒞 : Category 𝑖) (x : ⟨ 𝒞 ⟩) where
  over : Category 𝑖
  over = {!!}

-- module _ (𝒞 : Category 𝑖) {{_ : hasInitial}}

module Version1 (𝒞 : Category 𝑖) (L : Category 𝑗) (d : ⟨ 𝒞 ⟩) (X : 𝒰 𝑘) (L₀ : 𝒰₀) (loc : L₀ -> ⟨ L ⟩)
  {{_ : hasFiniteCoproducts L}} {{_ : hasFiniteProducts 𝒞}} {{_ : hasFiniteProducts L}}
  where

  StateObject = ⟨ 𝒞 ⟩ ×-𝒰 ⟨ L ⟩

  data StateHom : StateObject -> StateObject -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    pure : ∀{a b} -> a ⟶ b -> ∀{m n} -> m ≅ n -> StateHom (a , m) (b , n)
    write : (i : L₀) -> StateHom (d , ⊥) ((⊤ , loc i))
    read : (i : L₀) -> StateHom (⊤ , loc i) (d , loc i)
    -- par : {a₀ a₁ b₀ b₁ m n} -> (m × n ≅ ⊥) -> StateHom (a₀ , m)

module Version2
  (𝒞 : Category 𝑖) (L : Functor 𝒞 (𝐂𝐚𝐭 𝑗))
  {{_ : hasFiniteProducts 𝒞}}
  -- {{_ : hasFiniteCoproducts L}} {{_ : hasFiniteProducts 𝒞}} {{_ : hasFiniteProducts L}}
  (d : ⟨ 𝒞 ⟩)
  (l0 : ⟨ 𝒞 ⟩)
  (loc : ∀{a} -> (a ⟶ l0) -> ⟨ (⟨ L ⟩ a) ⟩)
  where

  -- LExt : 𝒰 ?
  -- LExt =
  -- StateObject = ⟨ 𝒞 ⟩ ×-𝒰 ⟨ L ⟩

  data StateHom : (a b : ⟨ 𝒞 ⟩) {m n : ⟨ ⟨ L ⟩ a ⟩} (f : HomOf (⟨ L ⟩ a) m n) -> 𝒰 (𝑖 ､ 𝑗) where
    -- pure : ∀{a b} -> a ⟶ b -> ∀{m n : ⟨ L ⟩} -> (ϕ : m ≅ n) -> StateHom a b ⟨ ϕ ⟩
    write : StateHom (d ⊓ l0) ⊤ {loc π₁} {loc π₁} {!!}

  --   write : (i : L₀) -> StateHom (d , ⊥) ((⊤ , loc i))
  --   read : (i : L₀) -> StateHom (⊤ , loc i) (d , loc i)
    -- par : {a₀ a₁ b₀ b₁ m n} -> (m × n ≅ ⊥) -> StateHom (a₀ , m)




