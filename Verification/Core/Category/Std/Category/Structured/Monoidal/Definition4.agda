
module Verification.Core.Category.Std.Category.Structured.Monoidal.Definition4 where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Iso
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Properties.Monoidal


module _ {a b c : 𝐂𝐚𝐭 𝑖} where
  α-𝐂𝐚𝐭 : ((a × b) ×-𝐂𝐚𝐭 c) ⟶ (a × (b × c))
  α-𝐂𝐚𝐭 = ⟨ assoc-l-⊓ ⟩

record isMonoidal (𝒞 : Category 𝑖) : 𝒰 𝑖 where

  -- field ⊗[_] : Functor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞
  -- field Ident : Functor (⊤-𝐂𝐚𝐭 {𝑖}) 𝒞

  -- field assoc-l-⊗ : (⊗[_] ⇃⊓⇂ id-𝐂𝐚𝐭) ◆-𝐂𝐚𝐭 ⊗[_] ≅ (α-𝐂𝐚𝐭 ◆ (id-𝐂𝐚𝐭 ⇃⊓⇂ ⊗[_]) ◆ ⊗[_])
  -- field unit-r-⊗ : ⧼ id-𝐂𝐚𝐭 , (intro-⊤ ◆ Ident) ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 ⊗[_] ≅ id
  -- field unit-l-⊗ : ⧼ intro-⊤ ◆ Ident , id-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 ⊗[_] ≅ id

  field _⊗_ : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
  field ident : ⟨ 𝒞 ⟩

  field _⇃⊗⇂_ : ∀{a b c d : ⟨ 𝒞 ⟩} -> (f : a ⟶ c) -> (g : b ⟶ d) -> a ⊗ b ⟶ c ⊗ d

  infixl 80 _⊗_ _⇃⊗⇂_


  -- field iα : ∀(a b c : ⟨ 𝒞 ⟩) -> (a ⊗ b) ⊗ c ≅ a ⊗ (b ⊗ c)
  -- iα a b c = ⟨ ⟨ assoc-l-⊗ ⟩ ⟩ ((a , b) , c)

  -- field iρ : ∀(a : ⟨ 𝒞 ⟩) -> a ⊗ ident ≅ a
  -- iρ a = ⟨ ⟨ unit-r-⊗ ⟩ ⟩ a

  -- field iλ : ∀(a : ⟨ 𝒞 ⟩) -> ident ⊗ a ≅ a
  -- iλ a = ⟨ ⟨ unit-l-⊗ ⟩ ⟩ a

  field fα : ∀(a b c : ⟨ 𝒞 ⟩) -> (a ⊗ b) ⊗ c ⟶ a ⊗ (b ⊗ c)
  -- fα a b c = ⟨ ⟨ assoc-l-⊗ ⟩ ⟩ ((a , b) , c)

  field fρ : ∀(a : ⟨ 𝒞 ⟩) -> a ⊗ ident ⟶ a
  -- fρ a = ⟨ ⟨ unit-r-⊗ ⟩ ⟩ a

  field fλ : ∀(a : ⟨ 𝒞 ⟩) -> ident ⊗ a ⟶ a
  -- fλ a = ⟨ ⟨ unit-l-⊗ ⟩ ⟩ a

  field bα : ∀(a b c : ⟨ 𝒞 ⟩) -> a ⊗ (b ⊗ c) ⟶ (a ⊗ b) ⊗ c
  -- bα a b c = ⟨ ⟨ assoc-l-⊗ ⟩⁻¹ ⟩ ((a , b) , c)

  field bρ : ∀(a : ⟨ 𝒞 ⟩) -> a ⟶ a ⊗ ident
  -- bρ a = ⟨ ⟨ unit-r-⊗ ⟩⁻¹ ⟩ a

  field bλ : ∀(a : ⟨ 𝒞 ⟩) -> a ⟶ ident ⊗ a
  -- bλ a = ⟨ ⟨ unit-l-⊗ ⟩⁻¹ ⟩ a

{-
-}

  field triangle : ∀{A B : ⟨ 𝒞 ⟩} -> (fρ A ⇃⊗⇂ id {a = B}) ∼ (fα A ident B ◆ (id ⇃⊗⇂ fλ B))



module _ 𝑖 where
  Monoidal = Category 𝑖 :& isMonoidal



