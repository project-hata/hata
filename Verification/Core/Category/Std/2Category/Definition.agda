
module Verification.Core.Category.Std.2Category.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Functor.Constant
-- open import Verification.Core.Category.Std.Functor.Instance.Category
-- open import Verification.Core.Category.Std.Natural.Definition
-- open import Verification.Core.Category.Std.Natural.Instance.Setoid
-- open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Setoid.As.Category
-- open import Verification.Core.Category.Std.Groupoid.As.Setoid
-- open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Groupoid.Definition
-- open import Verification.Core.Category.Std.Category.Construction.Core
-- open import Verification.Core.Setoid.Instance.Category



record is2Category {𝑗 : 𝔏 ^ 2} {𝑖} (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field cell : ∀(a b : ⟨ 𝒞 ⟩) -> isCategory {𝑗} (a ⟶ b)

  Cell : ∀(a b : ⟨ 𝒞 ⟩) -> Category _
  Cell a b = a ⟶ᵘ b since cell a b

  Comp : ∀{a b c} -> (Cell a b × Cell b c) -> (a ⟶ c)
  Comp = λ (f , g) -> f ◆ g

  Id : ∀{a : ⟨ 𝒞 ⟩} -> ⟨ ⊤-𝐂𝐚𝐭 {𝑖 ⌄ 0 , 𝑗 ⌄ 0 ⋯ 1} ⟩ -> a ⟶ a
  Id = λ _ -> id

  field isFunctor:Comp : ∀{a b c} -> isFunctor (Cell a b ×-𝐂𝐚𝐭 Cell b c) (Cell a c) Comp
  field isFunctor:Id : ∀{a} -> isFunctor ⊤-𝐂𝐚𝐭 (Cell a a) Id


module _ (𝑖 : 𝔏 ^ 5) where
  2Category = Category (𝑖 ⌄ 0 ⋯ 2) :& is2Category {𝑖 ⌄ 3 ⋯ 4}



