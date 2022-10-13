
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Workspace.Structure.Example.Algebra.Abelian.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Workspace.Structure.Example.Algebra.Monoid.Definition
open import Verification.Workspace.Structure.Example.Algebra.Group.Definition
-- open import Verification.Core.Algebra.Group.Quotient

open import Verification.Workspace.Structure.Definition2


Abelian' : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Abelian' 𝑗 = Monoid' 𝑗 :&' (isGroup :,' isCommutative)

{-

-- record isSubabelian {𝑗 : 𝔏 ^ 2} {A : Abelian 𝑗} (P : 𝒫-𝒰 ⟨ A ⟩ :& isSubsetoid :& isSubmonoid :& isSubgroup) : 𝒰 𝑗 where
-- open isSubabelian {{...}} public


-- Subabelian : {𝑗 : 𝔏 ^ 2} (A : Abelian 𝑗) -> 𝒰 _
-- Subabelian A = Subgroup ′ ⟨ A ⟩ ′ :& isSubabelian {A = A}


-- module _ {𝑗 : 𝔏 ^ 2} {A : Group 𝑗} {B : Subgroup A} {{_ : isCommutative ′ ⟨ A ⟩ ′}} where
--   instance
--     isNormal:Subabelian : isNormal ′ ⟨ B ⟩ ′
--     isNormal.normal isNormal:Subabelian a {b} b∈B =
--       let P₀ = b             ≣⟨ unit-r-⋆ ⁻¹ ⟩
--                 b ⋆ ◌         ≣⟨ refl ≀⋆≀ inv-r-⋆ ⁻¹ ⟩
--                 b ⋆ (a ⋆ ◡ a) ≣⟨ assoc-r-⋆ ⟩
--                 b ⋆ a ⋆ ◡ a   ≣⟨ comm-⋆ ≀⋆≀ refl ⟩
--                 a ⋆ b ⋆ ◡ a   ∎

--           P₁ : ⟨ ⟨ B ⟩ (a ⋆ b ⋆ ◡ a) ⟩
--           P₁ = transp-Subsetoid P₀ b∈B
--       in P₁

{-
module _ {𝑗 : 𝔏 ^ 2} {A : Group 𝑗} {{_ : isCommutative ′ ⟨ A ⟩ ′}} {B : Subgroup A} where

  instance
    isCommutative:AbelianQuot : isCommutative (′ ⟨ ′ ⟨ A ⟩ ′ /-Group ′ ⟨ B ⟩ ′ ⟩ ′)
    isCommutative.comm-⋆ isCommutative:AbelianQuot {a = [ a ]} {b = [ b ]} = cong-∼ comm-⋆


_/-Abelian_ : {𝑗 : 𝔏 ^ 2} (A : Abelian 𝑗) -> (B : Subabelian A) -> Abelian _
_/-Abelian_ A B = ′ ⟨ A ⟩ /-𝒰 RelSubgroup ′ ⟨ B ⟩ ′ ′

-}
-}
