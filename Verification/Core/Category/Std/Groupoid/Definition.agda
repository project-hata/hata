
module Verification.Core.Category.Std.Groupoid.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso

record isGroupoid (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field isIso:hom : ∀{a b : ⟨ 𝒞 ⟩} -> (ϕ : a ⟶ b) -> isIso (hom ϕ)

open isGroupoid {{...}} public

module _ {𝒞 : Category 𝑖} {{X : isGroupoid 𝒞}} where
  _⁻¹-𝐆𝐫𝐩𝐝 : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ b -> b ⟶ a
  _⁻¹-𝐆𝐫𝐩𝐝 ϕ = (inverse-◆ (isIso:hom ϕ) )

module _ 𝑖 where
  Groupoid = Category 𝑖 :& isGroupoid



