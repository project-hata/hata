
module Verification.Core.Category.Std.Groupoid.As.Setoid where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Groupoid.Definition

GroupoidAsSetoid : Groupoid 𝑖 -> Setoid _
GroupoidAsSetoid 𝒢 = ⟨ 𝒢 ⟩ since isSetoid:byDef (λ a b -> a ⟶ b) id _⁻¹-𝐆𝐫𝐩𝐝 _◆_



