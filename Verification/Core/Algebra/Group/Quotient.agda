
module Verification.Core.Algebra.Group.Quotient where

open import Verification.Core.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition

module _ {𝑗 : 𝔏 ^ 2} {G : Group 𝑗} where
  record isNormal (H : Subgroup G) : 𝒰 𝑗 where
    field normal : ∀ a -> ∀{b : ⟨ G ⟩} -> ⟨ ⟨ H ⟩ b ⟩ -> ⟨ ⟨ H ⟩ (a ⋆ b ⋆ ◡ a) ⟩

  open isNormal {{...}} public

module _ where
-- private
  module _ {𝑗 : 𝔏 ^ 2} {G : Group 𝑗} {H : Subgroup G} {{_ : isNormal H}} where

    private
      lem-10 : ∀{a : ⟨ G ⟩} -> RelSubgroup H a a
      lem-10 {a} = incl (transp-∼ (inv-r-⋆ ⁻¹) closed-◌)

      lem-20 : ∀{a b} -> RelSubgroup H a b -> RelSubgroup H b a
      lem-20 {a} {b} (incl x) =
        let p : ◡ (a ⋆ ◡ b) ∼ b ⋆ (◡ a)
            p = ◡ (a ⋆ ◡ b) ≣⟨ distr-⋆-◡ ⟩
                ◡ ◡ b ⋆ ◡ a ≣⟨ double-◡ ≀⋆≀ refl ⟩
                b ⋆ ◡ a     ∎
        in incl (transp-∼ p (closed-◡ x))

      lem-30 : ∀{a b c} -> RelSubgroup H a b -> RelSubgroup H b c -> RelSubgroup H a c
      lem-30 {a} {b} {c} (incl p) (incl q) =
        let P = (a ⋆ ◡ b) ⋆ (b ⋆ ◡ c) ≣⟨ assoc-r-⋆ ⟩
                (a ⋆ ◡ b) ⋆ b ⋆ ◡ c   ≣⟨ assoc-l-⋆ ≀⋆≀ refl ⟩
                a ⋆ (◡ b ⋆ b) ⋆ ◡ c   ≣⟨ refl ≀⋆≀ inv-l-⋆ ≀⋆≀ refl ⟩
                a ⋆ ◌ ⋆ ◡ c           ≣⟨ unit-r-⋆ ≀⋆≀ refl ⟩
                a ⋆ ◡ c               ∎
        in incl (transp-∼ P (closed-⋆ p q))

    instance
      isEquivRel:RelSubgroup : isEquivRel (RelSubgroup H)
      isEquivRel.refl-Equiv isEquivRel:RelSubgroup = lem-10
      isEquivRel.sym-Equiv isEquivRel:RelSubgroup = lem-20
      isEquivRel._∙-Equiv_ isEquivRel:RelSubgroup = lem-30

    instance
      isSetoidHom:[] : isSetoidHom ′(⟨ G ⟩)′ ′(⟨ G ⟩ /-𝒰 RelSubgroup H)′ [_]
      isSetoidHom.cong-∼ isSetoidHom:[] {a} {b} (p) =
        let P = a ⋆ ◡ b ≣⟨ p ≀⋆≀ refl ⟩
                b ⋆ ◡ b ≣⟨ inv-r-⋆ ⟩
                ◌       ∎
        in incl (incl (transp-∼ (P ⁻¹) closed-◌))

    instance
      isMonoid:GroupQuot : isMonoid ′ ⟨ G ⟩ /-𝒰 RelSubgroup H ′
      isMonoid._⋆_ isMonoid:GroupQuot [ a ] [ b ] = [ a ⋆ b ]
      isMonoid.◌ isMonoid:GroupQuot = [ ◌ ]
      isMonoid.unit-l-⋆ isMonoid:GroupQuot {a = [ a ]} = cong-∼ unit-l-⋆
      isMonoid.unit-r-⋆ isMonoid:GroupQuot {a = [ a ]} = cong-∼ unit-r-⋆
      isMonoid.assoc-l-⋆ isMonoid:GroupQuot {a = [ a ]} {b = [ b ]} {c = [ c ]} = cong-∼ assoc-l-⋆
      -- isMonoid.assoc-r-⋆ isMonoid:GroupQuot {a = [ a ]} {b = [ b ]} {c = [ c ]} = cong-∼ assoc-r-⋆
      isMonoid._≀⋆≀_ isMonoid:GroupQuot {a₀ = [ a₀ ]} {a₁ = [ a₁ ]} {b₀ = [ b₀ ]} {b₁ = [ b₁ ]} (incl (incl p)) (incl (incl q)) =
        let P₀ : ⟨ ⟨ H ⟩ (a₁ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁) ⟩
            P₀ = normal a₁ q

            P₁ : ⟨ ⟨ H ⟩ ((a₀ ⋆ ◡ a₁) ⋆ (a₁ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁)) ⟩
            P₁ = closed-⋆ p P₀

            P₂ = ((a₀ ⋆ ◡ a₁) ⋆ (a₁ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁))  ≣⟨ assoc-l-⋆ ⟩
                (a₀ ⋆ (◡ a₁ ⋆ (a₁ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁)))  ≣⟨ refl ≀⋆≀ assoc-r-⋆ ⟩
                (a₀ ⋆ (◡ a₁ ⋆ (a₁ ⋆ (b₀ ⋆ ◡ b₁)) ⋆ ◡ a₁))  ≣⟨ refl ≀⋆≀ (assoc-r-⋆ ≀⋆≀ refl) ⟩
                (a₀ ⋆ ((◡ a₁ ⋆ a₁) ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁))  ≣⟨ refl ≀⋆≀ ((inv-l-⋆ ≀⋆≀ refl) ≀⋆≀ refl) ⟩
                (a₀ ⋆ (◌ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁))            ≣⟨ refl ≀⋆≀ (unit-l-⋆ ≀⋆≀ refl) ⟩
                (a₀ ⋆ ((b₀ ⋆ ◡ b₁) ⋆ ◡ a₁))                ≣⟨ refl ≀⋆≀ assoc-l-⋆ ⟩
                (a₀ ⋆ (b₀ ⋆ (◡ b₁ ⋆ ◡ a₁)))                ≣⟨ assoc-r-⋆ ⟩
                ((a₀ ⋆ b₀) ⋆ (◡ b₁ ⋆ ◡ a₁))                ≣⟨ refl ≀⋆≀ distr-⋆-◡ ⁻¹ ⟩
                (a₀ ⋆ b₀) ⋆ ◡ (a₁ ⋆ b₁)                    ∎

            P₃ : ⟨ ⟨ H ⟩ ((a₀ ⋆ b₀) ⋆ ◡ (a₁ ⋆ b₁)) ⟩
            P₃ = transp-∼ P₂ P₁

        in incl (incl P₃)

    instance
      isGroup:GroupQuot : isGroup ′ ⟨ G ⟩ /-𝒰 RelSubgroup H ′
      isGroup.◡_ isGroup:GroupQuot [ a ] = [ ◡ a ]
      isGroup.inv-l-⋆ isGroup:GroupQuot {a = [ a ]} = cong-∼ inv-l-⋆
      isGroup.inv-r-⋆ isGroup:GroupQuot {a = [ a ]} = cong-∼ inv-r-⋆
      isGroup.cong-◡_ isGroup:GroupQuot {a₀ = [ a₀ ]} {a₁ = [ a₁ ]} (incl (incl p)) =
        let P₀ = ◡ (a₀ ⋆ ◡ a₁)               ≣⟨ distr-⋆-◡ ⟩
                  ◡ ◡ a₁ ⋆ ◡ a₀               ≣⟨ double-◡ ≀⋆≀ refl ⟩
                  a₁ ⋆ ◡ a₀                   ∎

            P₁ : ⟨ ⟨ H ⟩ (a₁ ⋆ ◡ a₀) ⟩
            P₁ = transp-∼ P₀ (closed-◡ p)

            P₂ : ⟨ ⟨ H ⟩ (◡ a₁ ⋆ (a₁ ⋆ ◡ a₀) ⋆ ◡ ◡ a₁) ⟩
            P₂ = normal (◡ a₁) P₁

            P₃ = ◡ a₁ ⋆ (a₁ ⋆ ◡ a₀) ⋆ ◡ ◡ a₁ ≣⟨ assoc-r-⋆ ≀⋆≀ refl ⟩
                  (◡ a₁ ⋆ a₁) ⋆ ◡ a₀ ⋆ ◡ ◡ a₁ ≣⟨ inv-l-⋆ ≀⋆≀ refl ≀⋆≀ refl ⟩
                  ◌ ⋆ ◡ a₀ ⋆ ◡ ◡ a₁           ≣⟨ unit-l-⋆ ≀⋆≀ refl ⟩
                  ◡ a₀ ⋆ ◡ ◡ a₁               ∎

            P₄ : ⟨ ⟨ H ⟩ (◡ a₀ ⋆ ◡ ◡ a₁) ⟩
            P₄ = transp-∼ P₃ P₂
        in incl (incl P₄)

_/-Group_ : {𝑗 : 𝔏 ^ 2} (G : Group 𝑗) -> (H : Subgroup G) {{_ : isNormal H}} -> Group _
_/-Group_ G H = ′ ⟨ G ⟩ /-𝒰 RelSubgroup H ′

