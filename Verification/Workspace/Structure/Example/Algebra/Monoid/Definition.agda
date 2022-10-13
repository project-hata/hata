
module Verification.Workspace.Structure.Example.Algebra.Monoid.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition

open import Verification.Workspace.Structure.Definition2


Setoid' : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Setoid' 𝑗 = 𝒰 (𝑗 ⌄ 0) :&' isSetoid {𝑗 ⌄ 1}

ι-Setoid' : Setoid' 𝑗 -> Setoid 𝑗
ι-Setoid' = {!!}

-- p-Setoid' : (A : Setoid' 𝑗) -> isSetoid El A
-- p-Setoid' (make:&' ⟨_⟩₁ A B) = B

-- #Notation/Rewrite# ◌ = \Circle

-- [Definition]
-- | A setoid |A| is a /monoid/, that is, the type [..] is inhabited,
--   if the following data is given.
record isMonoid {𝑗 : 𝔏 ^ 2} (A : Setoid' 𝑗) : 𝒰 (𝑗) where

  private instance
    I1 : isSetoid (ifst A)
    I1 = isnd A

  -- | 1. A binary operation [..].
  field _⋆_ : El A -> El A -> El A

  -- | 2. A specified element [..].
        ◌ : El A

  -- | 3. Proofs that |⋆| is associative,
  --      and |◌| is a unit for it.
        unit-l-⋆   : ∀ {a} -> ◌ ⋆ a ∼ a
        unit-r-⋆   : ∀ {a} -> a ⋆ ◌ ∼ a
        assoc-l-⋆  : ∀ {a b c} -> (a ⋆ b) ⋆ c ∼ a ⋆ (b ⋆ c)

  -- | 4. Finally, a proof that the operation is compatible
  --      with the equivalence relation.
        _≀⋆≀_ : ∀{a₀ a₁ b₀ b₁} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ⋆ b₀ ∼ a₁ ⋆ b₁

  -- | We further write [] [..].
  assoc-r-⋆ : ∀{a b c} -> a ⋆ (b ⋆ c) ∼ (a ⋆ b) ⋆ c
  assoc-r-⋆ = assoc-l-⋆ ⁻¹

  infixl 50 _⋆_ _≀⋆≀_
open isMonoid {{...}} public

-- module intertest1 {A : Setoid' 𝑗} {{X : isMonoid A}} where
--   testf : (a : El A) -> a ∼ a
--   testf = {!!}

Monoid' : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Monoid' 𝑗 = Setoid' 𝑗 :&' isMonoid



record Monoid (𝑗 : 𝔏 ^ 2) : 𝒰 (𝑗 ⁺) where
  field ⟨_⟩ : 𝒰 (𝑗 ⌄ 0)
  field {{isSetoid:This}} : isSetoid {𝑗 ⌄ 1} ⟨_⟩
  field {{isMonoid:This}} : isMonoid (make:&' ⟨_⟩ isSetoid:This)
  -- (make:&' ⟨_⟩ (record {}) isSetoid:This)

open Monoid {{...}} public

module _ {𝑗} where
  instance
    hasU2:Monoid : hasU2 (Monoid 𝑗) _
    getU hasU2:Monoid = 𝒰 (𝑗 ⌄ 0)
    destructEl hasU2:Monoid = λ M -> ⟨ M ⟩


open Monoid {{...}} public

module intertest2 {A : Monoid 𝑗} where
  postulate testf : (a : El A) -> a ⋆ a ∼ a



-- module _ {A : 𝒰 _} {{Ap : A is Monoid 𝑖}} where
--   macro
--    ⋆⃨ : SomeStructure
--    ⋆⃨ = #structureOn (λ₋ {A = A} {B = A} {C = A} (_⋆_))


record isCommutative {𝑗 : 𝔏 ^ 2} (A : Monoid' 𝑗) : 𝒰 𝑗 where

  private instance
    _ : isMonoid (ifst A)
    _ = isnd A

    _ : isSetoid _
    _ = isnd (ifst A)

  field comm-⋆ : ∀{a b : El A} -> a ⋆ b ∼ b ⋆ a

open isCommutative {{...}} public


record isSubmonoid {𝑗 : 𝔏 ^ 2} (A : Monoid 𝑗) (P : 𝒫 (El A) :& isSubsetoid) : 𝒰 𝑗 where
  field closed-◌ : ◌ ∈ P
        closed-⋆ : ∀{a b : El A} -> a ∈ P -> b ∈ P -> (a ⋆ b) ∈ P
        --⟨ ⟨ P ⟩ a ⟩ -> ⟨ ⟨ P ⟩ b ⟩ -> ⟨ ⟨ P ⟩ (a ⋆ b) ⟩
open isSubmonoid {{...}} public


Submonoid : (M : Monoid 𝑖) -> 𝒰 _
Submonoid M = _ :& isSubmonoid M

module _ (A : Monoid 𝑖) (B : Monoid 𝑗) where
  record isMonoidHom (f : SetoidHom ′ El A ′ ′ ⟨ B ⟩ ′) : 𝒰 (𝑖 ､ 𝑗) where
    field pres-◌ : ⟨ f ⟩ ◌ ∼ ◌
    field pres-⋆ : ∀{a b : El A} -> ⟨ f ⟩ (a ⋆ b) ∼ ⟨ f ⟩ a ⋆ ⟨ f ⟩ b

  MonoidHom : 𝒰 _
  MonoidHom = _ :& isMonoidHom

open isMonoidHom {{...}} public

module _ {A : Monoid 𝑖} {B : Monoid 𝑗} where

  instance
    isSetoid:MonoidHom : isSetoid (MonoidHom A B)
    isSetoid:MonoidHom = isSetoid:FullSubsetoid (_ since isSetoid:SetoidHom) (λ f -> ↳ f)

-- //

{-
-}
