
module Verification.Classical.Space.Measure.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition

{-
open import Verification.Workspace.Structure.Example.Algebra.Monoid.Definition
open import Verification.Workspace.Structure.Example.Algebra.Group.Definition
open import Verification.Workspace.Structure.Example.Algebra.Abelian.Definition
open import Verification.Workspace.Structure.Example.Algebra.Ring.Definition
open import Verification.Workspace.Structure.Example.Algebra.Ring.Ordered
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder
open import Verification.Workspace.Structure.Definition2
-}

open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Universe.Definition -- for function ᶜ-σ

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Definition

open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition
open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Setoid.Power.Instance.HasCoproducts
open import Verification.Core.Setoid.Power.Instance.HasProducts
open import Verification.Core.Setoid.Power.Union
open import Verification.Core.Setoid.Power.Intersection
open import Verification.Core.Setoid.Construction.Product

{-
open import Verification.Core.Category.Std.Groupoid.As.Setoid
open import Verification.Core.Category.Std.Groupoid.Definition
open import Verification.Core.Category.Std.Category.Construction.Core
-}

open import Verification.Core.Set.Contradiction



module _ {Ω : Setoid 𝑖} where
  -- Setoid structure on subsetoid
  -- instance
  --   isSetoid:Subsetoid : isSetoid (𝒫 Ω)
  --   isSetoid:Subsetoid = (GroupoidΩsSetoid X)
  --     where
  --       X : Groupoid _
  --       X = 𝐂𝐨𝐫𝐞 (𝒫 Ω)



  infix 120 _ᶜ
  _ᶜ : 𝒫 Ω -> 𝒫 Ω
  _ᶜ U = Vᵘ since isSubsetoid:Vᵘ
    where
      Vᵘ : ⟨ Ω ⟩ -> Prop _
      Vᵘ a = ∣ ¬ (a ∈ U) ∣

      P : ∀{a b : ⟨ Ω ⟩} -> a ∼ b -> a ∈ Vᵘ -> b ∈ Vᵘ
      P a∼b a∈V = λ b∈U → a∈V (transp-Subsetoid (sym a∼b) b∈U)

      isSubsetoid:Vᵘ : isSubsetoid Vᵘ
      isSubsetoid:Vᵘ = record { transp-Subsetoid = P }

  map-ᶜ : ∀{U V : 𝒫 Ω} -> (V ⟶ U) -> U ᶜ ⟶ V ᶜ
  map-ᶜ f = incl (λ x∉U x∈V → x∉U (⟨ f ⟩ x∈V))

  cong-ᶜ : ∀{U V : 𝒫 Ω} -> (V ≅ U) -> V ᶜ ≅ U ᶜ
  cong-ᶜ ϕ = ψ⁻¹ since record { inverse-◆ = ψ ; inv-r-◆ = tt ; inv-l-◆ = tt }
    where
      ψ = map-ᶜ ⟨ ϕ ⟩
      ψ⁻¹ = map-ᶜ ⟨ ϕ ⟩⁻¹

  isFunctor:ᶜ : isFunctor (𝒫 Ω ᵒᵖ) (𝒫 Ω) (_ᶜ)
  isFunctor.map isFunctor:ᶜ = map-ᶜ
  isFunctor.isSetoidHom:map isFunctor:ᶜ = {!!}
  isFunctor.functoriality-id isFunctor:ᶜ = tt
  isFunctor.functoriality-◆ isFunctor:ᶜ = tt

  complement-of-⊥ : (⊥ ᶜ) ≅ ⊤
  complement-of-⊥ = f since record { inverse-◆ = g ; inv-r-◆ = tt ; inv-l-◆ = tt }
    where
      f : ⊥ ᶜ ⟶ ⊤
      f = incl (λ _ → tt)

      g : ⊤ ⟶ ⊥ ᶜ
      g = incl (λ _ x → impossible x)


  -- -- TODO: actu⊤-σy use generic set colimit
  -- set-union : ∀{I : 𝒰₀} -> (I -> 𝒫 Ω) -> 𝒫 Ω
  -- set-union As = Bᵘ since isSubsetoid:Bᵘ
  --   where
  --     Bᵘ : ⟨ Ω ⟩ -> Prop _
  --     Bᵘ a = ∣ (∑ λ n -> a ∈ As n) ∣

  --     P : ∀{a b : ⟨ Ω ⟩} -> a ∼ b -> a ∈ Bᵘ -> b ∈ Bᵘ
  --     P {a} {b} a∼b (n , a∈Asn) = n , transp-Subsetoid {{_}} {{of As n}} a∼b a∈Asn

  --     isSubsetoid:Bᵘ : isSubsetoid Bᵘ
  --     isSubsetoid:Bᵘ = record { transp-Subsetoid = P }

  -- set-union2 : ∀{I : 𝒰₀} -> (I -> 𝒫 Ω) -> 𝒫 Ω
  -- set-union2 X = ⨆ᵢ X


record isSigmaAlgebra {𝑗 : 𝔏} {𝑖} (Ω : Setoid 𝑖) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
  field Measurable : 𝒰 𝑗
  field ⟦_⟧ : Measurable -> 𝒫 Ω
  field ⊥-σ : Measurable
  field _ᶜ-σ : Measurable -> Measurable
  field ⨆-σ : (ℕ -> Measurable) -> Measurable

  field eval-⊥-σ : ⟦ ⊥-σ ⟧ ≅ ⊥
  field eval-ᶜ-σ : ∀{m : Measurable} -> ⟦ m ᶜ-σ ⟧ ≅ (⟦ m ⟧ ᶜ)
  field eval-⨆-σ : ∀{A} -> ⟦ ⨆-σ A ⟧ ≅ ⨆[ i ] ⟦ A i ⟧

open isSigmaAlgebra using (Measurable) public
open isSigmaAlgebra {{...}} hiding (Measurable) public

module _ (𝑗 : 𝔏 ^ 3) where
  SigmaAlgebra = Setoid (𝑗 ⌄ 0 ⋯ 1) :& isSigmaAlgebra {𝑗 ⌄ 2}

  macro 𝐌𝐞𝐚𝐬 = #structureOn SigmaAlgebra


module SigmaAlgebraProofs (Ω : SigmaAlgebra 𝑖) where
  ⊤-σ : Measurable (of Ω)
  ⊤-σ = ⊥-σ ᶜ-σ

  lem-1 : ⟦ ⊤-σ ⟧ ≅ ⊤
  lem-1 = ⟦ ⊥-σ ᶜ-σ ⟧   ⟨ eval-ᶜ-σ ⟩-≅
          ⟦ ⊥-σ ⟧ ᶜ     ⟨ cong-ᶜ eval-⊥-σ ⟩-≅
          ⊥ ᶜ           ⟨ complement-of-⊥ ⟩-≅
          ⊤             ∎-≅





