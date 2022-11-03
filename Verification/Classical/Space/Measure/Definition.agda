
module Verification.Classical.Space.Measure.Definition where

open import Verification.Conventions hiding (comp)
open import Verification.Core.Setoid.Definition

open import Verification.Workspace.Structure.Example.Algebra.Monoid.Definition
open import Verification.Workspace.Structure.Example.Algebra.Group.Definition
open import Verification.Workspace.Structure.Example.Algebra.Abelian.Definition
open import Verification.Workspace.Structure.Example.Algebra.Ring.Definition
open import Verification.Workspace.Structure.Example.Algebra.Ring.Ordered
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder

open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Universe.Definition -- for function comp

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition

open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Definition
open import Verification.Core.Setoid.Power.Union
open import Verification.Core.Setoid.Power.Intersection

open import Verification.Core.Setoid.Power.Instance.HasCoproducts
open import Verification.Core.Setoid.Power.Instance.HasProducts
open import Verification.Core.Setoid.Construction.Product

open import Verification.Workspace.Structure.Definition2


open import Verification.Core.Category.Std.Groupoid.As.Setoid
open import Verification.Core.Category.Std.Groupoid.Definition
open import Verification.Core.Category.Std.Category.Construction.Core

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


  -- TODO: actually use generic set colimit
  set-union : ∀{I : 𝒰₀} -> (I -> 𝒫 Ω) -> 𝒫 Ω
  set-union As = Bᵘ since isSubsetoid:Bᵘ
    where
      Bᵘ : ⟨ Ω ⟩ -> Prop _
      Bᵘ a = ∣ (∑ λ n -> a ∈ As n) ∣

      P : ∀{a b : ⟨ Ω ⟩} -> a ∼ b -> a ∈ Bᵘ -> b ∈ Bᵘ
      P {a} {b} a∼b (n , a∈Asn) = n , transp-Subsetoid {{_}} {{of As n}} a∼b a∈Asn

      isSubsetoid:Bᵘ : isSubsetoid Bᵘ
      isSubsetoid:Bᵘ = record { transp-Subsetoid = P }


record isSigmaAlgebra {𝑗 : 𝔏} {𝑖} (Ω : Setoid 𝑖) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
  field Measurable : 𝒰 𝑗
  field 𝒻 : Measurable -> 𝒫 Ω
  field empt : Measurable
  field comp : Measurable -> Measurable
  field σ-union : (ℕ -> Measurable) -> Measurable

  field isEmpt : 𝒻 empt ≅ ⊥
  field isComp : ∀{m : Measurable} -> 𝒻 (comp m) ≅ (𝒻 m ᶜ)
  field closed-σ-union : ∀{As} -> 𝒻 (σ-union As) ≅ set-union (𝒻 ∘ As)

open isSigmaAlgebra using (Measurable) public
open isSigmaAlgebra {{...}} hiding (Measurable) public

module _ (𝑗 : 𝔏 ^ 3) where
  SigmaAlgebra = Setoid (𝑗 ⌄ 0 ⋯ 1) :& isSigmaAlgebra {𝑗 ⌄ 2}



module SigmaAlgebraProofs (Ω : SigmaAlgebra 𝑖) where
  all : Measurable (of Ω)
  all = comp empt

  lem-1 : 𝒻 all ≅ ⊤
  lem-1 = isComp ∙-≅ (cong-ᶜ isEmpt ∙-≅ complement-of-⊥)







