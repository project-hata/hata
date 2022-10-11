
module Verification.Core.Data.Prop.Definition where

open import Verification.Core.Conventions

record Prop (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  -- no-eta-equality
  constructor ∣_∣-Prop
  field ⟨_⟩ : 𝒰 𝑖
open Prop public

instance
  Notation-Absolute:Prop : Notation-Absolute (𝒰 𝑖) (Prop 𝑖)
  Notation-Absolute.∣_∣ Notation-Absolute:Prop = ∣_∣-Prop


𝒫-𝒰 : 𝒰 𝑖 -> 𝒰 (𝑖 ⁺)
𝒫-𝒰 {𝑖} A = A -> Prop 𝑖

-------------------------
-- notation for 𝒫


record hasPower (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field 𝒫ᵘ : A -> B

open hasPower {{...}} public

instance
  hasPower:𝒰 : hasPower (𝒰 𝑖) (𝒰 (𝑖 ⁺))
  hasPower:𝒰 = record { 𝒫ᵘ = 𝒫-𝒰 }

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : hasPower A B}} (a : A) where
  macro
    𝒫 = #structureOn (𝒫ᵘ a)



---------------------------------------------------------------
-- finitary Operators

infix 40 _∈_ _⊆_

_∈_ : {A : 𝒰 𝑙} -> (a : A) -> {U : 𝒰 𝑖} -> (u : U) -> {{UU : hasU U (𝑗 ⁺ ⊔ 𝑙) 𝑘}} -> {{_ : getU UU ≡-Str (A -> Prop 𝑗)}} -> 𝒰 𝑗
_∈_ a u {{UU}} {{p}} with destructEl UU u | p
... | f | refl-StrId = ⟨ f a ⟩

_⊆_ : {A : 𝒰 𝑙} ->
      {U : 𝒰 𝑖₀} -> (u : U) -> {{UU : hasU U (𝑗₀ ⁺ ⊔ 𝑙) 𝑘}} -> {{_ : getU UU ≡-Str (A -> Prop 𝑗₀)}}
      {V : 𝒰 𝑖₁} -> (v : V) -> {{VV : hasU V (𝑗₁ ⁺ ⊔ 𝑙) 𝑘}} -> {{_ : getU VV ≡-Str (A -> Prop 𝑗₁)}}
      -> 𝒰 (𝑗₀ ､ 𝑗₁ ､ 𝑙)
_⊆_ {A = A} u {{UU}} {{p}} v {{VV}} {{q}} with destructEl UU u | p | destructEl VV v | q
... | f | refl-StrId | g | refl-StrId = ∀{a : A} -> ⟨ f a ⟩ -> ⟨ g a ⟩


module _ {A : 𝒰 𝑙}
      {U : 𝒰 𝑖₀}  (u : U)  {{UU : hasU U (𝑗₀ ⁺ ⊔ 𝑙) 𝑘}}  {{_ : getU UU ≡-Str (A -> Prop 𝑗₀)}}
      {V : 𝒰 𝑖₁}  (v : V)  {{VV : hasU V (𝑗₁ ⁺ ⊔ 𝑙) 𝑘}}  {{_ : getU VV ≡-Str (A -> Prop 𝑗₁)}}
      where

  infixr 60 _∩_ _∪_ _∩ᵘ_ _∪ᵘ_

  _∪ᵘ_ : A -> Prop (𝑗₀ ､ 𝑗₁)
  _∪ᵘ_ a = ∣ a ∈ u +-𝒰 a ∈ v ∣

  _∩ᵘ_ : A -> Prop (𝑗₀ ､ 𝑗₁)
  _∩ᵘ_ a = ∣ a ∈ u ×-𝒰 a ∈ v ∣

  macro _∪_ = #structureOn _∪ᵘ_
  macro _∩_ = #structureOn _∩ᵘ_

module _ {A : 𝒰 𝑙} where
  module _ {𝑗} where
    ∅ᵘ : A -> Prop 𝑗
    ∅ᵘ a = ∣ ⊥-𝒰 ∣

    ℧ᵘ : A -> Prop 𝑗
    ℧ᵘ a = ∣ ⊤-𝒰 ∣

    macro ∅ = #structureOn ∅ᵘ
    macro ℧ = #structureOn ℧ᵘ

---------------------------------------------------------------
-- indexed Operators

module _ {A : 𝒰 𝑙} {I : 𝒰 𝑙₀}
      {U : 𝒰 𝑖₀}  (uᵢ : I -> U)  {{UU : hasU U (𝑗₀ ⁺ ⊔ 𝑙) 𝑘}}  {{_ : getU UU ≡-Str (A -> Prop 𝑗₀)}}
      where

  ⋂ᵘ : A -> Prop _
  ⋂ᵘ a = ∣ (∀ (i : I) -> a ∈ uᵢ i) ∣

  ⋃ᵘ : A -> Prop _
  ⋃ᵘ a = ∣ ∑ (λ (i : I) -> a ∈ uᵢ i) ∣

  macro ⋂ = #structureOn ⋂ᵘ
  macro ⋃ = #structureOn ⋃ᵘ



---------------------------------------------------------------
-- Existence

record ⦋_⦌ {U : 𝒰 𝑖} (P : U -> Prop 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  constructor _∢_
  field ⟨_⟩ : U
  field Proof : Prop.⟨_⟩ (P ⟨_⟩)
open ⦋_⦌ public

infix 60 _∢_


infix 1 exists

exists : ∀{A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> Prop (ℓ ⊔ ℓ')
exists B = ∣ ∑ B ∣

syntax exists (λ x -> F) = ∃ x , F

-- module _  where
existsIn : {A : 𝒰 𝑙} {U : 𝒰 𝑖} -> (u : U) -> {{UU : hasU U (𝑗 ⁺ ⊔ 𝑙) 𝑘}} {{_ : getU UU ≡-Str (A -> Prop 𝑗)}} -> (C : A -> 𝒰 𝑖₁) -> Prop (𝑙 ､ 𝑗 ､ 𝑖₁)
existsIn u C = ∣ ∑ (λ a -> (a ∈ u) ×-𝒰 C a) ∣

syntax existsIn U (λ x -> F) = ∃ x ∈ U , F


