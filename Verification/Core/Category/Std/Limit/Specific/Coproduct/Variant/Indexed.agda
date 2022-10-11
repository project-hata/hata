
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Indexed where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Notation.Associativity


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where

  record isIndexedCoproduct {I : 𝒰 𝑘} (aᵢ : I -> 𝒞) (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    field ιᵢ : ∀ i -> aᵢ i ⟶ x
    field ⦗_⦘ᵢ : ∀{y} -> (∀ i -> aᵢ i ⟶ y) -> x ⟶ y
    field reduce-ιᵢ : ∀{y} -> (f : ∀ i -> aᵢ i ⟶ y) -> ∀ i -> ιᵢ i ◆ ⦗ f ⦘ᵢ ∼ f i
    field expand-ιᵢ : ∀{y} -> (f : x ⟶ y) -> f ∼ ⦗ (λ i -> ιᵢ i ◆ f) ⦘ᵢ

    coproduct-syntax = ⦗_⦘ᵢ
    syntax coproduct-syntax (λ i -> f) = ⦗ f ⦘[ i ]

  open isIndexedCoproduct {{...}} public

-- NOTE: This one, strangely (?) does not work sometimes.
--       I.e., the type inference does not get the instance even though it exists.
--
{-
record hasIndexedCoproducts (I : 𝒰 𝑗) (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗) where
  infixl 80 ⨆ᵢ
  field ⨆ᵢ : (I -> ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
  field {{isIndexedCoproduct:⨆ᵢ}} : ∀{x : I -> ⟨ 𝒞 ⟩} -> isIndexedCoproduct x (⨆ᵢ x)

  syntax ⨆ᵢ (λ i -> X) = ⨆[ i ] X

open hasIndexedCoproducts {{...}} public
-}
--
-- END NOTE.


-- module _ (𝑗 : 𝔏) (𝒞 : Category 𝑖) where
  -- hasAllIndexedCoproducts : ∀{I : 𝒰 𝑗} -> 𝒰 _
  -- hasAllIndexedCoproducts {I} = hasIndexedCoproducts I 𝒞

-- record hasAllIndexedCoproducts (𝑗 : 𝔏) (𝒞 : Category 𝑖): 𝒰 (𝑖 ､ 𝑗 ⁺) where
--   field {{hasIndexedCoproducts:this}} : ∀{I : 𝒰 𝑗} -> hasIndexedCoproducts I 𝒞

record hasAllIndexedCoproducts (𝑗 : 𝔏) (𝒞 : Category 𝑖): 𝒰 (𝑖 ､ 𝑗 ⁺) where
  infixl 80 ⨆ᵢ
  field ⨆ᵢ : ∀{I : 𝒰 𝑗} -> (I -> ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
  field {{isIndexedCoproduct:⨆ᵢ}} : ∀{I : 𝒰 𝑗} -> ∀{x : I -> ⟨ 𝒞 ⟩} -> isIndexedCoproduct x (⨆ᵢ x)

  syntax ⨆ᵢ (λ i -> X) = ⨆[ i ] X

open hasAllIndexedCoproducts {{...}} public

