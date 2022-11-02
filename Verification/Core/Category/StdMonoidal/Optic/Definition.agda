
module Verification.Core.Category.StdMonoidal.Optic.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Category.StdMonoidal.Category.Definition



module _ (𝒞 : Monoidal 𝑖) where
  record Optic : 𝒰 𝑖 where
    field source : ⟨ 𝒞 ⟩
    field target : ⟨ 𝒞 ⟩

  open Optic public

  macro 𝐎𝐩𝐭𝐢𝐜 = #structureOn Optic

module _ {𝒞 : Monoidal 𝑖} where
  record Hom-𝐎𝐩𝐭𝐢𝐜 (A B : Optic 𝒞) : 𝒰 𝑖 where
    constructor _,_
    field {State} : ⟨ 𝒞 ⟩
    field get : source A ⟶ State ⊗ source B
    field put : State ⊗ target B ⟶ target A

  open Hom-𝐎𝐩𝐭𝐢𝐜 public

  module _ {A B : Optic 𝒞} where
    data _∼-Hom-𝐎𝐩𝐭𝐢𝐜_ : (f g : Hom-𝐎𝐩𝐭𝐢𝐜 A B) -> 𝒰 𝑖 where
      switch : ∀{M N : ⟨ 𝒞 ⟩} -> ∀{l r} -> (s : M ⟶ N)
               -> ((l ◆ (s ⇃⊗⇂ id) , r) ∼-Hom-𝐎𝐩𝐭𝐢𝐜 (l , (s ⇃⊗⇂ id) ◆ r))

      -- constructor _,_
      -- field iparam : Opticm g ≅ Opticm f
      -- field arr : (id ⇃⊗⇂ ⟨ iparam ⟩) ◆ ⟨ f ⟩ ∼ ⟨ g ⟩




