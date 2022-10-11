
module Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.Category where

open import Verification.Conventions
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Imports
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Definition


module _ {𝒞 : DCLC 𝑖} where
  record Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 (a b : DisjointPair 𝒞) : 𝒰 𝑖 where
    constructor _,_
    field fst : fst a ⟶ fst b
    field snd : snd b ⟶ snd a

  open Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 public

  module _ {a b : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞} where
    instance
      isSetoid:Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : isSetoid (Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 a b)
      isSetoid:Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = isSetoid:byCodiscrete {𝑗 = ℓ₀}

  id-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 : ∀{a : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞} -> Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 a a
  id-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 = id , id

  _◆-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_ : ∀{a b c : 𝐃𝐢𝐬𝐏𝐚𝐢𝐫 𝒞} -> Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 a b -> Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 b c -> Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫 a c
  _◆-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_ (f , fʳ) (g , gʳ) = f ◆ g , gʳ ◆ fʳ

  instance
    isCategory:DisjointPair : isCategory (DisjointPair 𝒞)
    isCategory.Hom isCategory:DisjointPair = Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
    isCategory.isSetoid:Hom isCategory:DisjointPair = isSetoid:Hom-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
    isCategory.id isCategory:DisjointPair = id-𝐃𝐢𝐬𝐏𝐚𝐢𝐫
    isCategory._◆_ isCategory:DisjointPair = _◆-𝐃𝐢𝐬𝐏𝐚𝐢𝐫_
    isCategory.unit-l-◆ isCategory:DisjointPair = tt
    isCategory.unit-r-◆ isCategory:DisjointPair = tt
    isCategory.unit-2-◆ isCategory:DisjointPair = tt
    isCategory.assoc-l-◆ isCategory:DisjointPair = tt
    isCategory.assoc-r-◆ isCategory:DisjointPair = tt
    isCategory._◈_ isCategory:DisjointPair = λ x x₁ → tt

