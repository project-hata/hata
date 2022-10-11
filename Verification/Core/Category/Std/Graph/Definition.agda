
module Verification.Core.Category.Std.Graph.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Setoid

open import Verification.Conventions.Meta.Term

record isGraph {𝑗 𝑖} (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
  constructor graph
  field Edge : A -> A -> 𝒰 𝑗

open isGraph {{...}} public

Graph : ∀ (𝑖 : 𝔏 ^ 2) -> 𝒰 _
Graph 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isGraph {𝑖 ⌄ 1}


record GraphSetoid (G : Graph 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  constructor incl
  field ⟨_⟩ : ⟨ G ⟩

open GraphSetoid public

data RST (G : Graph 𝑖) : (a b : GraphSetoid G) -> 𝒰 𝑖 where
  incl : ∀{a b} -> Edge ⟨ a ⟩ ⟨ b ⟩ -> RST G a b
  refl-RST : ∀{a} -> RST G a a
  sym-RST : ∀{a b} -> RST G a b -> RST G b a
  trans-RST : ∀{a b c} -> RST G a b -> RST G b c -> RST G a c

instance
  isSetoid:RST : ∀{G : Graph 𝑖} -> isSetoid (GraphSetoid G)
  isSetoid:RST {G = G} = isSetoid:byDef (RST G) (refl-RST) sym-RST trans-RST


Graph→Setoid : Graph 𝑖 -> Setoid _
Graph→Setoid G = GraphSetoid G since it

instance Register:Graph→Setoid = register₁[ "" , 𝑖 ] Graph→Setoid {𝑖}


private macro
  F'''' = instance[ "" , 𝑖 ] (Graph 𝑖 -> Setoid _) ◀





