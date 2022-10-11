
module Verification.Core.Category.Std.Category.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition

--------------------------------------------------------------------------------
-- Basic definitions

-- We define categories, functors and natural transformations.

--------------------------------------------------------------------------------
--  Categories

-- We define categories using hom-setoids as in "Proof_-relevant Category Theory in Agda"
-- (see: https://arxiv.org/pdf/2005.07059.pdf)
-- This is because this way we do not have to restrict ourselves to requiring the hom-types to be h-sets,
-- and can work mostly without doing truncations / requiring a certain hLevel.
--
-- (Problems would happen in slice categories and categories of_ cones, where equations become part of_ our morphisms)
--
-- We also copy other 'tricks' of_ them, as, e.g. requiring left and right associativity proof_s, and an id ◆ id ∼ id proof_.

-- [Hide]
record Hom-Base {𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} (Hom : A -> A -> 𝒰 𝑗) (a : A) (b : A) : 𝒰 (𝑗) where
  constructor incl
  field ⟨_⟩ : Hom a b
  -- incl : R a b -> Hom-Base R a b -- a ∼[ R ] b
open Hom-Base public

-- //

-- [Definition]
-- | Given a type $𝒞$, whose elements we are going to call /objects/, we say that it has the structure of a category [...] if
--   the following additional data is given:
record isCategory {𝑗 : 𝔏 ^ 2} {𝑖 : 𝔏} (𝒞 : 𝒰 𝑖) : 𝒰 ((𝑖 ⌄ 0) ⊔ 𝑗 ⁺) where
  constructor category
  infixl 50 _◆_ _◈_

-- | 1. A type family [..], assigning to every pair of objects |a b : 𝒞|
--      a type of /homomorphisms/ |Hom a b| between them.
--      We call elements of this type also simply /morphisms/ or /arrows/.
  field Hom : 𝒞 -> 𝒞 -> 𝒰 (𝑗 ⌄ 0)

  -- Hom : 𝒞 -> 𝒞 -> 𝒰 (𝑗 ⌄ 0)
  -- Hom a b = Hom-Base Hom' a b
  field {{isSetoid:Hom}} : ∀{a b : 𝒞} -> isSetoid {𝑗 ⌄ 1} (Hom a b)

-- | 3. An operation [..], assigning to every object |a| an identity morphism on this object.
  field id : ∀{a : 𝒞} -> Hom a a

-- | 4. A composition operation [..], which allows us to compose morphisms whose domain and codomain are compatible.
        _◆_ : ∀{a b c : 𝒞} -> Hom a b -> Hom b c -> Hom a c

-- | 5. Proofs that |id| is a unit for composition.
        unit-l-◆          : ∀{a b : 𝒞} -> ∀{f : Hom a b} -> id ◆ f ∼ f
        unit-r-◆          : ∀{a b : 𝒞} -> ∀{f : Hom a b} -> f ◆ id ∼ f
        unit-2-◆          : ∀{a : 𝒞} -> id ◆ id ∼ id {a = a}
-- | 6. Proofs that composition is associative.
        assoc-l-◆         : ∀{a b c d : 𝒞} -> ∀{f : Hom a b} -> ∀{g : Hom b c} -> ∀{h : Hom c d} -> (f ◆ g) ◆ h ∼ f ◆ (g ◆ h)
        assoc-r-◆         : ∀{a b c d : 𝒞} -> ∀{f : Hom a b} -> ∀{g : Hom b c} -> ∀{h : Hom c d} -> f ◆ (g ◆ h) ∼ (f ◆ g) ◆ h
-- | 7. A proof that composition is compatible with the equivalence relation.
        _◈_               : ∀{a b c : 𝒞} -> ∀{f g : Hom a b} -> ∀{h i : Hom b c} -> f ∼ g -> h ∼ i -> f ◆ h ∼ g ◆ i

open isCategory ⦃...⦄ public

-- //


-- [Hide]
Category : (𝑗 : 𝔏 ^ 3) -> 𝒰 _
Category 𝑗 = 𝒰 (𝑗 ⌄ 0) :& isCategory {𝑗 ⌄ 1 ⋯ 2}
-- //


-- [Notation]
-- | We usually write |a ⟶ b| for |Hom a b|. Note, that this arrow
--   is longer than the arrow of Agda's function types.

-- //

-- [Hide]
module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} (a b : 𝒞) where
  infixr 40 _⟶ᵘ_ _⟶_
  _⟶ᵘ_ = Hom a b
  macro _⟶_ = #structureOn (Hom a b)

-- //


-- [Hide]

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  idOn : (a : 𝒞) -> a ⟶ a
  idOn a = id


{-
-- module _ {C : 𝒰 _} {{_ : Category 𝑖 on C}} where
--   instance
--     hasU:Hom : ∀{a b : C} -> hasU (Hom a b) _ _
--     hasU:Hom = hasU:Base _

isSetoid:Hom-Base : {A : 𝒰 𝑖} {Hom : A -> A -> 𝒰 𝑗} -> ∀{a b}
                    -> {{_ : isSetoid 𝑘 (Hom a b)}}
                    -> isSetoid _ (Hom-Base Hom a b)
isSetoid._∼'_ (isSetoid:Hom-Base {{P}}) f g = _∼'_ {{P}} ⟨ f ⟩ ⟨ g ⟩
isSetoid.isEquivRel:∼ isSetoid:Hom-Base = {!!}

-- a[Hide]
-- a| A small category is one where all objects, arrows, and equivalence relations live in $𝒰₀$
-- aSmallCategory = Category (ℓ₀ , ℓ₀ , ℓ₀)
-- aISmallCategory : (𝒞 : 𝒰₀) -> 𝒰₁
-- aISmallCategory 𝒞 = isCategory (ℓ₀ , ℓ₀) 𝒞
-- a//
-}

record Hom' {𝒞 : Category 𝑖} (a b : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ⌄ 1) where
  constructor hom
  field ⟨_⟩ : a ⟶ b

open Hom' public

instance
  hasU:Hom' : ∀{𝒞 : 𝒰 _} {{_ : Category 𝑖 on 𝒞}} {a b : 𝒞} -> hasU (Hom' {𝒞 = ′ 𝒞 ′}a b) _ _
  hasU:Hom' {𝒞 = 𝒞} {a} {b} = record
               { getU = a ⟶ b
               ; getP = const 𝟙-𝒰
               ; reconstruct = λ x -> hom (fst x)
               ; destructEl = ⟨_⟩
               ; destructP = const tt
               }


record Obj (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  constructor obj
  field ⟨_⟩ : ⟨ 𝒞 ⟩

open Obj public

instance
  hasU:Obj : ∀{𝒞 : Category 𝑖} -> hasU (Obj 𝒞) _ _
  hasU:Obj {𝒞 = 𝒞} = record
               { getU = ⟨ 𝒞 ⟩
               ; getP = const 𝟙-𝒰
               ; reconstruct = λ x -> obj (fst x)
               ; destructEl = ⟨_⟩
               ; destructP = const tt
               }


module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory {𝑖} 𝒞}} where
  HomPair : (a b : 𝒞) -> 𝒰 _
  HomPair a x = Hom a x ×-𝒰 Hom a x

  data isId : ∀{a b : 𝒞} (f : a ⟶ b) -> 𝒰 (𝑖 ､ 𝑗) where
    incl : ∀{a : 𝒞} {f : a ⟶ a} -> f ∼ id -> isId {a} {a} f



module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  _⟨_⟩-Hom_ : (x : 𝒞) {y : 𝒞} {z : 𝒞} → x ⟶ y → y ⟶ z → x ⟶ z
  _ ⟨ f ⟩-Hom g = f ◆ g

  ⟨⟩-Hom-syntax : (x : 𝒞) {y z : 𝒞} → x ⟶ y → y ⟶ z → x ⟶ z
  ⟨⟩-Hom-syntax = _⟨_⟩-Hom_
  infixr 2 ⟨⟩-Hom-syntax
  infixr 2 _⟨_⟩-Hom_

  infix  3 _∎-Hom

  _∎-Hom : (x : 𝒞) → x ⟶ x
  _ ∎-Hom = id


-- //


