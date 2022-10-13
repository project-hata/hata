
--
-- WIP for 旗/Core
--
-- Real numbers as a locale.
--
-- This file is not original research, it is mostly going to be
-- an implementation of https://ncatlab.org/nlab/show/locale+of+real+numbers.
--

module Verification.Workspace.Real.Variant.Locale.Definition where

open import Verification.Conventions



-- definitions for axiomatizing the rational numbers
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Algebra.Group.Definition
-- open import Verification.Core.Algebra.Group.Quotient
-- open import Verification.Core.Algebra.Abelian.Definition
-- open import Verification.Core.Algebra.Ring.Definition
-- open import Verification.Core.Algebra.Ring.Domain
-- open import Verification.Core.Algebra.Ring.Ordered
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

open import Verification.Core.Category.Std.Category.Definition
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



--
-- We abstract over the notion of rational number, to allow
-- for external implementations.
--

-- record isRational (Q : OrderedRing 𝑖) : 𝒰 𝑖 where
--   -- field {{isOrderedRing:this}} : isOrderedRing Q

-- module _ (𝑖 : 𝔏) where
--   Rational = OrderedRing (𝑖 , 𝑖 , 𝑖) :& isRational

--
-- The definition of opens.
--
module _ {𝑖 : 𝔏} {Q : OrderedRing (𝑖 , 𝑖 , 𝑖)} where
  macro ℚ = #structureOn ⟨ Q ⟩

  _ = LinearAsTotal.isTotal:Linear {𝑗 = 𝑖} {A = ℚ} {{it}}


  record isOpen (U : 𝒫 (ℚ ×-𝐒𝐭𝐝 ℚ)) : 𝒰 𝑖 where
    field O1 : ∀{a b : ℚ} -> a ≮ b -> (a , b) ∈ U
    field O2 : ∀{a b c d : ℚ} -> a ≮ b -> (b , c) ∈ U -> c ≮ d -> (a , d) ∈ U
    field O3 : ∀{a b c d : ℚ} -> (a , b) ∈ U -> c < b -> (c , d) ∈ U -> (a , d) ∈ U
    field O4 : ∀{a d : ℚ} -> (∀{b c : ℚ} -> a < b -> c < d -> (b , c) ∈ U) -> (a , d) ∈ U

  open isOpen {{...}} public

  Opens = ∑ isOpen

{-

  -- data Open : ℚ -> ℚ -> 𝒰 𝑖 where
  --   O1 : ∀{a b : ℚ} -> a ≮ b -> Open a b
  --   O2 : ∀{a b c d} -> a ≮ b -> b ∼ c -> c ≮ d -> Open a d
  --   O3 : ∀{a b c d} -> a ∼ b -> c < b -> c ∼ d -> Open a d
  --   O4 : ∀{a d} -> (∀{b c} -> a < b -> c < d -> Open b c) -> Open a d


  -- record Opens : 𝒰 𝑖 where
  --   constructor _,_because_
  --   field fst : ℚ
  --   field snd : ℚ
  --   field op : Open fst snd

-}





  ι-Opens : Opens -> 𝒫 (ℚ × ℚ)
  ι-Opens = fst


  open import Verification.Core.Category.Std.Category.Subcategory.Full

  ℝᵘ : 𝒰 _
  ℝᵘ = 𝐅𝐮𝐥𝐥 (𝒫 (ℚ × ℚ)) ι-Opens

  macro ℝ = #structureOn ℝᵘ

  --
  -- now we show that Op has various limits.
  --
  ⊤-ℝ : ℝ
  ⊤-ℝ = incl (⊤ , P)
    where
      P : isOpen ⊤
      P = record
          { O1 = λ x → tt
          ; O2 = λ x x₁ x₂ → tt
          ; O3 = λ x x₁ x₂ → tt
          ; O4 = λ x → tt
          }

  instance
    isTerminal:⊤-ℝ : isTerminal ⊤-ℝ
    isTerminal:⊤-ℝ = record { intro-⊤ = incl intro-⊤ ; expand-⊤ = incl tt }

  _⊓-ℝ_ : ℝ -> ℝ -> ℝ
  _⊓-ℝ_ G H = incl (fst ⟨ G ⟩ ⊓ fst ⟨ H ⟩ , P)
    where
      instance _ = snd ⟨ G ⟩
      instance _ = snd ⟨ H ⟩
      GH = (fst ⟨ G ⟩ ⊓ fst ⟨ H ⟩)

      P : isOpen GH
      P = record
        { O1 = λ {a b : ℚ} (p : a ≮ b) -> (O1 p) , (O1 p)
        ; O2 = λ {a b c d : ℚ} (p : a ≮ b) (q : (b , c) ∈ GH) (r : c ≮ d) -> O2 p (fst q) r , O2 p (snd q) r
        ; O3 = λ p q r -> O3 (fst p) q (fst r) , O3 (snd p) q (snd r)
        ; O4 = λ F -> O4 (λ p q -> fst (F p q)) , O4 λ p q -> snd (F p q)
        }

  ⊥-ℝ : ℝ
  ⊥-ℝ = incl (X since isSubsetoid:X , {!!})
    where
      X : ℚ × ℚ -> Prop _
      X (a , b) = ∣ a ≮ b ∣

      P : {a b : ⟨ Q ⟩ ×-𝒰 ⟨ Q ⟩} → (a ∼ b) -> a ∈ X -> b ∈ X
      P {(a , b)} {(x , y)} (p , q) r s = r (transp-< (sym p) (sym q) s)

      instance
        isSubsetoid:X : isSubsetoid X
        isSubsetoid:X = record { transp-Subsetoid = P }


      isOpen:X : isOpen ′ X ′
      isOpen:X = record
        { O1 = λ a≮b → a≮b
        ; O2 = λ a≮b b≮c c≮d -> c≮d ⟡ b≮c ⟡ a≮b
        ; O3 = λ {a} {b} {c} {d} a≮b c<b c≮d a<d -> case compare-< a<d b of a≮b λ b<d -> c≮d (c<b ∙-< b<d)
        ; O4 = λ {a} {d} F a<d ->
                 let c : ℚ
                     c = {!!}
                     c' : ℚ
                     c' = {!!}
                     p : a < c
                     p = {!!}
                     q : c' < d
                     q = {!!}
                     r : c < c'
                     r = {!!}
                 in F p q r
        }

        -- record { transp-Subsetoid = λ {(a , b) (x , y) : ℚ × ℚ } -> {!!} }
  -- module _ (G H : ℝ) where




