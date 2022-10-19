
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

record isRational (Q : OrderedRing' 𝑖) : 𝒰 𝑖 where

  private instance
    _ : isOrderedRing _ _
    _ = isnd Q

    _ : isRing _
    _ = (isnd (ifst Q))

    _ : isCommutative _
    _ = Proof2, (isnd (ifst (ifst Q)))

    _ : isMonoid _
    _ = isnd (ifst (ifst (ifst Q)))

    _ : isSetoid _
    _ = isnd (ifst (ifst (ifst (ifst Q))))

  field {{isDense:This}} : isDense ′ El Q ′

module _ 𝑖 where
  Rational' = OrderedRing' 𝑖 :&' isRational

record isRational# {𝑗 : 𝔏 ^ 3} (This : 𝒰 (𝑗 ⌄ 0)) : 𝒰 (𝑗 ⁺) where
  instance constructor makeIsRational#
  field {{isSetoid:This}} : isSetoid {𝑗 ⌄ 1} This
  field {{isMonoid:This}} : isMonoid (make:&' This isSetoid:This)
  field {{isGroup:This}}  : isGroup (make:&' (make:&' This isSetoid:This) isMonoid:This)
  field {{isCommutative:This}}  : isCommutative ((make:&' (make:&' This isSetoid:This) isMonoid:This))
  field {{isRing:This}}    : isRing (make:&' ((make:&' (make:&' This isSetoid:This) isMonoid:This)) (make, isGroup:This isCommutative:This))
  field {{isOrderedRing:This}}    : isOrderedRing (𝑗 ⌄ 2) (make:&' (make:&' ((make:&' (make:&' This isSetoid:This) isMonoid:This)) (make, isGroup:This isCommutative:This)) isRing:This)
  field {{isRational:This}} : isRational (make:&' ((make:&' (make:&' ((make:&' (make:&' This isSetoid:This) isMonoid:This)) (make, isGroup:This isCommutative:This)) isRing:This)) isOrderedRing:This)

open isRational# public

module _ 𝑖 where
  Rational = _ :& isRational# {𝑖}

--
-- The definition of opens.
--
module _ {𝑖 : 𝔏} {Q : Rational (𝑖 , 𝑖 , 𝑖)} where
  macro ℚ = #structureOn ⟨ Q ⟩

  _ = LinearAsTotal.isTotal:Linear {𝑗 = 𝑖} {A = ℚ} {{it}}


  record isOpen (U : 𝒫 (ℚ ×-𝐒𝐭𝐝 ℚ)) : 𝒰 𝑖 where
    field O1 : ∀{a b : ℚ} -> a ≮ b -> (a , b) ∈ U
    field O2 : ∀{a b c d : ℚ} -> a ≮ b -> (b , c) ∈ U -> c ≮ d -> (a , d) ∈ U
    field O3 : ∀{a b c d : ℚ} -> (a , b) ∈ U -> c < b -> (c , d) ∈ U -> (a , d) ∈ U
    field O4 : ∀{a d : ℚ} -> (∀{b c : ℚ} -> a < b -> c < d -> (b , c) ∈ U) -> (a , d) ∈ U

  open isOpen {{...}} public

  Opens = ∑ isOpen


  ι-Opens : Opens -> 𝒫 (ℚ × ℚ)
  ι-Opens = fst


  open import Verification.Core.Category.Std.Category.Subcategory.Full

  ℝᵘ : 𝒰 _
  ℝᵘ = 𝐅𝐮𝐥𝐥 (𝒫 (ℚ × ℚ)) ι-Opens

  macro ℝ = #structureOn ℝᵘ

  --
  -- Zigzags and the zigzag lemma
  --
  data Zigzag {I : 𝒰₀} (F : I -> Opens) : (a b : ℚ) -> 𝒰 𝑖 where
    zig : ∀{a b} -> ∀ i -> (a , b) ∈ fst (F i) -> Zigzag F a b
    zagzig : ∀{a b} -> Zigzag F a b -> ∀{a₁ b₁} -> a₁ < b -> ∀ i -> (a₁ , b₁) ∈ fst (F i) -> Zigzag F a b₁

  module Zigzag-Proof-1 where
    --
    -- We can make a zigzag shorter at the end.
    --
    lem-1 : ∀{I} {F : I -> Opens} {a b c} -> Zigzag F a b -> b ≮ c -> Zigzag F a c
    lem-1 {F = F} {a = a} {b} {c} (zig i x) b≮c = zig i (O2 {{snd (F i)}} (reflexive {a = a}) x b≮c)
    lem-1 {F = F} {a = a} {b₁} {c} (zagzig {_} {b} z {a₁} {.b₁} a₁<b i zag) b₁≮c with compare-< a₁<b c
    ... | left a₁<c = lem-1 z {!!}
    ... | just c<b = zagzig z c<b i (O1 {{snd (F i)}} irrefl-<)

  --
  -- now we show that Op has various limits.
  --

  module Compute-⊔-ℝ (U V : ℝ) where
    instance _ = snd ⟨ U ⟩
    instance _ = snd ⟨ V ⟩

    F : Bool -> Opens
    F true = ⟨ U ⟩
    F false = ⟨ V ⟩

    Wᵘ : 𝒫-𝒰 (ℚ × ℚ)
    Wᵘ (a , b) = ∣ Zigzag F a b ∣

    macro W = #structureOn Wᵘ

    instance
      isSubsetoid:W : isSubsetoid W
      isSubsetoid:W = {!!}

    isOpen:W : isOpen W
    isOpen:W = record
      { O1 = λ a≮b → zig true (O1 a≮b)
      ; O2 = λ a≮b bc∈W c≮d -> zagzig (zig true (O1 a≮b)) {!!} {!!} {!!}
      ; O3 = {!!}
      ; O4 = {!!}
      }

    Return : ℝ
    Return = incl (W , {!!})


{-

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
  ⊥-ℝ = incl (X since isSubsetoid:X , isOpen:X)
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
                 let B = between a<d
                     b = ⟨ B ⟩
                     a<b = fst (Proof B)
                     b<d = snd (Proof B)

                     C = between b<d
                     c = ⟨ C ⟩
                     b<c = fst (Proof C)
                     c<d = snd (Proof C)
                 in F a<b c<d b<c
        }

-}






