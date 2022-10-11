
module Verification.Core.Data.Prop.Subset where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Prop.Instance.Setoid
open import Verification.Core.Data.Prop.Instance.Preorder
open import Verification.Core.Data.Prop.Instance.Lattice
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Preorder
open import Verification.Core.Data.Universe.Instance.Lattice
open import Verification.Core.Data.Sum.Definition


----------------------------------------------------------
-- Common operations

module _ {A B : 𝒰 𝑖} where
  pb-𝒫 : (A -> B) -> (B -> Prop 𝑖) -> (A -> Prop 𝑖)
  pb-𝒫 f P a = P (f a)

  instance
    isSetoidHom:pb-𝒫 : ∀{f : A -> B} -> isSetoidHom ′(B -> Prop 𝑖)′ ′(A -> Prop 𝑖)′ (pb-𝒫 f)
    isSetoidHom.cong-∼ isSetoidHom:pb-𝒫 {a = P} {b = Q} (x) = x

  instance
    isMonotone:pb-𝒫 : ∀{f : A -> B} -> isMonotone ′(B -> Prop 𝑖)′ ′(A -> Prop 𝑖)′ (′(pb-𝒫 f)′)
    isMonotone.monotone isMonotone:pb-𝒫 {a = P} {b = Q} (x) = {!!}

-- module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} where
--   instance
--     Notation-Restriction:pb-𝒫 : Notation-Restriction (B -> C) (A -> B) (λ _ _ -> A -> C)
--     Notation-Restriction._∣_ Notation-Restriction:pb-𝒫 P f = λ a -> P (f a)

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : B -> 𝒰 𝑘} where
  instance
    Notation-Restriction:pb-𝒫-dep2 : Notation-Restriction (∀(b : B) -> C b) (A -> B) (λ X Y -> ∀(a : A) -> C (Y a))
    Notation-Restriction._∣_ Notation-Restriction:pb-𝒫-dep2 P f = λ a -> P (f a)

  -- instance
  --   Notation-Restriction:pb-𝒫-Monotone : {p q : A -> Prop 𝑖} -> Notation-Restriction (p ≤ q) (A -> B) (A -> Prop 𝑖)
  --   Notation-Restriction._∣_ Notation-Restriction:pb-𝒫-Monotone P f = pb-𝒫 f P

----------------------------------------------------------
-- Decidable subsets


-- record 𝒫-Dec (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
--   constructor _,_
--   field ⟨_⟩ : A -> Prop 𝑖
--   field Proof : ∀ a -> Decision (Prop.⟨_⟩ (⟨_⟩ a))
-- open 𝒫-Dec public

record is𝒫-Dec {A : 𝒰 𝑖} (P : A -> Prop 𝑖) : 𝒰 (𝑖) where
  field decide-𝒫 : ∀ a -> (¬ ⟨ P a ⟩) +-𝒰 ⟨ P a ⟩
open is𝒫-Dec {{...}} public

𝒫-Dec : (A : 𝒰 𝑖) -> 𝒰 _
𝒫-Dec {𝑖} A = (A -> Prop 𝑖) :& is𝒫-Dec

-- module _ {A : 𝒰 𝑖} where
--   instance
--     isSetoid:𝒫-Dec :

module _ {A : 𝒰 𝑖} where
  instance
    is𝒫-Dec:∨ : {p q : A -> Prop 𝑖} {{_ : is𝒫-Dec p}} {{_ : is𝒫-Dec q}} -> is𝒫-Dec (p ∨ q)
    is𝒫-Dec.decide-𝒫 (is𝒫-Dec:∨ {p = p} {q}) a =
      let P₀ : (¬ ⟨ p a ⟩) +-𝒰 ⟨ p a ⟩
          P₀ = decide-𝒫 {P = p} a
          P₁ = decide-𝒫 {P = q} a
      in case P₀ of
              (λ ¬pa -> case P₁ of
                             (λ ¬qa -> left (either ¬pa ¬qa))
                             (λ qa -> right (right qa)))
              (λ pa -> right (left pa))

module _ {A B : 𝒰 𝑖} where
  private
    instance
      is𝒫-Dec:pb-𝒫 : ∀{f : A -> B} -> {P : B -> Prop 𝑖} -> {{_ : is𝒫-Dec P}} -> is𝒫-Dec (pb-𝒫 f P)
      is𝒫-Dec.decide-𝒫 (is𝒫-Dec:pb-𝒫 {f = f} {p} {{D}}) a =
        let P₀ : (¬ ⟨ p (f a) ⟩) +-𝒰 ⟨ p (f a) ⟩
            P₀ = decide-𝒫 {{D}} (f a)
        in P₀

  pb-𝒫-Dec : ∀(f : A -> B) -> (𝒫-Dec B) -> (𝒫-Dec A)
  ⟨ pb-𝒫-Dec f P ⟩ a = pb-𝒫 f ⟨ P ⟩ a
  _:&_.oldProof (pb-𝒫-Dec f P) = record {}
  _:&_.of (pb-𝒫-Dec f P) = is𝒫-Dec:pb-𝒫

  instance
    Notation-Restriction:pb-𝒫-Dec : Notation-Restriction (𝒫-Dec B) (A -> B) (λ _ _ -> 𝒫-Dec A)
    Notation-Restriction._∣_ Notation-Restriction:pb-𝒫-Dec P f = pb-𝒫-Dec f P


