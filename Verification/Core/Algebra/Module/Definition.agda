
module Verification.Core.Algebra.Module.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition


record isModule {𝑗 𝑖} (R : Ring 𝑖) (A : Abelian 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  infixr 70 _↷_
  field
    _↷_ : ⟨ R ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
    assoc-l-↷ : ∀{r s a} -> r ⋅ s ↷ a ∼ r ↷ s ↷ a
    zero-↷ : ∀{a} -> ◌ ↷ a ∼ ◌
    distr-l-↷ : ∀{r s a} -> (r ⋆ s) ↷ a ∼ r ↷ a ⋆ s ↷ a
    distr-r-↷ : ∀{r a b} -> r ↷ (a ⋆ b) ∼ r ↷ a ⋆ r ↷ b

open isModule {{...}} public

Module : Ring 𝑖 -> ∀ 𝑗 -> 𝒰 _
Module R 𝑗 = _ :& isModule {𝑗} R


module _ (R : Ring 𝑖) (A : Setoid 𝑗) where
  data Free-𝐌𝐨𝐝ᵘ : 𝒰 (𝑖 ､ 𝑗) where
    :◌ : Free-𝐌𝐨𝐝ᵘ
    _:⋅_ : ⟨ R ⟩ -> ⟨ A ⟩ -> Free-𝐌𝐨𝐝ᵘ
    _:⋆_ : Free-𝐌𝐨𝐝ᵘ -> Free-𝐌𝐨𝐝ᵘ -> Free-𝐌𝐨𝐝ᵘ

  macro Free-𝐌𝐨𝐝 = #structureOn Free-𝐌𝐨𝐝ᵘ

module _ (R : Ring 𝑖) (A : Setoid 𝑗) where
  data _∼-Free-𝐌𝐨𝐝_ : (m n : Free-𝐌𝐨𝐝 R A) -> 𝒰 (𝑖 ､ 𝑗) where
    :cong : ∀{r s a b} -> r ∼ s -> a ∼ b -> (r :⋅ a) ∼-Free-𝐌𝐨𝐝 (s :⋅ b)
    :assoc-l-:⋆ : ∀{m n o} -> ((m :⋆ n) :⋆ o) ∼-Free-𝐌𝐨𝐝 (m :⋆ (n :⋆ o))
    :unit-l-:⋆ : ∀{m} -> (:◌ :⋆ m) ∼-Free-𝐌𝐨𝐝 m
    :unit-r-:⋆ : ∀{m} -> (m :⋆ :◌) ∼-Free-𝐌𝐨𝐝 m
    :comm-:⋆ : ∀{m n} -> (m :⋆ n) ∼-Free-𝐌𝐨𝐝 (n :⋆ m)
    :distr-l : ∀{r s a} -> ((r ⋆ s) :⋅ a) ∼-Free-𝐌𝐨𝐝 ((r :⋅ a) :⋆ (s :⋅ a))


  instance
    isSetoid:Free-𝐌𝐨𝐝 : isSetoid (Free-𝐌𝐨𝐝 R A)
    isSetoid:Free-𝐌𝐨𝐝 = isSetoid:byFree _∼-Free-𝐌𝐨𝐝_


  instance
    isMonoid:Free-𝐌𝐨𝐝 : isMonoid (Free-𝐌𝐨𝐝 R A)
    isMonoid:Free-𝐌𝐨𝐝 = record
                          { _⋆_ = _:⋆_
                          ; ◌ = :◌
                          ; unit-l-⋆ = incl :unit-l-:⋆
                          ; unit-r-⋆ = incl :unit-r-:⋆
                          ; assoc-l-⋆ = incl :assoc-l-:⋆
                          ; _≀⋆≀_ = {!λ p q -> incl (:cong ? ?)!}
                          }

