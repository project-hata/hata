
module Verification.Core.Computation.Unification.Monoidic.PrincipalFamily where

open import Verification.Conventions

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Category.As.Monoid
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Subsetoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Computation.Unification.Definition
-- open import Verification.Core.Theory.Presentation.Signature.Definition


module _ (M : Monoid₀ (𝑖 , 𝑖)) where
  module _ (Good : Submonoid ′ ⟨ M ⟩ ′) {B I : 𝒰 𝑗} (𝒷 : B -> I) (𝓘 : I -> Ideal-r M) where

    record isSplittable (n : ℕ) (i : I) (P : I -> 𝒰₀) : 𝒰 (𝑗 ､ 𝑖 ⁺) where
      field fam : Fin-R n -> I
      field covers : ⋀-fin (λ i -> 𝓘 (fam i)) ∼ 𝓘 i
      field famprops : ∀ k -> P (fam k)
    open isSplittable public

    record isPrincipalFamily : 𝒰 (𝑗 ､ 𝑖 ⁺) where
      field Size : WFT (ℓ₀ , ℓ₀)
      -- field Size : 𝒰₀
      field size : I -> ⟨ Size ⟩
      -- field _≪_ : Size -> Size -> 𝒰₀
      -- field isWellFounded:Size : WellFounded _≪_
      -- field trans-Size : ∀{a b c} -> a ≪ b -> b ≪ c -> a ≪ c
      field _⁻¹*_ : ⦋ ⟨ Good ⟩ ⦌ -> I -> I
      field size:⁻¹* : ∀ g i -> (size (g ⁻¹* i) ≡-Str size i) +-𝒰 (size (g ⁻¹* i) ≪ size i)
      field preserves-𝓘:⁻¹* : ∀ {g i} -> 𝓘 (g ⁻¹* i) ∼ (⟨ g ⟩ ⁻¹↷-Ide (𝓘 i))
      -- field 𝓘 : Idx -> Ideal-r M
      field ∂ : (i : I) -> (∑ λ b -> 𝓘 (𝒷 b) ∼ 𝓘 i) +-𝒰 (∑ λ n -> isSplittable n i (λ j -> size j ≪ size i))
      field principalBase : ∀ b -> isPrincipal/⁺-r Good (𝓘 (𝒷 b))


  open isPrincipalFamily {{...}} public

  module _ (Good : Submonoid ′ ⟨ M ⟩ ′) {B I : 𝒰 𝑗} (𝒷 : B -> I) (𝓘 : I -> Ideal-r M) {{PF : isPrincipalFamily Good 𝒷 𝓘}} {{_ : zeroIsDecidable M}} where

    private
      P : (s : ⟨ Size ⟩) -> 𝒰 _
      P s = ∀ i -> size i ≡-Str s -> isPrincipal/⁺-r Good (𝓘 i)

      lem-40 : ∀ {U V : Ideal-r M} -> (PU : isPrincipal/⁺-r Good U) -> isPrincipal/⁺-r Good (rep' U ⁻¹↷-Ide V) -> isPrincipal/⁺-r Good (V ∧ U)
      lem-40 {U} {V} PU PV =
        let u : ⟨ M ⟩
            u = rep' U

            V' = u ⁻¹↷-Ide V

            v : ⟨ M ⟩
            v = rep' V'
            P₈ : (V ∧ U) ∼ (u ⋆ v) ↷ ⊤
            P₈ = V ∧ U                                          ⟨ refl ≀∧≀ (principal-r) ⟩-∼
                 V ∧ (u ↷ ⊤)                                   ⟨ refl ≀∧≀ idem-∧ ⁻¹ ⟩-∼
                 V ∧ ((u ↷ ⊤) ∧ (u ↷ ⊤))                      ⟨ assoc-r-∧ ⟩-∼
                 (V ∧ (u ↷ ⊤)) ∧ (u ↷ ⊤)                      ⟨ inv-↷Ide-r ⁻¹ ≀∧≀ refl ⟩-∼
                 (u ↷ (u ⁻¹↷-Ide V)) ∧ (u ↷ ⊤)                 ⟨ distr-↷-∧-Ide (zeroOrCancel-r {{_:>_.Proof2> PU}}) ⁻¹ ⟩-∼
                 (u ↷ ((u ⁻¹↷-Ide V) ∧ ⊤))                      ⟨ refl ≀↷≀ unit-r-∧ ⟩-∼
                 (u ↷ ((u ⁻¹↷-Ide V)))                           ⟨ refl ≀↷≀ (principal-r)  ⟩-∼
                 -- (u ↷ (v ↷ ⊤))                                   ⟨ assoc-l-↷ {A = Ideal-r ′ ⟨ M ⟩ ′ since isSetoid:Ideal-r} {m = u} {n = v} {a = ⊤} ⁻¹ ⟩-∼
                 {-(u ↷ (v ↷ ⊤)) -} _                                 ⟨ {!!} ⟩-∼
                 (u ⋆ v) ↷ (⊤ since isIdeal-r:⊤)   ∎
            instance
              P₉ : isPrincipal-r (V ∧ U)
              P₉ = record { rep = u ⋆ v ; principal-r = P₈ }
            instance
              P₁₀ : isPrincipal⁺-r Good ′ ⟨ V ∧ U ⟩ ′
              P₁₀ = record
                    { zeroOrCancel-r = (closed-⋆-ZeroOrCancel-r  (zeroOrCancel-r {{_:>_.Proof2> PU}}) (zeroOrCancel-r {{_:>_.Proof2> PV}}))
                    ; isGood = closed-⋆ (isGood {{_:>_.Proof2> PU}}) (isGood {{_:>_.Proof2> PV}})
                    }
        in it

      lem-45 : ∀{n} -> (F : Fin-R n -> I) -> (∀ i -> ∀ (g : ⦋ ⟨ Good ⟩ ⦌) -> isPrincipal/⁺-r Good (𝓘 (g ⁻¹* F (i)))) -> isPrincipal/⁺-r Good (⋀-fin (𝓘 ∣ F))
      lem-45 {zero} F FP = it
      lem-45 {suc n} F FP =
        let
            P₀ : isPrincipal/⁺-r Good (⋀-fin (𝓘 ∣ (F ∣ suc)))
            P₀ = (lem-45 (F ∣ suc) (FP ∣ suc))

            r : ⟨ M ⟩
            r = rep' (⋀-fin (𝓘 ∣ (F ∣ suc))) {{_:>_.Proof1> P₀}}

            rr : ⦋ ⟨ Good ⟩ ⦌
            rr = r ∢ isGood {{_:>_.Proof2> P₀}}

            P₁ : isPrincipal/⁺-r Good (𝓘 (rr ⁻¹* F zero))
            P₁ = FP zero rr
            P₂ : isPrincipal/⁺-r Good (⟨ rr ⟩ ⁻¹↷-Ide 𝓘 (F zero))
            P₂ = transp-isPrincipal/⁺-r preserves-𝓘:⁻¹* P₁
        in lem-40 P₀ P₂

      lem-50 : ∀ s -> (∀ t -> t ≪ s -> P t) -> P s
      lem-50 s IH k refl-StrId with ∂ k
      ... | left (b , P) = let P₀ = principalBase b
                           in transp-isPrincipal/⁺-r P P₀
      ... | just (n , Split) =
        let P₀ : ∀ i -> ∀(g : ⦋ ⟨ Good ⟩ ⦌) -> isPrincipal/⁺-r Good (𝓘 (g ⁻¹* Split .fam i))
            P₀ i g = case size:⁻¹* g (fam Split i) of
                       (λ p ->
                          let Q₀ : size (fam Split i) ≪ size k
                              Q₀ = Split .famprops i
                              Q₁ : size (g ⁻¹* fam Split i) ≪ size k
                              Q₁ = transport-Str (cong-Str (λ ξ -> ξ ≪ size k) (sym-≣ p)) Q₀
                          in IH (size (g ⁻¹* Split .fam i)) Q₁ (g ⁻¹* fam Split i) refl-≣
                       )
                       (λ p ->
                          let Q₀ : size (fam Split i) ≪ size k
                              Q₀ = Split .famprops i
                              Q₁ : size (g ⁻¹* fam Split i) ≪ size k
                              Q₁ = p ⟡-≪ Q₀
                          in IH (size (g ⁻¹* Split .fam i)) Q₁ (g ⁻¹* fam Split i) refl-≣
                       )
            P₁ = lem-45 (Split .fam) P₀
        in transp-isPrincipal/⁺-r (Split .covers) P₁


    isPrincipal:Family : ∀ s -> P s
    isPrincipal:Family = WFI.induction wellFounded lem-50









