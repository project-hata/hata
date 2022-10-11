
module Verification.Core.Category.Std.Category.As.Monoid.Coequalizer where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Special
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.As.Monoid.Definition
open import Verification.Core.Category.Std.Category.As.Monoid.Special
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer

module _ {M : 𝒰 _} {{_ : Monoid (𝑖 , 𝑖) on M}} where
  -- MonEqᵣ : M -> M -> M -> Prop _
  -- MonEqᵣ a b x = ∣ a ⋆ x ∼ b ⋆ x ∣

  record MonEqᵣᵘ (f g h : M) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : f ⋆ h ∼ g ⋆ h
  open MonEqᵣᵘ public

  -- MonEqᵣ' : (f g : M) -> (M -> Prop _)
  -- MonEqᵣ' f g = λ h -> ∣ MonEqᵣᵘ f g h ∣

  module _ (f g : M) where
    MonEqᵣ' : M -> Prop _
    MonEqᵣ' h = ∣ MonEqᵣᵘ f g h ∣

    macro MonEqᵣ = #structureOn MonEqᵣ'


  module _ {f g : M} where
    instance
      isSubsetoid:MonEqᵣ : isSubsetoid (MonEqᵣ f g)
      isSubsetoid.transp-Subsetoid isSubsetoid:MonEqᵣ p (incl P) = incl ((refl ≀⋆≀ p ⁻¹) ∙ P ∙ (refl ≀⋆≀ p))

module _ {M : 𝒰 _} {{_ : Monoid₀ (𝑖 , 𝑖) on M}} where
  module _ {f g : M} where
    instance
      isIdeal:MonEqᵣ : isIdeal ′ M ′ (MonEqᵣ f g)
      isIdeal.ideal-r-⋆ isIdeal:MonEqᵣ {h} (incl P) i =
        let P₀ : f ⋆ (h ⋆ i) ∼ g ⋆ (h ⋆ i)
            P₀ = f ⋆ (h ⋆ i)   ⟨ assoc-r-⋆ ⟩-∼
                  (f ⋆ h) ⋆ i   ⟨ P ≀⋆≀ refl ⟩-∼
                  (g ⋆ h) ⋆ i   ⟨ assoc-l-⋆ ⟩-∼
                  g ⋆ (h ⋆ i)   ∎
        in incl P₀
      isIdeal.ideal-◍ isIdeal:MonEqᵣ = incl (absorb-r-⋆ ∙ absorb-r-⋆ ⁻¹)


module _ {𝒞 : Category 𝑖} {{_ : isSizedCategory 𝒞}} where
  asIdeal : ∀{a b : ⟨ 𝒞 ⟩} -> HomPair a b -> Ideal (𝖯𝖺𝗍𝗁𝖬𝗈𝗇 𝒞)
  asIdeal (f , g) = MonEqᵣ (arrow f) (arrow g)

  module _ {a b : ⟨ 𝒞 ⟩} where
    private
      lem-1 : {p : HomPair a b} -> {h : 𝖯𝖺𝗍𝗁𝖬𝗈𝗇 𝒞} -> h ∈ asIdeal p -> (h ∼ ◍) +-𝒰 hasCoequalizerCandidate p
      lem-1 {f , g} {[]} hP = left []
      lem-1 {f , g} {idp} (incl hP) = right (b since P₁)
        where
          P₀ : f ◆ id ∼ g ◆ id
          P₀ = PathMon-arrow-path-inv _ _ refl-≣ refl-≣ hP ◈ refl

          P₁ = record { π₌? = id ; equate-π₌? = P₀ }

      lem-1 {f , g} {arrow {x} {y} h} (incl hP) = {!!}

      -- right ({!!} since {!!})



    -- Forward : {f : HomPair a b} -> hasSizedCoequalizerDecision f -> isSpecialEpiPrincipalᵣ (asIdeal f)
    -- Forward {f , g} (left x) = lem-11
    --   where
    --     lem-10 : asIdeal (f , g) ∼ ⊥-Ideal
    --     lem-10 = antisym P Q
    --       where
    --         P : asIdeal (f , g) ≤ ⊥-Ideal
    --         ⟨ P a ⟩ (incl h) = {!!}

    --         Q : ⊥-Ideal ≤ asIdeal (f , g)
    --         Q = initial-⊥-Ideal {I = asIdeal (f , g)}

    --     lem-11 = transp-isSpecialEpiPrincipalᵣ (lem-10 ⁻¹) it

    -- Forward (just x) = {!!}




-- module _ {M : 𝒰 𝑖} {{_ : Monoid₀ (𝑖 , 𝑖) on M}} where

--   record MonEqᵣ' (f g h : M) : 𝒰 𝑖 where
--     constructor incl
--     field ⟨_⟩ : f ⋆ h ∼ g ⋆ h
--   open MonEqᵣ' public

--   MonEqᵣ : (f g : M) -> 𝒫 M
--   MonEqᵣ f g = λ h -> ∣ MonEqᵣ' f g h ∣

-- module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
--   record hasProperty-isCoeq {a b x : 𝒞} (f : (a ⟶ b) ^ 2) (h : b ⟶ x) : 𝒰 (𝑖 ､ 𝑗) where
--     constructor incl
--     field ⟨_⟩ : fst f ◆ h ∼ snd f ◆ h

-- module _ {M : Monoid₀ (𝑖 , 𝑖)} {f g : ⟨ M ⟩} where
--   instance
--     isSubsetoid:MonEqᵣ : isSubsetoid (MonEqᵣ f g)
--     isSubsetoid.transp-Subsetoid isSubsetoid:MonEqᵣ (p) (incl P) = incl ((refl ≀⋆≀ p ⁻¹) ∙ P ∙ (refl ≀⋆≀ p))

--   instance
--     isIdeal:MonEqᵣ : isIdeal M ′(MonEqᵣ f g)′
--     isIdeal.ideal-r-⋆ isIdeal:MonEqᵣ {h} (incl P) i =
--       let P₀ : f ⋆ (h ⋆ i) ∼ g ⋆ (h ⋆ i)
--           P₀ = f ⋆ (h ⋆ i)   ⟨ assoc-r-⋆ ⟩-∼
--                 (f ⋆ h) ⋆ i   ⟨ P ≀⋆≀ refl ⟩-∼
--                 (g ⋆ h) ⋆ i   ⟨ assoc-l-⋆ ⟩-∼
--                 g ⋆ (h ⋆ i)   ∎
--       in incl P₀
--     isIdeal.ideal-◍ isIdeal:MonEqᵣ = incl (absorb-r-⋆ ∙ absorb-r-⋆ ⁻¹)





-- module _ {𝒞 : Category 𝑖} where
--   module _ (a b : ⟨ 𝒞 ⟩) (f g : a ⟶ b) where




--     -- lem-10 : Unification f g -> isEpiPrincipal (MonCoequalizing f g)
--     -- lem-10 = {!!}

--     -- lem-20 : isEpiPrincipal (MonCoequalizing (arrow f) (arrow g)) -> Unification f g
--     -- lem-20 = {!!}



