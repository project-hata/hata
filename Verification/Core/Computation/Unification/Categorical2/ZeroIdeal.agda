
module Verification.Core.Computation.Unification.Categorical2.ZeroIdeal where

open import Verification.Conventions
open import Verification.Core.Setoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition
open import Verification.Core.Computation.Unification.Categorical2.Ideal


-- ===* The zero ideal
-- | Remember that the ideals we are interested in
--   are formed as "set of arrows which unify |t| and |s|",
--   for two terms |t| and |s|. Now if these terms
--   do not have a unifier in |𝐒𝐮𝐛𝐬𝐭-FO|, then
--   they still have a unifier in |Free-𝐙𝐌𝐂𝐚𝐭 𝐒𝐮𝐛𝐬𝐭-FO|,
--   namely |0| itself.
--   Expressed more formally, we know that |(t ◆ pt) ∼ pt ∼ (s ◆ pt)| always holds.

-- [Definition]
-- | The ideal containing only |pt| is called the /zero ideal/
--   and is denoted by |⊥-Ideal|.

-- //

-- | This means that if |t| and |s| do not have a unifier,
--   the ideal generated by them is the zero ideal. We
--   can also show the following property of |⊥-Ideal|.

-- [Lemma]
-- | The ideal |⊥-Ideal| is a bottom element of the
--   preorder of ideals at any object |a| of |𝒞|.

-- //

-- [Proof]
-- | To show this, we merely must show that there is
--   a subset inclusion of |⊥-Ideal| into any other
--   ideal. But the |⊥-Ideal| only contains |pt|,
--   and by definition (evidenced by the
--   record field |ideal-pt|) every ideal contains |pt|.

-- //


-- [Hide]
module _ {𝒞 : 𝒰 𝑖}
         {{_ : isCategory {𝑗} 𝒞}}
         {{_ : isZeroMorphismCategory ′ 𝒞 ′}}
         where
  -- private
  --   𝒞 = ⟨ 𝒞' ⟩

-- module _ {𝑖} {𝒞 : 𝒰 _} {{_ : 𝐙𝐌𝐂𝐚𝐭 𝑖 on 𝒞}} where
  module _ {a : 𝒞} where
    record ⊥-Idealᵘ {b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor incl
      field ⟨_⟩ : f ∼ pt

    open ⊥-Idealᵘ public

    macro
      ⊥-Ideal = #structureOn (λ {b} -> ⊥-Idealᵘ {b})


    instance
      isIdeal:⊥-Ideal : isIdeal a ⊥-Idealᵘ
      isIdeal:⊥-Ideal = record
        { transp-Ideal = λ f∼g (incl f∼pt) → incl (f∼g ⁻¹ ∙ f∼pt)
        ; ideal-r-◆     = λ (incl f∼pt) g → incl ((f∼pt ◈ refl) ∙ absorb-l-◆)
        ; ideal-pt      = incl refl
        }

    initial-⊥-Ideal : ∀{I : Ideal a} -> ′ (λ {b} -> ⊥-Idealᵘ {b}) ′ ≤ I
    initial-⊥-Ideal = incl λ f (incl f∼pt) → transp-Ideal (f∼pt ⁻¹) ideal-pt

-- //

