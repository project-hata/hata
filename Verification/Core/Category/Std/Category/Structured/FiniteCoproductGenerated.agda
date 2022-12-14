
module Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated where

open import Verification.Conventions hiding (_โ_)
open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category
-- open import Verification.Core.Data.Indexed.Duplicate
-- open import Verification.Core.Data.Indexed.Definition
-- open import Verification.Core.Data.Indexed.Instance.Monoid
-- open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Data.List.Variant.Binary.Natural


-------------------------
-- Finite coproducts via category of functors

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid

module _ {๐ : Category ๐} {{_ : hasFiniteCoproducts ๐}} where

  โจแถ แต : โ{n : ไบบโ} -> ๐๐ฎ๐ง๐ [ n ]แถ  ๐ -> โจ ๐ โฉ
  โจแถ แต {incl x}   d = โจ d โฉ (member incl)
  โจแถ แต {a โ-โง b}  d = โจแถ แต (leftแถ  โ-๐๐๐ญ d) โ โจแถ แต (rightแถ  โ-๐๐๐ญ d)
  โจแถ แต {โ-โง}      d = โฅ

  -----------------------------------------
  -- Properties of โจแถ 
  module _ {n : ไบบโ} where
    macro โจแถ  = #structureOn (โจแถ แต {n})

  โผ-โจแถ :byPointwise : โ{n : ไบบโ} -> {F G : ๐๐ฎ๐ง๐ [ n ]แถ  ๐} -> (โ(i : [ n ]แถ ) -> โจ F โฉ i โ โจ G โฉ i) -> โจแถ  F โ โจแถ  G
  โผ-โจแถ :byPointwise = {!!}

  โจแถ โ : {n : ไบบโ} {F G : ๐๐ฎ๐ง๐ [ n ]แถ  ๐} -> (F โผ G) -> โจแถ  F โ โจแถ  G
  โจแถ โ {incl x} {F} {G} p = โจ โจ p โฉ โฉ _ since record
                         { inverse-โ = โจ โจ p โฉโปยน โฉ _
                         ; inv-r-โ = โจ inv-r-โ (of p) โฉ _
                         ; inv-l-โ = โจ inv-l-โ (of p) โฉ _
                         }
  โจแถ โ {m โ-โง n} {F} {G} p = โจแถ โ (refl โโโ-๐๐๐ญ p) โโโ โจแถ โ (refl โโโ-๐๐๐ญ p)
  โจแถ โ {โ-โง} {F} {G} p = refl-โ



  --------------------------------------------------------------------------------
  -- [Lemma]
  -- | If a functor |F : ๐ โ ๐| preserves coproducts, then it also
  --   preserves |โจแถ |.
  -- //
  -- [Proof]
module _ {๐ : Category ๐} {๐ : Category ๐}
         {{_ : hasFiniteCoproducts ๐}} {{_ : hasFiniteCoproducts ๐}}
         (F : Functor ๐ ๐) {{_ : isFiniteCoproductPreserving F}}
         where
  preserves-โจแถ  : โ{n} -> โ{x : ๐๐ฎ๐ง๐ [ n ]แถ  ๐} -> โจ F โฉ (โจแถ  x) โ โจแถ  (x โ-๐๐๐ญ F)
  preserves-โจแถ  {incl xโ} {x} = refl-โ
  preserves-โจแถ  {n โ-โง nโ} {x} =
    โจ F โฉ (โจแถ  (leftแถ  โ-๐๐๐ญ x) โ โจแถ  (rightแถ  โ-๐๐๐ญ x))

    โจ preserves-โ โฉ-โ

    (โจ F โฉ (โจแถ  (leftแถ  โ-๐๐๐ญ x)) โ (โจ F โฉ (โจแถ  (rightแถ  โ-๐๐๐ญ x))))

    โจ preserves-โจแถ  โโโ preserves-โจแถ  โฉ-โ

    ((โจแถ  (leftแถ  โ-๐๐๐ญ x โ-๐๐๐ญ F)) โ (โจแถ  (rightแถ  โ-๐๐๐ญ x โ-๐๐๐ญ F)))

    โจ โจแถ โ assoc-l-โ-๐๐๐ญ โโโ โจแถ โ assoc-l-โ-๐๐๐ญ โฉ-โ

    โจแถ  (x โ-๐๐๐ญ F)

    โ-โ

  -- preserves-โ โ-โ ({!!} โโโ {!!})
  preserves-โจแถ  {โ-โง} {x} = preserves-โฅ

  -- //






module _ (๐ : ๐) (๐ : Category ๐) {{_ : hasFiniteCoproducts ๐}} where
  record isFiniteCoproductGenerated : ๐ฐ (๐ ๏ฝค ๐ โบ) where
    -- constructor isFiniteCoproductGenerated:byDefinition
    field fcgProp : โจ ๐ โฉ -> ๐ฐ ๐
    field fcgPropIsoStable : โ{a b : โจ ๐ โฉ} -> a โ b -> fcgProp a -> fcgProp b
    field fcgSize : โจ ๐ โฉ -> ไบบโ
    field fcg : (a : โจ ๐ โฉ) -> ๐๐ฎ๐ง๐ [ fcgSize a ]แถ  ๐
    field fcgHasProp : โ{a : โจ ๐ โฉ} -> โ(i : [ fcgSize a ]แถ )-> fcgProp (โจ fcg a โฉ i)
    field fcgIso : โ (a : โจ ๐ โฉ) -> a โ โจแถ  (fcg a)

  open isFiniteCoproductGenerated {{...}} public



--------------------------------------------------------------
-- Properties of FCG

-- [Lemma]
-- | If there is a coproduct preserving, eso functor |๐ โ ๐|,
--   and |๐| is FCG, then so is |๐|.
--
-- //
-- [Proof]
module _ {๐ : Category ๐} {๐ : Category ๐} {{_ : hasFiniteCoproducts ๐}} {{_ : hasFiniteCoproducts ๐}} (F : Functor ๐ ๐) where
  module _ {{_ : isFiniteCoproductPreserving F}} {{_ : isEssentiallySurjective F}} where
    module _ {{_ : isFiniteCoproductGenerated ๐ ๐}} where
      private
        fcg'Size : โจ ๐ โฉ -> ไบบโ
        fcg'Size a = fcgSize (eso a)

        fcg'Prop : โจ ๐ โฉ -> ๐ฐ ๐
        fcg'Prop a = fcgProp (eso a)

        fcg' : (a : โจ ๐ โฉ) โ Functor [ fcg'Size a ]แถ  ๐
        fcg' a = fcg (eso a) โ-๐๐๐ญ F

        fcg'Iso : (a : โจ ๐ โฉ) โ a โ โจแถ  (fcg' a)
        fcg'Iso a = a

                    โจ sym-โ inv-eso โฉ-โ

                    โจ F โฉ (eso a)

                    โจ cong-โ (fcgIso (eso a)) โฉ-โ

                    โจ F โฉ (โจแถ  (fcg (eso a)))

                    โจ preserves-โจแถ  F โฉ-โ

                    โจแถ  (fcg' a)

                    โ-โ

      fcg'HasProp : {a : โจ ๐ โฉ} (i : [ fcg'Size a ]แถ แต) โ fcg'Prop (โจ fcg' a โฉ i)
      fcg'HasProp {a} i =
        let P = fcgHasProp {a = eso a} i
        in {!!}

      isFiniteCoproductGenerated:byIsFiniteCoproductPreserving : isFiniteCoproductGenerated ๐ ๐
      isFiniteCoproductGenerated:byIsFiniteCoproductPreserving = record
        { fcgSize = fcg'Size
        ; fcgProp = fcg'Prop
        ; fcg = fcg'
        ; fcgIso = fcg'Iso
        ; fcgHasProp = {!!}
        ; fcgPropIsoStable = {!!}
        }



-- //



open import Verification.Core.Category.Std.Functor.Equivalence
-- [Corollary]
-- | If there is an equivalence of categories |F : ๐ โ ๐|, and |๐| is cfg, then so is |๐|.
-- //

-- [Proof]
module _ {๐ : Category ๐} {๐ : Category ๐} {{_ : hasFiniteCoproducts ๐}} {{_ : hasFiniteCoproducts ๐}} (Fp : ๐ โ-๐๐๐ญ ๐) where
  module _ {{_ : isFiniteCoproductGenerated ๐ ๐}} where
    private
      F : Functor ๐ ๐
      F = โฒ โจ Fp โฉ โฒ

    isFiniteCoproductGenerated:byโ-๐๐๐ญ : isFiniteCoproductGenerated ๐ ๐
    isFiniteCoproductGenerated:byโ-๐๐๐ญ = isFiniteCoproductGenerated:byIsFiniteCoproductPreserving F
      where
        instance
          P-0 : isFiniteCoproductPreserving F
          P-0 = {!!}

        instance
          P-1 : isEssentiallySurjective F
          P-1 = isEssentiallySurjective:byIsIso-๐๐๐ญ

-- //
