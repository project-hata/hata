
module Verification.Core.Algebra.Ring.Localization.Instance.Setoid where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
-- open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Ring.Localization.Definition



module _ {๐ : ๐ ^ 2} {R : CRing ๐} {M : MCS R} where
  LocRel : Localize R M -> Localize R M -> ๐ฐ _
  LocRel (a / da) (b / db) = โ ฮป (t : โฆ โจ M โฉ โฆ) -> (a โ โจ db โฉ โ โจ t โฉ) โผ (b โ โจ da โฉ โ โจ t โฉ)

  -- instance
  --   isEquivRel:LocRel : isEquivRel (โผ-Base LocRel)
  --   isEquivRel.refl isEquivRel:LocRel {x = a / da} = incl ((โจก โข closed-โจก) , refl)
  --   isEquivRel.sym isEquivRel:LocRel {x = a / da} {y = b / db} (incl (t , p)) = incl (t , sym p)
  --   isEquivRel._โ_ isEquivRel:LocRel {x = a / (da โข _)} {y = b / (db โข dbP)} {z = c / (dc โข _)} (incl ((s โข sP) , p)) (incl ((t โข tP) , q)) =
  --     let u : โฆ โจ M โฉ โฆ
  --         u = db โ s โ t โข closed-โ (closed-โ dbP sP) tP

  --         P : a โ dc โ โจ u โฉ โผ c โ da โ โจ u โฉ
  --         P = a โ dc โ (db โ s โ t)     โฃโจ assoc-l-โ โฉ
  --             a โ (dc โ (db โ s โ t))   โฃโจ refl `cong-โ` comm-โ โฉ
  --             a โ ((db โ s โ t) โ dc)   โฃโจ assoc-r-โ โฉ
  --             a โ (db โ s โ t) โ dc     โฃโจ assoc-r-โ `cong-โ` refl โฉ
  --             a โ (db โ s) โ t โ dc     โฃโจ (assoc-r-โ โ p โ assoc-l-โ) `cong-โ` refl `cong-โ` refl โฉ
  --             b โ (da โ s) โ t โ dc     โฃโจ comm-โ `cong-โ` refl `cong-โ` refl โฉ
  --             (da โ s) โ b โ t โ dc     โฃโจ assoc-l-โ `cong-โ` refl โฉ
  --             (da โ s) โ (b โ t) โ dc   โฃโจ assoc-l-โ โฉ
  --             (da โ s) โ (b โ t โ dc)   โฃโจ refl `cong-โ` assoc-l-โ โฉ
  --             (da โ s) โ (b โ (t โ dc)) โฃโจ refl `cong-โ` (refl `cong-โ` comm-โ) โฉ
  --             (da โ s) โ (b โ (dc โ t)) โฃโจ refl `cong-โ` (assoc-r-โ โ q) โฉ
  --             (da โ s) โ (c โ db โ t)   โฃโจ assoc-l-โ โฉ
  --             da โ (s โ (c โ db โ t))   โฃโจ refl `cong-โ` comm-โ โฉ
  --             da โ (c โ db โ t โ s)     โฃโจ refl `cong-โ` assoc-l-โ โฉ
  --             da โ (c โ db โ (t โ s))   โฃโจ refl `cong-โ` assoc-l-โ โฉ
  --             da โ (c โ (db โ (t โ s))) โฃโจ assoc-r-โ โฉ
  --             (da โ c) โ (db โ (t โ s)) โฃโจ comm-โ `cong-โ` ((refl `cong-โ` comm-โ) โ assoc-r-โ) โฉ
  --             c โ da โ (db โ s โ t)     โ
  --     in incl (u , P)

  instance
    isSetoid:Localize : isSetoid (Localize R M)
    isSetoid._โผ_ isSetoid:Localize = โผ-Base LocRel
    isSetoid.refl isSetoid:Localize {a = a / da} = incl ((โจก โข closed-โจก) , refl)
    isSetoid.sym isSetoid:Localize {a = a / da} {b = b / db} (incl (t , p)) = incl (t , sym p)
    isSetoid._โ_ isSetoid:Localize {a = a / (da โข _)} {b = b / (db โข dbP)} {c = c / (dc โข _)} (incl ((s โข sP) , p)) (incl ((t โข tP) , q)) =
      let u : โฆ โจ M โฉ โฆ
          u = db โ s โ t โข closed-โ (closed-โ dbP sP) tP

          P : a โ dc โ โจ u โฉ โผ c โ da โ โจ u โฉ
          P = a โ dc โ (db โ s โ t)     โฃโจ assoc-l-โ โฉ
              a โ (dc โ (db โ s โ t))   โฃโจ refl `cong-โ` comm-โ โฉ
              a โ ((db โ s โ t) โ dc)   โฃโจ assoc-r-โ โฉ
              a โ (db โ s โ t) โ dc     โฃโจ assoc-r-โ `cong-โ` refl โฉ
              a โ (db โ s) โ t โ dc     โฃโจ (assoc-r-โ โ p โ assoc-l-โ) `cong-โ` refl `cong-โ` refl โฉ
              b โ (da โ s) โ t โ dc     โฃโจ comm-โ `cong-โ` refl `cong-โ` refl โฉ
              (da โ s) โ b โ t โ dc     โฃโจ assoc-l-โ `cong-โ` refl โฉ
              (da โ s) โ (b โ t) โ dc   โฃโจ assoc-l-โ โฉ
              (da โ s) โ (b โ t โ dc)   โฃโจ refl `cong-โ` assoc-l-โ โฉ
              (da โ s) โ (b โ (t โ dc)) โฃโจ refl `cong-โ` (refl `cong-โ` comm-โ) โฉ
              (da โ s) โ (b โ (dc โ t)) โฃโจ refl `cong-โ` (assoc-r-โ โ q) โฉ
              (da โ s) โ (c โ db โ t)   โฃโจ assoc-l-โ โฉ
              da โ (s โ (c โ db โ t))   โฃโจ refl `cong-โ` comm-โ โฉ
              da โ (c โ db โ t โ s)     โฃโจ refl `cong-โ` assoc-l-โ โฉ
              da โ (c โ db โ (t โ s))   โฃโจ refl `cong-โ` assoc-l-โ โฉ
              da โ (c โ (db โ (t โ s))) โฃโจ assoc-r-โ โฉ
              (da โ c) โ (db โ (t โ s)) โฃโจ comm-โ `cong-โ` ((refl `cong-โ` comm-โ) โ assoc-r-โ) โฉ
              c โ da โ (db โ s โ t)     โ
      in incl (u , P)




    -- isSetoid._โผ'_ isSetoid:Localize = LocRel
    -- isSetoid.isEquivRel:โผ isSetoid:Localize = {!!}




