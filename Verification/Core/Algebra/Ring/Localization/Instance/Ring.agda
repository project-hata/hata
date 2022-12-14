
module Verification.Core.Algebra.Ring.Localization.Instance.Ring where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
-- open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Ring.Localization.Definition
open import Verification.Core.Algebra.Ring.Localization.Instance.Setoid
open import Verification.Core.Algebra.Ring.Localization.Instance.Monoid
open import Verification.Core.Algebra.Ring.Localization.Instance.Group




module _ {๐ : ๐ ร-๐ฐ ๐} {R : CRing ๐} {M : MCS R} where
  private
    _โ-Loc_ : (a b : Localize R M) -> Localize R M
    _โ-Loc_ (a / da) (b / db) = (a โ b) / (da โ-MCS db)
    infixl 80 _โ-Loc_

    โจก-Loc : Localize R M
    โจก-Loc = โจก / โจก-MCS

    lem-10 : โ{a b : Localize R M} -> a โ-Loc b โผ b โ-Loc a
    lem-10 {a / (da โข _)} {b / (db โข _)} =
      let P : (a โ b) โ (db โ da) โผ (b โ a) โ (da โ db)
          P = comm-โ โโโ comm-โ
      in incl (โจก-MCS , P โโโ โ)

    lem-20 : โ{a : Localize R M} -> โจก-Loc โ-Loc a โผ a
    lem-20 {a / (da โข _)} =
      let P : (โจก โ a) โ da โผ a โ (โจก โ da)
          P = (โจก โ a) โ da   โฃโจ unit-l-โ โโโ โ โฉ
              a โ da         โฃโจ โ โโโ unit-l-โ โปยน โฉ
              a โ (โจก โ da)   โ

      in incl (โจก-MCS , P โโโ โ)

    lem-30 : โ{a b c : Localize R M} -> (a โ-Loc b) โ-Loc c โผ a โ-Loc (b โ-Loc c)
    lem-30 {a / (da โข _)} {b / (db โข _)} {c / (dc โข _)} =
      let P : (a โ b โ c) โ (da โ (db โ dc)) โผ (a โ (b โ c)) โ (da โ db โ dc)
          P = assoc-l-โ โโโ assoc-r-โ
      in incl (โจก-MCS , P โโโ โ)

    lem-40 : โ{a b c : Localize R M} -> a โ-Loc (b โ c) โผ (a โ-Loc b) โ (a โ-Loc c)
    lem-40 {a / (da โข _)} {b / (db โข _)} {c / (dc โข _)} =
      let Pโ : โ{a b da db dc : โจ R โฉ} -> (a โ (b โ dc)) โ ((da โ db) โ (da โ dc))  โผ  ((a โ b) โ (da โ dc)) โ (da โ (db โ dc))
          Pโ {a} {b} {da} {db} {dc} =
               (a โ (b โ dc)) โ ((da โ db) โ (da โ dc))  โฃโจ assoc-r-โ โโโ assoc-r-โ โฉ
               ((a โ b) โ dc) โ (((da โ db) โ da) โ dc)  โฃโจ โ โโโ (assoc-l-โ โโโ โ) โฉ
               ((a โ b) โ dc) โ ((da โ (db โ da)) โ dc)  โฃโจ โ โโโ ((โ โโโ comm-โ) โโโ โ) โฉ
               ((a โ b) โ dc) โ ((da โ (da โ db)) โ dc)  โฃโจ โ โโโ assoc-l-โ โฉ
               ((a โ b) โ dc) โ (da โ ((da โ db) โ dc))  โฃโจ โ โโโ (โ โโโ assoc-l-โ) โฉ
               ((a โ b) โ dc) โ (da โ (da โ (db โ dc)))  โฃโจ assoc-l-โ โฉ
               (a โ b) โ (dc โ (da โ (da โ (db โ dc))))  โฃโจ โ โโโ assoc-r-โ โฉ
               (a โ b) โ ((dc โ da) โ (da โ (db โ dc)))  โฃโจ assoc-r-โ โฉ
               ((a โ b) โ (dc โ da)) โ (da โ (db โ dc))  โฃโจ โ โโโ comm-โ โโโ โ โฉ
               ((a โ b) โ (da โ dc)) โ (da โ (db โ dc))  โ

          Pโ : (a โ (c โ db)) โ ((da โ db) โ (da โ dc))  โผ  ((a โ c) โ (da โ db)) โ (da โ (db โ dc))
          Pโ = (a โ (c โ db)) โ ((da โ db) โ (da โ dc)) โฃโจ โ โโโ comm-โ โฉ
               (a โ (c โ db)) โ ((da โ dc) โ (da โ db)) โฃโจ Pโ โฉ
               ((a โ c) โ (da โ db)) โ (da โ (dc โ db)) โฃโจ โ โโโ (โ โโโ comm-โ) โฉ
               ((a โ c) โ (da โ db)) โ (da โ (db โ dc)) โ

          Pโ : (a โ (b โ dc โ c โ db)) โ ((da โ db) โ (da โ dc)) โผ ((a โ b) โ (da โ dc) โ (a โ c) โ (da โ db)) โ (da โ (db โ dc))
          Pโ = (a โ (b โ dc โ c โ db)) โ ((da โ db) โ (da โ dc))                                   โฃโจ distr-l-โ โโโ โ โฉ
               (a โ (b โ dc) โ a โ (c โ db)) โ ((da โ db) โ (da โ dc))                              โฃโจ distr-r-โ โฉ
               (a โ (b โ dc)) โ ((da โ db) โ (da โ dc)) โ (a โ (c โ db)) โ ((da โ db) โ (da โ dc))    โฃโจ Pโ โโโ Pโ โฉ
               ((a โ b) โ (da โ dc)) โ (da โ (db โ dc)) โ ((a โ c) โ (da โ db)) โ (da โ (db โ dc))    โฃโจ distr-r-โ โปยน โฉ
               ((a โ b) โ (da โ dc) โ (a โ c) โ (da โ db)) โ (da โ (db โ dc)) โ

      in incl (โจก-MCS , Pโ โโโ โ)

    lem-50 : โ{aโ aโ bโ bโ : Localize R M} -> (aโ โผ aโ) -> (bโ โผ bโ) -> (aโ โ-Loc bโ โผ aโ โ-Loc bโ)
    lem-50 {aโ / (daโ โข _)} {aโ / (daโ โข _)} {bโ / (dbโ โข _)} {bโ / (dbโ โข _)} (incl ((s โข sP) , p)) (incl ((t โข tP) , q)) =
      let Pโ : โ{aโ bโ daโ dbโ s t : โจ R โฉ} -> (aโ โ bโ) โ (daโ โ dbโ) โ (s โ t) โผ (aโ โ daโ โ s) โ (bโ โ dbโ โ t)
          Pโ {aโ} {bโ} {daโ} {dbโ} {s} {t} =
               (aโ โ bโ) โ (daโ โ dbโ) โ (s โ t)   โฃโจ assoc-r-โ โฉ
               ((aโ โ bโ) โ (daโ โ dbโ) โ s) โ t   โฃโจ assoc-l-โ โโโ โ โฉ
               ((aโ โ bโ) โ ((daโ โ dbโ) โ s)) โ t   โฃโจ โ โโโ comm-โ โโโ โ โฉ
               ((aโ โ bโ) โ (s โ (daโ โ dbโ))) โ t   โฃโจ โ โโโ (assoc-r-โ โ (comm-โ โโโ โ)) โโโ โ โฉ
               ((aโ โ bโ) โ ((daโ โ s) โ dbโ)) โ t   โฃโจ assoc-l-โ โโโ โ โฉ
               (aโ โ (bโ โ ((daโ โ s) โ dbโ))) โ t   โฃโจ โ โโโ assoc-r-โ โโโ โ โฉ
               (aโ โ ((bโ โ (daโ โ s)) โ dbโ)) โ t   โฃโจ โ โโโ (comm-โ โโโ โ) โโโ โ โฉ
               (aโ โ (((daโ โ s) โ bโ) โ dbโ)) โ t   โฃโจ โ โโโ assoc-l-โ โโโ โ โฉ
               (aโ โ ((daโ โ s) โ (bโ โ dbโ))) โ t   โฃโจ assoc-r-โ โโโ โ โฉ
               ((aโ โ (daโ โ s)) โ (bโ โ dbโ)) โ t   โฃโจ assoc-l-โ โฉ
               (aโ โ (daโ โ s)) โ ((bโ โ dbโ) โ t)   โฃโจ assoc-r-โ โโโ โ โฉ
               (aโ โ daโ โ s) โ (bโ โ dbโ โ t)     โ

          Pโ : (aโ โ bโ) โ (daโ โ dbโ) โ (s โ t) โผ (aโ โ bโ) โ (daโ โ dbโ) โ (s โ t)
          Pโ = Pโ โ (p โโโ q) โ Pโ โปยน
      in incl (((s โข sP) โ-MCS (t โข tP)) , Pโ)

  instance
    isSemiring:Localize : isSemiring โฒ Localize R M โฒ
    isSemiring._โ_ isSemiring:Localize = _โ-Loc_
    isSemiring.โจก isSemiring:Localize = โจก-Loc
    isSemiring.unit-l-โ isSemiring:Localize = lem-20
    isSemiring.unit-r-โ isSemiring:Localize = lem-10 โ lem-20
    isSemiring.assoc-l-โ isSemiring:Localize = lem-30
    isSemiring.distr-l-โ isSemiring:Localize = lem-40
    isSemiring.distr-r-โ isSemiring:Localize = lem-10 โ lem-40 โ (lem-10 โโโ lem-10)
    isSemiring._`cong-โ`_ isSemiring:Localize = lem-50

  instance
    isRing:Localize : isRing โฒ Localize R M โฒ
    isRing:Localize = record {}

  instance
    isCRing:Localize : isCRing โฒ Localize R M โฒ
    isCRing.comm-โ isCRing:Localize = lem-10



