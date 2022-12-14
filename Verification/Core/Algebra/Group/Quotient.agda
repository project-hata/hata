
module Verification.Core.Algebra.Group.Quotient where

open import Verification.Core.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition

module _ {๐ : ๐ ^ 2} {G : Group ๐} where
  record isNormal (H : Subgroup G) : ๐ฐ ๐ where
    field normal : โ a -> โ{b : โจ G โฉ} -> โจ โจ H โฉ b โฉ -> โจ โจ H โฉ (a โ b โ โก a) โฉ

  open isNormal {{...}} public

module _ where
-- private
  module _ {๐ : ๐ ^ 2} {G : Group ๐} {H : Subgroup G} {{_ : isNormal H}} where

    private
      lem-10 : โ{a : โจ G โฉ} -> RelSubgroup H a a
      lem-10 {a} = incl (transp-โผ (inv-r-โ โปยน) closed-โ)

      lem-20 : โ{a b} -> RelSubgroup H a b -> RelSubgroup H b a
      lem-20 {a} {b} (incl x) =
        let p : โก (a โ โก b) โผ b โ (โก a)
            p = โก (a โ โก b) โฃโจ distr-โ-โก โฉ
                โก โก b โ โก a โฃโจ double-โก โโโ refl โฉ
                b โ โก a     โ
        in incl (transp-โผ p (closed-โก x))

      lem-30 : โ{a b c} -> RelSubgroup H a b -> RelSubgroup H b c -> RelSubgroup H a c
      lem-30 {a} {b} {c} (incl p) (incl q) =
        let P = (a โ โก b) โ (b โ โก c) โฃโจ assoc-r-โ โฉ
                (a โ โก b) โ b โ โก c   โฃโจ assoc-l-โ โโโ refl โฉ
                a โ (โก b โ b) โ โก c   โฃโจ refl โโโ inv-l-โ โโโ refl โฉ
                a โ โ โ โก c           โฃโจ unit-r-โ โโโ refl โฉ
                a โ โก c               โ
        in incl (transp-โผ P (closed-โ p q))

    instance
      isEquivRel:RelSubgroup : isEquivRel (RelSubgroup H)
      isEquivRel.refl-Equiv isEquivRel:RelSubgroup = lem-10
      isEquivRel.sym-Equiv isEquivRel:RelSubgroup = lem-20
      isEquivRel._โ-Equiv_ isEquivRel:RelSubgroup = lem-30

    instance
      isSetoidHom:[] : isSetoidHom โฒ(โจ G โฉ)โฒ โฒ(โจ G โฉ /-๐ฐ RelSubgroup H)โฒ [_]
      isSetoidHom.cong-โผ isSetoidHom:[] {a} {b} (p) =
        let P = a โ โก b โฃโจ p โโโ refl โฉ
                b โ โก b โฃโจ inv-r-โ โฉ
                โ       โ
        in incl (incl (transp-โผ (P โปยน) closed-โ))

    instance
      isMonoid:GroupQuot : isMonoid โฒ โจ G โฉ /-๐ฐ RelSubgroup H โฒ
      isMonoid._โ_ isMonoid:GroupQuot [ a ] [ b ] = [ a โ b ]
      isMonoid.โ isMonoid:GroupQuot = [ โ ]
      isMonoid.unit-l-โ isMonoid:GroupQuot {a = [ a ]} = cong-โผ unit-l-โ
      isMonoid.unit-r-โ isMonoid:GroupQuot {a = [ a ]} = cong-โผ unit-r-โ
      isMonoid.assoc-l-โ isMonoid:GroupQuot {a = [ a ]} {b = [ b ]} {c = [ c ]} = cong-โผ assoc-l-โ
      -- isMonoid.assoc-r-โ isMonoid:GroupQuot {a = [ a ]} {b = [ b ]} {c = [ c ]} = cong-โผ assoc-r-โ
      isMonoid._โโโ_ isMonoid:GroupQuot {aโ = [ aโ ]} {aโ = [ aโ ]} {bโ = [ bโ ]} {bโ = [ bโ ]} (incl (incl p)) (incl (incl q)) =
        let Pโ : โจ โจ H โฉ (aโ โ (bโ โ โก bโ) โ โก aโ) โฉ
            Pโ = normal aโ q

            Pโ : โจ โจ H โฉ ((aโ โ โก aโ) โ (aโ โ (bโ โ โก bโ) โ โก aโ)) โฉ
            Pโ = closed-โ p Pโ

            Pโ = ((aโ โ โก aโ) โ (aโ โ (bโ โ โก bโ) โ โก aโ))  โฃโจ assoc-l-โ โฉ
                (aโ โ (โก aโ โ (aโ โ (bโ โ โก bโ) โ โก aโ)))  โฃโจ refl โโโ assoc-r-โ โฉ
                (aโ โ (โก aโ โ (aโ โ (bโ โ โก bโ)) โ โก aโ))  โฃโจ refl โโโ (assoc-r-โ โโโ refl) โฉ
                (aโ โ ((โก aโ โ aโ) โ (bโ โ โก bโ) โ โก aโ))  โฃโจ refl โโโ ((inv-l-โ โโโ refl) โโโ refl) โฉ
                (aโ โ (โ โ (bโ โ โก bโ) โ โก aโ))            โฃโจ refl โโโ (unit-l-โ โโโ refl) โฉ
                (aโ โ ((bโ โ โก bโ) โ โก aโ))                โฃโจ refl โโโ assoc-l-โ โฉ
                (aโ โ (bโ โ (โก bโ โ โก aโ)))                โฃโจ assoc-r-โ โฉ
                ((aโ โ bโ) โ (โก bโ โ โก aโ))                โฃโจ refl โโโ distr-โ-โก โปยน โฉ
                (aโ โ bโ) โ โก (aโ โ bโ)                    โ

            Pโ : โจ โจ H โฉ ((aโ โ bโ) โ โก (aโ โ bโ)) โฉ
            Pโ = transp-โผ Pโ Pโ

        in incl (incl Pโ)

    instance
      isGroup:GroupQuot : isGroup โฒ โจ G โฉ /-๐ฐ RelSubgroup H โฒ
      isGroup.โก_ isGroup:GroupQuot [ a ] = [ โก a ]
      isGroup.inv-l-โ isGroup:GroupQuot {a = [ a ]} = cong-โผ inv-l-โ
      isGroup.inv-r-โ isGroup:GroupQuot {a = [ a ]} = cong-โผ inv-r-โ
      isGroup.cong-โก_ isGroup:GroupQuot {aโ = [ aโ ]} {aโ = [ aโ ]} (incl (incl p)) =
        let Pโ = โก (aโ โ โก aโ)               โฃโจ distr-โ-โก โฉ
                  โก โก aโ โ โก aโ               โฃโจ double-โก โโโ refl โฉ
                  aโ โ โก aโ                   โ

            Pโ : โจ โจ H โฉ (aโ โ โก aโ) โฉ
            Pโ = transp-โผ Pโ (closed-โก p)

            Pโ : โจ โจ H โฉ (โก aโ โ (aโ โ โก aโ) โ โก โก aโ) โฉ
            Pโ = normal (โก aโ) Pโ

            Pโ = โก aโ โ (aโ โ โก aโ) โ โก โก aโ โฃโจ assoc-r-โ โโโ refl โฉ
                  (โก aโ โ aโ) โ โก aโ โ โก โก aโ โฃโจ inv-l-โ โโโ refl โโโ refl โฉ
                  โ โ โก aโ โ โก โก aโ           โฃโจ unit-l-โ โโโ refl โฉ
                  โก aโ โ โก โก aโ               โ

            Pโ : โจ โจ H โฉ (โก aโ โ โก โก aโ) โฉ
            Pโ = transp-โผ Pโ Pโ
        in incl (incl Pโ)

_/-Group_ : {๐ : ๐ ^ 2} (G : Group ๐) -> (H : Subgroup G) {{_ : isNormal H}} -> Group _
_/-Group_ G H = โฒ โจ G โฉ /-๐ฐ RelSubgroup H โฒ

