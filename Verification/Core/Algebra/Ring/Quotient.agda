
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Core.Algebra.Ring.Quotient where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition



-- module _ {R : ð° _} {I : ð« R} {{_ : Ring ð on R}} {{_ : Ideal â² R â² on I}} where
module _ {ð : ð ^ 2} {R : Ring ð} {I : Ideal R} where
  -- blabla : isCommutative â² â¨ R â© â²
  -- blabla = it
  -- X = â¨ (â² â¨ R â© â²) /-Abelian â² â¨ I â© â² â©

  instance
    isSemiring:Quot : isSemiring â² (â¨ R â©) /-ð° RelIdeal I â²
    -- isSemiring:Quot : isSemiring â² â¨ (â² R â²) /-Abelian â² I â² â© â²
    isSemiring._â_ isSemiring:Quot [ a ] [ b ] = [ a â b ]
    isSemiring.â¨¡ isSemiring:Quot = [ â¨¡ ]
    isSemiring.unit-l-â isSemiring:Quot {a = [ a ]} = cong-â¼ unit-l-â
    isSemiring.unit-r-â isSemiring:Quot {a = [ a ]} = cong-â¼ unit-r-â
    isSemiring.assoc-l-â isSemiring:Quot {a = [ a ]} {b = [ b ]} {c = [ c ]} = cong-â¼ assoc-l-â
    isSemiring.distr-l-â isSemiring:Quot {a = [ a ]} {b = [ b ]} {c = [ c ]} = cong-â¼ distr-l-â
    isSemiring.distr-r-â isSemiring:Quot {a = [ a ]} {b = [ b ]} {c = [ c ]} = cong-â¼ distr-r-â
    isSemiring._`cong-â`_ isSemiring:Quot {aâ = [ aâ ]} {aâ = [ aâ ]} {bâ = [ bâ ]} {bâ = [ bâ ]} (incl (incl p)) (incl (incl q)) =
      let Pâ : â¨ â¨ I â© ((aâ â â¡ aâ) â bâ) â©
          Pâ = ideal-r-â p

          Pâ : â{x y z : â¨ R â©} -> ((x â â¡ y) â z) â¼ x â z â â¡ (y â z)
          Pâ {x} {y} {z} =
               ((x â â¡ y) â z) â£â¨ distr-r-â â©
               (x â z â â¡ y â z) â£â¨ refl âââ switch-â¡-â-l â»Â¹ â©
               x â z â â¡ (y â z) â

          Pâ : â¨ â¨ I â© (aâ â bâ â â¡ (aâ â bâ)) â©
          Pâ = transp-â¼ Pâ Pâ

          Pâ : â{x y z : â¨ R â©} -> (z â (x â â¡ y)) â¼ z â x â â¡ (z â y)
          Pâ {x} {y} {z} =
               (z â (x â â¡ y)) â£â¨ distr-l-â â©
               (z â x â z â â¡ y) â£â¨ refl âââ switch-â¡-â-r â»Â¹ â©
               z â x â â¡ (z â y) â

          Pâ : â¨ â¨ I â© (aâ â bâ â â¡ (aâ â bâ)) â©
          Pâ = transp-â¼ Pâ (ideal-l-â q)

          Pâ : â¨ â¨ I â© ((aâ â bâ â â¡ (aâ â bâ)) â (aâ â bâ â â¡ (aâ â bâ))) â©
          Pâ = closed-â Pâ Pâ

          Pâ : â {x y z : â¨ R â©} -> (x â â¡ y) â (y â z) â¼ x â z
          Pâ {x} {y} {z} =
            (x â â¡ y) â (y â z)   â£â¨ assoc-l-â â©
            x â (â¡ y â (y â z))   â£â¨ refl âââ assoc-r-â â©
            x â (â¡ y â y â z)     â£â¨ refl âââ ((inv-l-â âââ refl) â unit-l-â) â©
            x â z                 â

          Pâ : â¨ â¨ I â© (aâ â bâ â â¡ (aâ â bâ)) â©
          Pâ = transp-â¼ Pâ Pâ
      in incl (incl Pâ)

    -- isRing:Quot : isRing â² â¨ (â² R â²) /-Abelian â² I â² â© â²
    -- -- isRing:Quot : isRing â² â¨ (â² â¨ R â© â²) /-Abelian â² â¨ I â© â² â© â²
    -- isRing:Quot = record {}

-- _/-Ring_ : (R : Ring ð) -> (I : Ideal R) -> Ring _
-- _/-Ring_ R I = â² â¨ â² â¨ R â© â² /-Abelian â² â¨ I â© â² â© â²


