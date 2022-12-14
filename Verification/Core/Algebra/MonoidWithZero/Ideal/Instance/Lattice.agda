
module Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.Lattice where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Subsetoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Definition



---------------------------------------------------------------
-- We show that the preorder of ideals has finite meets
module _ {A : Monoidβ π} where

  -- the top element
  instance
    isIdeal:β€ : isIdeal A β€
    isIdeal.ideal-β isIdeal:β€ = tt
    isIdeal.ideal-r-β isIdeal:β€ _ _ = tt

  β€-Ideal : Ideal A
  β€-Ideal = β² β€ β²

  -- the meet
  instance
    isIdeal:β§ : β{I J : π« β¨ A β©} -> {{_ : Ideal A on I}} {{_ : Ideal A on J}} -> isIdeal A (β² I β² β§ β² J β²)
    isIdeal:β§ = record
      { ideal-β = ideal-β , ideal-β
      ; ideal-r-β = Ξ» (p , q) a -> ideal-r-β p a , ideal-r-β q a
      }

  _β§-Ideal_ : (I J : Ideal A) -> Ideal A
  _β§-Ideal_ I J = β² β¨ I β© β§ β¨ J β© β²



  instance
    hasFiniteMeets:Ideal : hasFiniteMeets (Ideal A)
    hasFiniteMeets:Ideal = record
                              { β€          = β€-Ideal
                              ; terminal-β€ = terminal-β€
                              ; _β§_        = _β§-Ideal_
                              ; Οβ-β§       = Οβ-β§
                              ; Οβ-β§       = Οβ-β§
                              ; β¨_,_β©-β§    = β¨_,_β©-β§
                              }



---------------------------------------------------------------
-- We show that the preorder of ideals has finite joins
module _ {A : Monoidβ π} where
  instance
    isIdeal:β¨ : β{I J : π« β¨ A β©} -> {{_ : Ideal A on I}} {{_ : Ideal A on J}} -> isIdeal A (β² I β² β¨ β² J β²)
    isIdeal:β¨ = record
                 { ideal-β = left ideal-β
                 ; ideal-r-β = Ξ» x b β case x of
                                       (Ξ» aβI β left (ideal-r-β aβI b))
                                       (Ξ» aβJ -> right (ideal-r-β aβJ b))
                 }

  _β¨-Ideal_ : (I J : Ideal A) -> Ideal A
  _β¨-Ideal_ I J = β² β¨ I β© β¨ β¨ J β© β²


module _ {Aα΅ : π° _} {{_ : Monoidβ (π , π) on Aα΅}} where

  private macro A = #structureOn Aα΅

  -- the zero ideal
  record β₯-Idealα΅ (a : A) : π° π where
    constructor incl
    field β¨_β© : a βΌ β

  open β₯-Idealα΅ public

  macro β₯-Ideal = #structureOn (βπ« β₯-Idealα΅)

  -- it is a setoid
  instance
    isSetoid:β₯-Ideal : isSubsetoid β₯-Ideal
    isSetoid:β₯-Ideal = record { transp-βΌ = t }
      where
        t : β{a b : A} -> a βΌ b -> β₯-Idealα΅ a -> β₯-Idealα΅ b
        t p (incl P) = incl (p β»ΒΉ β P)

  -- it is an ideal
  instance
    isIdeal:β₯-Ideal : isIdeal A β₯-Ideal
    isIdeal:β₯-Ideal = record { ideal-β = P0 ; ideal-r-β = P1 }
      where
        P0 : β₯-Idealα΅ β
        P0 = incl refl

        P1 : β{a} -> β₯-Idealα΅ a -> β b -> β₯-Idealα΅ (a β b)
        P1 {a} (incl p) b = incl q
          where
            q : (a β b) βΌ β
            q = a β b  β¨ p βββ refl β©-βΌ
                β β b  β¨ absorb-l-β β©-βΌ
                β      β

  -- it is the initial ideal
  initial-β₯-Ideal : β{I : Ideal A} -> β₯-Ideal β€ I
  initial-β₯-Ideal a = incl (Ξ» (incl aβΌβ) β transp-βΌ (aβΌβ β»ΒΉ) ideal-β)

  ----------------------------------------------------------
  -- This means that the preorder of ideals has finite joins
  instance
    hasFiniteJoins:Ideal : hasFiniteJoins (Ideal A)
    hasFiniteJoins:Ideal = record
                              { β₯          = β₯-Ideal
                              ; initial-β₯  = Ξ» {I} -> initial-β₯-Ideal {I = I}
                              ; _β¨_        = _β¨-Ideal_
                              ; ΞΉβ-β¨       = ΞΉβ-β¨
                              ; ΞΉβ-β¨       = ΞΉβ-β¨
                              ; [_,_]-β¨    = [_,_]-β¨
                              }


