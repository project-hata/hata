
module Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.hasAction where

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
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.Lattice



module _ {A : Monoidβ (π , π)} where
  record _β·-Idealα΅_ (a : β¨ A β©) (I : Ideal A) (b : β¨ A β©) : π° π where
    constructor incl
    field β¨_β©  : (β Ξ» x -> (x β I) Γ-π° (b βΌ a β x))

  module _ (a : β¨ A β©) (I : Ideal A) where
    infixr 30 _β·-Ideal_
    macro _β·-Ideal_ = #structureOn (βπ« (a β·-Idealα΅ I))


  -- module _ {a : β¨ A β©} {I : π« β¨ A β©}
  --   {{_ : isSubsetoid I}}
  --   {{_ : isIdeal A β² I β²}} where
  module _ {a : β¨ A β©} {I : Ideal A} where
    instance
      -- isSubsetoid:β·-Ideal : isSubsetoid ((a β·-Ideal β² I β²))
      isSubsetoid:β·-Ideal : isSubsetoid (a β·-Ideal I)
      isSubsetoid.transp-βΌ isSubsetoid:β·-Ideal {b} {c} p (incl (x , Ix , q)) = incl (x , Ix , p β»ΒΉ β q)

      -- isIdeal:β·-Ideal : isIdeal A (β² (Ξ» x -> β£ β¨ (a β·-Ideal I) x β© β£-Prop) β² {{isSubsetoid:β·-Ideal}})
    instance
      isIdeal:β·-Ideal : isIdeal A (a β·-Ideal I)
      isIdeal:β·-Ideal = record
        { ideal-β = incl (β , ideal-β , absorb-r-β β»ΒΉ)
        ; ideal-r-β = Ξ» {y} -> Ξ» (incl (x , xβI , xP)) b β incl $
                    (x β b) ,
                    ideal-r-β xβI b ,
                    (let Pβ : y β b βΌ a β (x β b)
                         Pβ = (xP βββ refl) β assoc-l-β
                     in Pβ)
        }


  -- infixr 30 _β·-Idealα΅_
  -- _β·-Idealα΅_ : (a : β¨ A β©) -> (I : Ideal A) -> Ideal A
  -- _β·-Idealα΅_ a I = a β·-Ideal I


  instance
    hasActionβ:Ideal : hasActionβ β² β¨ A β© β² (Ideal A)

    hasActionβ._β·_ hasActionβ:Ideal
      = Ξ» a I -> a β·-Ideal I

    hasActionβ.assoc-l-β·  hasActionβ:Ideal {m} {n} {I}
      = antisym Pβ Pβ
      where
        Pβ : ((m β n) β· I) β€ (m β· (n β· I))
        Pβ = Ξ» _ -> incl (Ξ» (incl (x , xβI , xP)) β incl $ (n β x) , (incl (x , xβI , refl) , (xP β assoc-l-β)))

        Pβ : (m β· n β· I) β€ (m β n β· I)
        β¨ Pβ a β© (incl (x , (incl (y , yβI , yP)) , xP)) = incl $ y , yβI , yP'
          where
            yP' : a βΌ (m β n) β y
            yP'  = a           β¨ xP β©-βΌ
                  m β x       β¨ refl βββ yP β©-βΌ
                  m β (n β y) β¨ assoc-r-β β©-βΌ
                  (m β n) β y β

    hasActionβ._ββ·β_       hasActionβ:Ideal {m} {n} {I} {J} p q =
      let Pβ : (m β· I) β€ (n β· J)
          Pβ = Ξ» _ -> incl (Ξ» (incl (x , xβI , xP)) β incl $ x , β¨ by-βΌ-β€ (β¨ q β©) β© xβI  , (xP β (p βββ refl)))
          Pβ : (n β· J) β€ (m β· I)
          Pβ = Ξ» _ -> incl (Ξ» (incl (x , xβI , xP)) β incl $ x , β¨ by-βΌ-β€ β¨ q β»ΒΉ β© β© xβI  , (xP β (p β»ΒΉ βββ refl)))
      in antisym Pβ Pβ


  -- distributivity
  distr-β·-β§-Ide : {a : β¨ A β©} -> {I J : Ideal A} -> (isZeroOrEpi a) -> (a β· (I β§ J)) βΌ ((a β· I) β§ (a β· J))
  distr-β·-β§-Ide {a} {I} {J} P =
    let Pβ : (a β· (I β§ J)) β€ ((a β· I) β§ (a β· J))
        Pβ = Ξ» _ -> incl (Ξ» (incl (x , (xβI , xβJ) , xP)) β (incl (x , xβI , xP)) , (incl (x , xβJ , xP)))
        -- Pβ = incl (Ξ» {b} (incl (x , xβI , xP) , incl (y , yβJ , yP)) β
        --   let Qβ = case P of
        --               (Ξ» aβΌβ ->
        --                 let Qβ : b βΌ a β β
        --                     Qβ = b      β¨ xP β©-βΌ
        --                          a β x  β¨ aβΌβ βββ refl β©-βΌ
        --                          β β x  β¨ absorb-l-β β©-βΌ
        --                          β      β¨ absorb-r-β β»ΒΉ β©-βΌ
        --                          a β β  β

        --                 in incl (β , ideal-β , Qβ)
        --               )
        --               (Ξ» (aββ , cancel-a) -> let Qβ : a β x βΌ a β y
        --                                          Qβ = xP β»ΒΉ β yP
        --                                          Qβ : x βΌ y
        --                                          Qβ = cancel-a Qβ
        --                                          Qβ : x β (I β§ J)
        --                                          Qβ = (xβI , transp-βΌ (Qβ β»ΒΉ) yβJ)

        --                                      in incl (x , Qβ , xP))

        --   in Qβ)
    in {!!} -- antisym Pβ Pβ




--------------------------------------------------------------------------------------------------------------
-- There is an additional inverse action


  record _β»ΒΉβ·-Ide''_ (a : β¨ A β©) (I : Ideal A) (x : β¨ A β©) : π° π where
    constructor incl
    field β¨_β©  : (a β x) β I

  open _β»ΒΉβ·-Ide''_ {{...}} public

  _β»ΒΉβ·-Ide'_ : (a : β¨ A β©) -> (I : Ideal A) -> π« β¨ A β©
  _β»ΒΉβ·-Ide'_ a I = Ξ» x β β£ (a β»ΒΉβ·-Ide'' I) x β£

  -- _β»ΒΉβ·-Ide'_ : (a : β¨ A β©) -> (I : Ideal A) -> π« β¨ A β©
  -- _β»ΒΉβ·-Ide'_ a I = Ξ» x β β£ (a β x) β I β£

  -- module _ {a : β¨ A β©} {I : π« β¨ A β©} {{_ : Ideal A on I}} where
  module _ {a : β¨ A β©} {I : π« β¨ A β©}
    {{_ : isSubsetoid I}}
    {{_ : isIdeal A β² I β²}} where
    instance
      isSubsetoid:β»ΒΉβ·-Ide' : isSubsetoid (a β»ΒΉβ·-Ide' β² I β²)
      isSubsetoid.transp-βΌ isSubsetoid:β»ΒΉβ·-Ide' {x} {y} xβΌy xβI = incl (transp-βΌ (refl βββ xβΌy) β¨ xβI β©)

    instance
      isIdeal:β»ΒΉβ·-Ide' : isIdeal A β²(a β»ΒΉβ·-Ide' β² I β²)β²
      isIdeal.ideal-β   isIdeal:β»ΒΉβ·-Ide' = incl (transp-βΌ (absorb-r-β β»ΒΉ) ideal-β)
      isIdeal.ideal-r-β isIdeal:β»ΒΉβ·-Ide' {b} bβaβ»ΒΉI c =
        let Pβ : a β (b β c) β I
            Pβ = transp-βΌ assoc-l-β (ideal-r-β β¨ bβaβ»ΒΉI β© c)
        in incl Pβ

  _β»ΒΉβ·-Ide_ : (a : β¨ A β©) -> (I : Ideal A) -> Ideal A
  _β»ΒΉβ·-Ide_ a I = β²(a β»ΒΉβ·-Ide' I)β² {{isIdeal:β»ΒΉβ·-Ide' {a = a} {I = β¨ I β©}}}

  inv-β·Ide-r : {a : β¨ A β©} -> {I : Ideal A} -> a β· (a β»ΒΉβ·-Ide I) βΌ I β§ (a β· β€)
  inv-β·Ide-r {a} {I} =
    let Pβ : (a β· (a β»ΒΉβ·-Ide I)) β€ (I β§ (a β· β€))
        Pβ = {!!} -- incl (Ξ» (incl (x , xβaβ»ΒΉI , xP)) β transp-βΌ (xP β»ΒΉ) β¨ xβaβ»ΒΉI β© , incl (x , tt , xP))
        Pβ : (I β§ (a β· β€)) β€ (a β· (a β»ΒΉβ·-Ide I))
        Pβ = {!!} -- incl (Ξ» {b} (x , (incl (z , _ , zP))) β incl $ z , (incl (transp-βΌ zP x) , zP))
    in antisym Pβ Pβ

  absorb-l-β»ΒΉβ·-Ide : {I : Ideal A} -> (β β»ΒΉβ·-Ide I) βΌ β€
  absorb-l-β»ΒΉβ·-Ide {I} =
    let Pβ : β€ β€ (β β»ΒΉβ·-Ide I)
        Pβ = {!!} -- incl (Ξ» x β incl (transp-βΌ (absorb-l-β β»ΒΉ) ideal-β))
    in {!!} --  antisym terminal-β€ Pβ


  unit-l-β»ΒΉβ·-Ide : {I : Ideal A} -> (β β»ΒΉβ·-Ide I) βΌ I
  unit-l-β»ΒΉβ·-Ide {I} =
    let Pβ : (β β»ΒΉβ·-Ide I) β€ I
        Pβ = {!!} -- incl (Ξ» (incl x) β transp-βΌ unit-l-β x)
        Pβ : I β€ (β β»ΒΉβ·-Ide I)
        Pβ = {!!} -- incl (Ξ» x β incl (transp-βΌ (unit-l-β β»ΒΉ) x))
    in antisym Pβ Pβ

  unit-r-β»ΒΉβ·-Ide : {a : β¨ A β©} -> (a β»ΒΉβ·-Ide β€) βΌ β€
  unit-r-β»ΒΉβ·-Ide {a} =
    let Pβ : β€ β€ (a β»ΒΉβ·-Ide β€)
        Pβ = Ξ» _ -> incl (Ξ» x β incl tt)
        Pβ : (a β»ΒΉβ·-Ide β€) β€ β€
        Pβ = Ξ» _ -> incl (Ξ» x β tt)
    in antisym Pβ Pβ



