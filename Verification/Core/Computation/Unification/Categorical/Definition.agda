
module Verification.Core.Computation.Unification.Categorical.Definition where

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




module _ (๐ : Category ๐) where
  HomFamily : โ ๐ -> ๐ฐ _
  HomFamily ๐ = โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> ๐ฐ ๐

module _ {๐ : ๐ฐ ๐} {{_ : isCategory {๐} ๐}} where
  module _ {{_ : isZeroMorphismCategory โฒ ๐ โฒ}} where

    record isPt {a b : ๐} (f : a โถ b) : ๐ฐ (๐ ๏ฝค ๐) where
      constructor incl
      field โจ_โฉ : f โผ pt
      -- -> isPt {a} {b} f

    open isPt public


module _ {๐ : Category ๐} {{_ : isSizedCategory ๐}} {{_ : isZeroMorphismCategory ๐}} where

  isGood : HomFamily ๐ _
  isGood {a} {b} g = isPt g +-๐ฐ (isId g +-๐ฐ (sizeO b โช sizeO a))

  transp-isGood : โ{a b : โจ ๐ โฉ} {f g : a โถ b} -> f โผ g -> isGood f -> isGood g
  transp-isGood fโผg (left (incl fโผpt)) = left (incl (fโผg โปยน โ fโผpt))
  transp-isGood fโผg (just (left (incl fโผid))) = just (left (incl (fโผg โปยน โ fโผid)))
  transp-isGood fโผg (just (just x)) = just (just x)

  isGood:โ : โ{a b c : โจ ๐ โฉ} {f : a โถ b} {g : b โถ c} -> isGood f -> isGood g -> isGood (f โ g)
  isGood:โ (left (incl fโผpt)) (q) = left (incl ((fโผpt โ refl) โ absorb-l-โ))
  isGood:โ (just (left (incl fโผid))) q = transp-isGood (unit-l-โ โปยน โ (fโผid โปยน โ refl)) q
  isGood:โ (just (just x)) (left (incl gโผpt)) = left (incl ((refl โ gโผpt) โ absorb-r-โ))
  isGood:โ (just (just x)) (just (left (incl _))) = just (just x)
  isGood:โ (just (just x)) (just (just y)) = just (just (y โก-โช x))


module _ {๐} {๐ : ๐ฐ _} {{_ : ๐๐๐๐๐ญ ๐ on ๐}} where
  UpFamily : (a : ๐) -> ๐ฐ _
  UpFamily a = โ{b : ๐} -> (a โถ b) -> ๐ฐ (๐)

  record isIdeal (a : ๐) (P : โ{b : ๐} -> (f : a โถ b) -> ๐ฐ (๐)) : ๐ฐ (๐) where
    field transp-Ideal : โ{b} -> {f g : a โถ b} -> (p : f โผ g) -> P f -> P g
    field ideal-r-โ : โ{b} -> {f : a โถ b} -> P f -> โ{c} -> (g : b โถ c) -> P (f โ g)
    field ideal-pt : โ{b} -> P {b} pt

  open isIdeal {{...}} public

  module _ (a : ๐) where
    Idealแต = _ :& isIdeal a
    macro Ideal = #structureOn Idealแต


  module _ {a : ๐} where

    record _โผ-Ideal_ (A B : Ideal a) : ๐ฐ (๐) where
      constructor incl
      field โจ_โฉ : โ{b} -> (f : a โถ b) -> โจ A โฉ f โ โจ B โฉ f

    open _โผ-Ideal_ public
    -- _โผ-Ideal_ : (A B : Ideal a) -> ๐ฐ _
    -- _โผ-Ideal_ A B = โ{b} -> (f : a โถ b) -> โจ A โฉ f โ โจ B โฉ f

    private
      lem-1 : โ{A : Ideal a} -> A โผ-Ideal A
      lem-1 = incl ฮป f โ (id , id)

      lem-2 : โ{A B : Ideal a} -> A โผ-Ideal B -> B โผ-Ideal A
      lem-2 P = incl ฮป f โ โจ P โฉ f .snd , โจ P โฉ f .fst

      lem-3 : โ{A B C : Ideal a} -> A โผ-Ideal B -> B โผ-Ideal C -> A โผ-Ideal C
      lem-3 P Q = incl ฮป f โ โจ P โฉ f .fst โ โจ Q โฉ f .fst , โจ Q โฉ f .snd โ โจ P โฉ f .snd


    instance
      isSetoid:Ideal : isSetoid (Ideal a)
      isSetoid:Ideal = isSetoid:byDef (_โผ-Ideal_) lem-1 lem-2 lem-3

    record _โค-Ideal_ (A B : Ideal a) : ๐ฐ (๐) where
      constructor incl
      field โจ_โฉ : โ{b} -> (f : a โถ b) -> โจ A โฉ f -> โจ B โฉ f

    open _โค-Ideal_ public

    reflexive-Ideal : โ{A : Ideal a} -> A โค-Ideal A
    reflexive-Ideal = incl ฮป f P โ P

    _โก-Ideal_ : โ{A B C : Ideal a} -> A โค-Ideal B -> B โค-Ideal C -> A โค-Ideal C
    _โก-Ideal_ P Q = incl ฮป f โ โจ P โฉ f โ โจ Q โฉ f

    transp-โค-Ideal : โ{A B C D : Ideal a} -> (A โผ B) -> (C โผ D) -> A โค-Ideal C -> B โค-Ideal D
    transp-โค-Ideal p q r = incl ฮป f โ โจ p โฉ f .snd โ โจ r โฉ f โ โจ q โฉ f .fst

    instance
      isPreorder:Ideal : isPreorder _ (Ideal a)
      isPreorder:Ideal = record
        { _โค_ = _โค-Ideal_
        ; reflexive = reflexive-Ideal
        ; _โก_ = _โก-Ideal_
        ; transp-โค = transp-โค-Ideal
        }

      isPartialorder:Ideal : isPartialorder (Ideal a)
      isPartialorder:Ideal = record { antisym = ฮป p q โ incl ฮป f โ โจ p โฉ f , โจ q โฉ f }

-----------------------------------------------------------------------------------------
-- The zero ideal

module _ {๐ : ๐ฐ ๐}
         {{_ : isCategory {๐} ๐}}
         {{_ : isZeroMorphismCategory โฒ ๐ โฒ}}
         where
  -- private
  --   ๐ = โจ ๐' โฉ

-- module _ {๐} {๐ : ๐ฐ _} {{_ : ๐๐๐๐๐ญ ๐ on ๐}} where
  module _ {a : ๐} where
    record โฅ-Idealแต {b : ๐} (f : a โถ b) : ๐ฐ (๐ ๏ฝค ๐) where
      constructor incl
      field โจ_โฉ : f โผ pt

    open โฅ-Idealแต public

    macro
      โฅ-Ideal = #structureOn (ฮป {b} -> โฅ-Idealแต {b})


    instance
      isIdeal:โฅ-Ideal : isIdeal a โฅ-Idealแต
      isIdeal:โฅ-Ideal = record
        { transp-Ideal = ฮป fโผg (incl fโผpt) โ incl (fโผg โปยน โ fโผpt)
        ; ideal-r-โ     = ฮป (incl fโผpt) g โ incl ((fโผpt โ refl) โ absorb-l-โ)
        ; ideal-pt      = incl refl
        }

    initial-โฅ-Ideal : โ{I : Ideal a} -> โฒ (ฮป {b} -> โฅ-Idealแต {b}) โฒ โค I
    initial-โฅ-Ideal = incl ฮป f (incl fโผpt) โ transp-Ideal (fโผpt โปยน) ideal-pt



-----------------------------------------------------------------------------------------
-- The semilattice structure


-- module _ {๐' : ๐๐๐๐๐ญ ๐} where
module _ {๐ : ๐ฐ ๐}
         {{_ : isCategory {๐} ๐}}
         {{_ : isZeroMorphismCategory โฒ ๐ โฒ}}
         where
  -- private
  --   ๐ = โจ ๐' โฉ
  -- the meets
  module _ {a : ๐} (I J : Ideal a) where
    record _โง-Idealแต_ {b : ๐} (f : a โถ b) : ๐ฐ (๐ ๏ฝค ๐) where
      constructor _,_
      field fst : โจ I โฉ f
      field snd : โจ J โฉ f

    open _โง-Idealแต_ public

    macro
      _โง-Ideal_ = #structureOn (ฮป {b} -> _โง-Idealแต_ {b})

  module _ {a : ๐} {I J : Ideal a} where
    instance
      isIdeal:โง-Ideal : isIdeal a (I โง-Idealแต J)
      isIdeal:โง-Ideal = record
        { transp-Ideal = lem-1
        ; ideal-r-โ     = lem-2
        ; ideal-pt = ideal-pt , ideal-pt
        }
        where
          lem-1 : {b : ๐} {f g : a โถ b} โ f โผ g โ (I โง-Idealแต J) f โ (I โง-Idealแต J) g
          lem-1 p (A , B) = transp-Ideal p A , transp-Ideal p B

          lem-2 : {b : ๐} {f : a โถ b} โ (I โง-Idealแต J) f โ
                  {c : ๐} (g : b โถ c) โ (I โง-Idealแต J) (f โ g)
          lem-2 (A , B) g = ideal-r-โ A g , ideal-r-โ B g

  -- the top element
  module _ {a : ๐} where
    record โค-Idealแต {b : ๐} (f : a โถ b) : ๐ฐ (๐ ๏ฝค ๐) where
      constructor tt

    open โค-Idealแต public

    macro
      โค-Ideal = #structureOn (ฮป {b} -> โค-Idealแต {b})

    instance
      isIdeal:โค-Ideal : isIdeal a โค-Ideal
      isIdeal:โค-Ideal = record
        { transp-Ideal = ฮป p x โ tt
        ; ideal-r-โ     = ฮป x g โ tt
        }


    instance
      hasFiniteMeets:Ideal : hasFiniteMeets (Ideal a)
      hasFiniteMeets:Ideal = record
                                { โค = โค-Ideal
                                ; terminal-โค = incl ฮป f x โ tt
                                ; _โง_ = ฮป I J -> I โง-Ideal J
                                ; ฯโ-โง = incl ฮป f x โ x .fst
                                ; ฯโ-โง = incl ฮป f x โ x .snd
                                ; โจ_,_โฉ-โง = ฮป f g โ incl ฮป h x โ โจ f โฉ h x , โจ g โฉ h x
                                }

    module ยง-โง-Ideal where
      prop-1 : โ{n : โ} {P : Fin-R n -> Ideal a} -> {x : ๐} {f : a โถ x} -> โจ โ-fin P โฉ f -> โ i -> โจ P i โฉ f
      prop-1 {zero} {P} {x} {f} fโP ()
      prop-1 {suc n} {P} {x} {f} (fโP0 , _   ) zero = fโP0
      prop-1 {suc n} {P} {x} {f} (_    , fโPS) (suc i) = prop-1 fโPS i

      prop-2 : โ{n : โ} {P : Fin-R n -> Ideal a} -> {x : ๐} {f : a โถ x} -> (โ i -> โจ P i โฉ f) -> โจ โ-fin P โฉ f
      prop-2 {zero} {P} {x} {f} fโPi = tt
      prop-2 {suc n} {P} {x} {f} fโPi = fโPi zero , prop-2 (ฮป i -> fโPi (suc i))

      prop-3 : โ{n : โ} -> โ{b : ๐} -> {P : Fin-R n -> Ideal a} -> โจ โ-fin P โฉ (pt {a = a} {b})
      prop-3 {P = P} = ideal-pt {{_}} {{of โ-fin P}}

-----------------------------------------------------------------------------------------
-- The forward action

module _ {๐' : ๐๐๐๐๐ญ ๐} where
  private
    ๐ = โจ ๐' โฉ

  module _ {a b : ๐} (f : a โถ b) (I : Ideal b) where

    record _โทแต_ {x : ๐} (g : a โถ x) : ๐ฐ (๐) where
      constructor incl
      field โจ_โฉ : โ ฮป (h : b โถ x) -> โจ I โฉ h ร-๐ฐ (f โ h โผ g)

    open _โทแต_ public

    -- macro _โท_ = #structureOn (ฮป {x} -> _โทแต_ {x})


  module _ {a b : ๐} {h : a โถ b} {I : Ideal b} where
    instance
      isIdeal:โท : isIdeal a (h โทแต I)
      isIdeal:โท = record
        { transp-Ideal = lem-1
        ; ideal-r-โ     = lem-2
        ; ideal-pt = incl (pt , (ideal-pt , absorb-r-โ))
        }
        where
          lem-1 : {b : ๐} {f : a โถ b} {g : a โถ b} โ
                  f โผ g โ (h โทแต I) f โ (h โทแต I) g
          lem-1 fโผg (incl (e , eโI , heโผf)) = incl (e , (eโI , heโผf โ fโผg))

          lem-2 : {d : ๐} {f : a โถ d} โ (h โทแต I) f โ {c : ๐} (g : d โถ c) โ (h โทแต I) (f โ g)
          lem-2 {d} {f} (incl (e , eโI , heโผf)) {c} g =
            let P : h โ (e โ g) โผ f โ g
                P = h โ (e โ g)  โจ assoc-r-โ โฉ-โผ
                    (h โ e) โ g  โจ heโผf โ refl โฉ-โผ
                    f โ g        โ
            in incl (e โ g , (ideal-r-โ eโI g , P))

  infixr 30 _โท_
  _โท_ : โ{a b : ๐} -> (f : a โถ b) -> Ideal b -> Ideal a
  _โท_ f I = โฒ f โทแต I โฒ

  _โโทโ_ : โ{a b : ๐} -> {f g : a โถ b} -> f โผ g -> {I J : Ideal b} -> I โผ J -> f โท I โผ g โท J
  _โโทโ_ {a} {b} {f} {g} fโผg {I} {J} IโผJ = antisym
    (incl (ฮป h (incl (e , eโI , feโผh)) โ
      let eโJ : โจ J โฉ e
          eโJ = โจ IโผJ โฉ e .fst eโI
          geโผh : g โ e โผ h
          geโผh = (fโผg โปยน โ refl) โ feโผh
      in incl (e , (eโJ , geโผh))
    ))
    (incl (ฮป h (incl (e , eโJ , geโผh)) โ
      let eโI : โจ I โฉ e
          eโI = โจ IโผJ โปยน โฉ e .fst eโJ
          feโผh : f โ e โผ h
          feโผh = (fโผg โ refl) โ geโผh
      in incl (e , (eโI , feโผh))
    ))

  assoc-l-โท : โ{a b c : ๐} {f : a โถ b} {g : b โถ c} -> {I : Ideal c} -> (f โ g) โท I โผ f โท (g โท I)
  assoc-l-โท {a} {b} {c} {f} {g} {I} = antisym
    (incl (ฮป h (incl (e , eโI , fgeโผh)) โ incl (g โ e , ((incl (e , (eโI , refl))) , assoc-r-โ โ fgeโผh))))
    (incl ฮป h (incl (ge' , (incl (e , eโI , geโผge')) , fge'โผh)) โ incl (e , (eโI ,
      let P : f โ g โ e โผ h
          P = assoc-l-โ โ (refl โ geโผge') โ fge'โผh
      in P
      )))



-----------------------------------------------------------------------------------------
-- The inverse action

module _ {๐' : ๐๐๐๐๐ญ ๐} where
  private
    ๐ = โจ ๐' โฉ

  record _โปยนโทแต_ {a b : ๐} (f : a โถ b) (I : Ideal a) {x : ๐} (g : b โถ x) : ๐ฐ (๐) where
    constructor incl
    field โจ_โฉ : โจ I โฉ (f โ g)

  open _โปยนโทแต_ public


  infixr 30 _โปยนโท_
  _โปยนโท_ : โ{a b : ๐} -> (h : a โถ b) -> Ideal a -> Ideal b
  _โปยนโท_ {a} {b} h I = (h โปยนโทแต I) since P
    where
      lem-1 : {c : ๐} {f : b โถ c} {g : b โถ c} โ
              f โผ g โ (h โปยนโทแต I) f โ (h โปยนโทแต I) g
      lem-1 {c} {f} {g} fโผg (incl fโhI) = incl (transp-Ideal (refl โ fโผg) fโhI)

      lem-2 : {d : ๐} {f : b โถ d} โ
                (h โปยนโทแต I) f โ {c : ๐} (g : d โถ c) โ (h โปยนโทแต I) (f โ g)
      lem-2 {d} {f} (incl fโhI) {c} g =
        let P : โจ I โฉ ((h โ f) โ g)
            P = ideal-r-โ fโhI g
            Q : โจ I โฉ (h โ (f โ g))
            Q = transp-Ideal assoc-l-โ P
        in incl Q

      P : isIdeal b _
      P = record
          { transp-Ideal = lem-1
          ; ideal-r-โ = lem-2
          ; ideal-pt = incl (transp-Ideal (absorb-r-โ โปยน) ideal-pt)
          }

  inv-โท-r : {a b : ๐} {f : a โถ b} -> {I : Ideal a} -> f โท (f โปยนโท I) โผ I โง (f โท โค-Ideal)
  inv-โท-r {a} {b} {f} {I} = antisym
    (incl (ฮป h (incl (e , incl eโfโปยนI , feโผh)) โ transp-Ideal (feโผh) (eโfโปยนI)  , (incl (e , (tt , feโผh)))))
    (incl ฮป h (hโI , incl (e , tt , feโผh)) โ incl (e , (incl (transp-Ideal (feโผh โปยน) hโI) , feโผh)))


-----------------------------------------------------------------------------------------
-- Epi principal

module _ {๐' : ๐๐๐๐๐ญ ๐} {{_ : isSizedCategory โฒ โจ ๐' โฉ โฒ}} where

  private
    ๐ = โจ ๐' โฉ

  isZeroOrEpi : โ{a b : ๐} -> (f : a โถ b) -> ๐ฐ _
  isZeroOrEpi f = (f โผ pt) +-๐ฐ (isEpi f)

  isZeroOrEpi:โ : โ{a b c : ๐} -> {f : a โถ b} {g : b โถ c} -> isZeroOrEpi f -> isZeroOrEpi g
                  -> isZeroOrEpi (f โ g)
  isZeroOrEpi:โ (left fโผpt) q = left ((fโผpt โ refl) โ absorb-l-โ)
  isZeroOrEpi:โ (just x) (left gโผpt) = left ((refl โ gโผpt) โ absorb-r-โ)
  isZeroOrEpi:โ (just x) (just y) = just (isEpi:โ x y)

-- module _ {๐ : ๐ฐ ๐} {{_ : isCategory {๐} ๐}} where
  module _ {a : ๐} where
    record isEpiPrincipal (I : Ideal a) : ๐ฐ (๐) where
      field repObj : ๐
      field rep : a โถ repObj
      field principal-r : I โผ rep โท โค-Ideal
      field isGoodRep : isGood rep
      field zeroOrEpi : isZeroOrEpi rep
      -- field factorPrinc : โ{x} -> (f : a โถ x) -> โจ I โฉ f -> โ ฮป (g : repObj โถ x) -> f โผ rep โ g

    open isEpiPrincipal {{...}} public

    repObjOf : (I : Ideal a) {{_ : isEpiPrincipal I}} -> ๐
    repObjOf I = repObj

    repOf : (I : Ideal a) {{_ : isEpiPrincipal I}} -> a โถ repObjOf I
    repOf I = rep

    instance
      isEpiPrincipal:โค : isEpiPrincipal โค
      isEpiPrincipal:โค = record
        { repObj = a
        ; rep = id
        ; principal-r = antisym lem-1 terminal-โค
        ; isGoodRep = right (left (incl refl))
        ; zeroOrEpi = right (isEpi:id)
        }
        where
          lem-1 : โค โค (id โท โค)
          lem-1 = incl ฮป f x โ incl (f , (x , unit-l-โ))

    transp-isEpiPrincipal : โ{I J : Ideal a} -> (I โผ J) -> isEpiPrincipal I -> isEpiPrincipal J
    transp-isEpiPrincipal {I} {J} IโผJ P =
      let
        instance _ = P
      in record
        { repObj = repObjOf I
        ; rep = repOf I
        ; principal-r = IโผJ โปยน โ principal-r
        ; isGoodRep = isGoodRep
        ; zeroOrEpi = zeroOrEpi
        }

    instance
      isEpiPrincipal:โฅ : isEpiPrincipal โฅ-Ideal
      isEpiPrincipal:โฅ = record
        { repObj = a
        ; rep = pt
        ; principal-r = antisym initial-โฅ-Ideal lem-1
        ; isGoodRep = left (incl refl)
        ; zeroOrEpi = left refl
        }
        where
          lem-1 : (pt {a = a} {a} โท โค-Ideal) โค โฅ-Ideal
          lem-1 = incl ฮป f (incl (e , tt , ptโeโผf)) โ incl (ptโeโผf โปยน โ absorb-l-โ)

    module ยง-EpiPrincipalแตฃ where

      prop-1 : โ{I : Ideal a} {{_ : isEpiPrincipal I}} -> repOf I โผ pt -> I โผ โฅ-Ideal
      prop-1 {I} p = principal-r โ (p โโทโ refl) โ P
        where
          P : (pt {a = a} {repObjOf I} โท โค-Ideal) โผ โฅ-Ideal
          P = antisym
              (incl (ฮป f (incl (e , _ , ptโeโผf)) โ
                let ptโผf : pt โผ f
                    ptโผf = absorb-l-โ โปยน โ ptโeโผf
                in incl (ptโผf โปยน)
              ))
              initial-โฅ-Ideal

      prop-2 : โ{I : Ideal a} {{_ : isEpiPrincipal I}} -> โจ I โฉ (repOf I)
      prop-2 {I} {{IP}} = โจ by-โผ-โค (principal-r {{IP}} โปยน) โฉ _ (incl (id , (tt , unit-r-โ)))

