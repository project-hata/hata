
module Verification.Core.Computation.Unification.Categorical2.EpiPrincipal where

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
open import Verification.Core.Computation.Unification.Categorical2.ForwardAction
open import Verification.Core.Computation.Unification.Categorical2.SemilatticeStructure
open import Verification.Core.Computation.Unification.Categorical2.ZeroIdeal

-- [Hide]

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

module _ {๐' : ๐๐๐๐๐ญ ๐} {{_ : isSizedCategory โฒ โจ ๐' โฉ โฒ}} where
  private
    ๐ = โจ ๐' โฉ
    variable a b c : ๐
-- //

-- ===* Epi-principal ideals
-- | We have seen that an epimorphism |ฯ : a โถ b| such that |I โผ ฯ โท โค|
--   captures the notion of a coequalizer. It would be useful if we could
--   say that, given some ideal |I|, the goal of unification is to find exactly such an
--   epimorphism |ฯ|. But there is one problem:
--   If |t| and |s| are not unifiable, then |I| is the zero ideal.
--   We then have |I โผ pt โท โค|. But, even though |pt| fulfills this equation,
--   it is not an epimorphism: |pt โ f โผ pt โ g| does not imply |f โผ g|.
--   Thus, we have to relax the requirement on |ฯ|, we define the following:


  isZeroOrEpi : (f : a โถ b) -> ๐ฐ _
  isZeroOrEpi f = (f โผ pt) +-๐ฐ (isEpi f)

  -- [Hide]
  isZeroOrEpi:โ : โ{a b c : ๐} -> {f : a โถ b} {g : b โถ c} -> isZeroOrEpi f -> isZeroOrEpi g
                  -> isZeroOrEpi (f โ g)
  isZeroOrEpi:โ (left fโผpt) q = left ((fโผpt โ refl) โ absorb-l-โ)
  isZeroOrEpi:โ (just x) (left gโผpt) = left ((refl โ gโผpt) โ absorb-r-โ)
  isZeroOrEpi:โ (just x) (just y) = just (isEpi:โ x y)
  -- //


-- [Definition]
-- | Let |I| be an ideal at |a|. We say that it
--   is /epi-principal/ if the following data is
--   given: []
  record isEpiPrincipal (I : Ideal a) : ๐ฐ (๐) where
    -- | 1. An object [..].
    field repObj : ๐
    -- | 2. An arrow [..] said to be representing this ideal.
    field rep : a โถ repObj
    -- | 3. Such that the equation [..] holds.
    field principal-r : I โผ rep โท โค
    -- | 4. Finally, we want the representing arrow
    --      to be either zero, or an epimorphism.
    field zeroOrEpi : isZeroOrEpi rep
    -- //


-- [Hide]
    field isGoodRep : isGood rep

    -- field factorPrinc : โ{x} -> (f : a โถ x) -> โจ I โฉ f -> โ ฮป (g : repObj โถ x) -> f โผ rep โ g

  open isEpiPrincipal {{...}} public

  repObjOf : (I : Ideal a) {{_ : isEpiPrincipal I}} -> ๐
  repObjOf I = repObj

  repOf : (I : Ideal a) {{_ : isEpiPrincipal I}} -> a โถ repObjOf I
  repOf I = rep

  module _ {a : ๐} where
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

-- //


