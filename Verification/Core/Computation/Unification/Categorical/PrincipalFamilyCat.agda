
module Verification.Core.Computation.Unification.Categorical.PrincipalFamilyCat where

open import Verification.Conventions

open import Verification.Core.Set.Induction.WellFounded
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Subsetoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.List.Variant.Binary.Natural
-- open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.WellFounded.Construction.Lexicographic
open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Computation.Unification.Categorical.PrincipalFamily
open import Verification.Core.Computation.Unification.Categorical.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Free
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Coequalizer
-- open import Verification.Core.Theory.Presentation.Signature.Definition


-- module _ {M : π° π} {{_ : Monoidβ (π , π) on M}} where

--   record CoeqSolutions' (f g h : M) : π° π where
--     constructor incl
--     field β¨_β© : f β h βΌ g β h
--   open CoeqSolutions' public

--   CoeqSolutions : (f g : M) -> π« M
--   CoeqSolutions f g = Ξ» h -> β£ CoeqSolutions' f g h β£

-- module _ {π : π° π} {{_ : isCategory {π} π}} where
--   record hasProperty-isCoeq {a b x : π} (f : (a βΆ b) ^ 2) (h : b βΆ x) : π° (π ο½€ π) where
--     constructor incl
--     field β¨_β© : fst f β h βΌ snd f β h

-- module _ {M : Monoidβ (π , π)} {f g : β¨ M β©} where
--   instance
--     isSubsetoid:CoeqSolutions : isSubsetoid (CoeqSolutions f g)
--     isSubsetoid.transp-βΌ isSubsetoid:CoeqSolutions (p) (incl P) = incl ((refl βββ p β»ΒΉ) β P β (refl βββ p))

--   instance
--     isIdeal-r:CoeqSolutions : isIdeal-r M β²(CoeqSolutions f g)β²
--     isIdeal-r.ideal-r-β isIdeal-r:CoeqSolutions {h} (incl P) i =
--       let Pβ : f β (h β i) βΌ g β (h β i)
--           Pβ = f β (h β i)   β¨ assoc-r-β β©-βΌ
--                 (f β h) β i   β¨ P βββ refl β©-βΌ
--                 (g β h) β i   β¨ assoc-l-β β©-βΌ
--                 g β (h β i)   β
--       in incl Pβ
--     isIdeal-r.ideal-β isIdeal-r:CoeqSolutions = incl (absorb-r-β β absorb-r-β β»ΒΉ)
-- -- private
-- module _ {π : π° π} {{_ : isCategory {π} π}} where
--   Pair : (a b : π) -> π° _
--   Pair a x = Hom a x Γ-π° Hom a x

IxC : (π : Category π) -> π° _
IxC π = β Ξ» (a : β¨ π β©) -> β Ξ» b -> HomPair a b

-- module _ (π : Category π) {{_ : isSizedCategory π}} where
--   πC : (i : IxC π) -> Ideal {π = Free-πππππ­ π} (incl (fst (snd i)))
--   πC (_ , _ , f , g) = asIdeal (f , g)
  -- β² (CoeqSolutions (arrow f) (arrow g)) β²

-- module _ {π : π° π} {{_ : isCategory {π} π}} {{_ : isDiscrete π}} {{_ : isSet-Str π}} where
  -- data isPrincipalC {a b : π} (f g : a βΆ b) : π° π where
  --   solved : hasCoequalizer f g
  --   field princobj : 




module _ (π : SizedHomPairCategory π) where
  record isSplittableC (n : β) {a b : β¨ π β©} (f : (a βΆα΅ b) ^ 2) : π° π where
    field famC : Fin-R n -> β Ξ» a' -> (HomPair a' b)
    field coversC : β{x} -> (h : b βΆ x) -> (f β 0 β h βΌ f β 1 β h) β (β p -> (famC p .snd) β 0 β h βΌ (famC p .snd) β 1 β h)
    -- field coversC : β-fin (Ξ» i -> πC π (famC i)) βΌ πC π i
    field fampropsC : β k -> sizeC (famC k .snd) βͺ sizeC f
    -- P (_ , _ , f) (_ , _ , famC k .snd)
  open isSplittableC public

record isPrincipalFamilyCat (π : SizedHomPairCategory π) : π° (π βΊ) where
  field isBase : β{a x : β¨ π β©} -> (HomPair a x) -> π° (π β 1)
  field βC : β{x y : β¨ π β©} -> (i : HomPair x y)
           -> (isBase i +-π° (β Ξ» n -> isSplittableC π n i))
  field isPrincipalC:Base : β{a b : β¨ π β©} -> β(f g : a βΆ b) -> isBase (f , g) -> hasSizedCoequalizerDecision (f , g)

open isPrincipalFamilyCat {{...}} public

module _ {π : Category π}
         {{SP : isSizedCategory π}}
         {{SP2 : isSizedHomPairCategory β² β¨ π β© β²}}
         {{_ : isPrincipalFamilyCat β² β¨ π β© β²}} where

  private
    Ix : β(a : Free-πππππ­ π) -> π° _
    Ix (incl x) = Bool +-π° (β Ξ» (a : β¨ π β©) -> HomPair a x)

    Bx : β(a : Free-πππππ­ π) -> π° _
    Bx (incl x) = Bool +-π° (β Ξ» (a : β¨ π β©) -> β isBase {a = a} {x})

    π·' : β{a} -> Bx a -> Ix a
    π·' (left x) = left x
    π·' (just (x , (f , g) , p)) = just (x , (f , g))

    π' : β{a} -> Ix a -> Ideal a
    π' (left false) = β₯-Ideal
    π' (left true) = β€-Ideal
    π' (just (_ , (f , g))) = asIdeal (f , g)

    Size' : WFT (ββ , ββ)
    Size' = Lexi β¨ SizeO {{SP}} β© β¨ SizeC {{SP2}} β©

    size' : β{a} -> Ix a -> β¨ Size' β©
    size' {a} (left x) = β₯-WFT
    size' {a} (just (x , (f , g))) = sizeO a , sizeC (f , g)

  instance
    hasSizedFamily:byIsPrincipalFamilyCat : hasSizedFamily _ β²(Free-πππππ­ π)β²
    hasSizedFamily:byIsPrincipalFamilyCat = record
      { Base = Bx
      ; Ind = Ix
      ; π· = π·'
      ; π = π'
      ; Size = Size'
      ; size = size'
      }

  private
    inv : {a b : Free-πππππ­ π} β a βΆ b β Ix a β Ix b
    inv (zero) _ = left true
    inv (some h) (left x) = left x
    inv (some h) (just (x , (f , g))) = just (x , (f β h , g β h))

    size-inv : {a b : Free-πππππ­ π} (g : a βΆ b) -> isGood g -> (i : Ix a) β size' (inv g i) βͺ£ size' i
    size-inv (some x) good (left y) = left refl-β£
    size-inv (some x) (left (incl ())) (just xβ)
    size-inv (some x) (just (left (incl (some xβΌid)))) (just (_ , (f , g))) = left (congβ-Str _,_ refl-β£ (cong-sizeC (f β x , g β x) (f , g) ((refl β xβΌid) β unit-r-β , (refl β xβΌid) β unit-r-β)))
    size-inv (some x) (just (just good)) (just xβ) = right (first good)
    size-inv zero good i = initial-β₯-WFT

    lem-1 : {a b : Free-πππππ­ π} {g : a βΆ b} {i : Ix a} β π' (inv g i) βΌ-Ideal (g β»ΒΉβ· π' i)
    lem-1 {a} {b} {zero} {left false} = antisym P terminal-β€
      where
        P : β€ β€ (zero β»ΒΉβ· β₯-Ideal)
        β¨ P β© f x = incl (incl refl)
    lem-1 {a} {b} {zero} {left true} = antisym P terminal-β€
      where
        P : β€ β€ (zero β»ΒΉβ· β€)
        β¨ P β© f x = incl tt
    lem-1 {a} {b} {zero} {just (_ , (f , g))} = antisym P terminal-β€
      where
        P : β€ β€ (zero β»ΒΉβ· asIdeal (f , g))
        P = incl (Ξ» fβ x β incl ideal-pt)
    lem-1 {a} {b} {some x} {left false} = antisym initial-β₯-Ideal P
      where
        P : (some x β»ΒΉβ· β₯-Ideal) β€ β₯-Ideal
        β¨ P β© zero x = ideal-pt
    lem-1 {a} {b} {some x} {left true} = antisym P terminal-β€
      where
        P : β€ β€ (some x β»ΒΉβ· β€)
        P = incl (Ξ» f xβ β incl tt)
    lem-1 {a} {b} {some x} {just (_ , (f , g))} = antisym P Q
      where
        P : asIdeal (f β x , g β x) β€ (some x β»ΒΉβ· asIdeal (f , g))
        P = incl (Ξ» fβ (incl p) β incl (incl (assoc-r-β β p β assoc-l-β)))

        Q : (some x β»ΒΉβ· asIdeal (f , g)) β€ asIdeal (f β x , g β x)
        Q = incl (Ξ» fβ (incl (incl p)) β incl (assoc-l-β β p β assoc-r-β))

    lem-2 : {a : Free-πππππ­ π} (b : Bx a) β isEpiPrincipal (π' (π·' b))
    lem-2 (left false) = isEpiPrincipal:β₯
    lem-2 (left true) = isEpiPrincipal:β€
    lem-2 (just (x , (f , g) , isbase)) = Forward (isPrincipalC:Base f g isbase)

    lem-3 : β{a b : β¨ π β©} {f g : a βΆ b} -> isSplittableC β² β¨ π β© β² n (f , g)
          -> isSplittable n (right (_ , (f , g)))
    lem-3 {n} {a} {b} {f} {g} S = record
      { fam = fam'
      ; covers = antisym coversβ coversβ
      ; famprops = Ξ» k β second (fampropsC S k)
      }
      where
        fam' : Fin-R n β Ix (incl b)
        fam' i = right (famC S i)

        coversβ : β-fin (Ξ» i β asIdeal (fst (snd (famC S i)) , snd (snd (famC S i))))
                  β€ asIdeal (f , g)
        β¨ coversβ β© zero hβP = ideal-pt
        β¨ coversβ β© (some h) hβP = incl (some (coversC S (h) .snd Q))
          where
            Q : β(i : Fin-R n) -> (fst (snd (famC S i)) β h) βΌ (snd (snd (famC S i)) β h)
            Q i with β¨ Β§-β§-Ideal.prop-1 hβP i β©
            ... | some p = p

        coversβ : asIdeal (f , g)
                  β€ β-fin (Ξ» i β asIdeal (fst (snd (famC S i)) , snd (snd (famC S i))))
        β¨ coversβ β© zero hβP = Β§-β§-Ideal.prop-3 {P = (Ξ» i β asIdeal (fst (snd (famC S i)) , snd (snd (famC S i))))}
        β¨ coversβ β© (some h) (incl (some hβP)) = Β§-β§-Ideal.prop-2 {P = Ξ» i β asIdeal (fst (snd (famC S i)) , snd (snd (famC S i)))} Ξ» i β incl (some (coversC S h .fst hβP i))

    lem-4 : {a : Free-πππππ­ π} (i : Ix a) β
            (β (Ξ» b β π' (π·' b) βΌ-Ideal π' i)) +-π°
            (β (Ξ» n β isSplittable n i))
    lem-4 (left x) = left (left x , refl)
    lem-4 (just (x , (f , g))) with βC (f , g)
    ... | left isbase:fg = left ((right (x , (f , g) , isbase:fg)) , refl)
    ... | just (n , splittable) = right (n , lem-3 splittable)

  instance
    hasPrincipalFamily:byIsPrincipalFamilyCat : hasPrincipalFamily β²(Free-πππππ­ π)β²
    hasPrincipalFamily:byIsPrincipalFamilyCat = record
                                                  { _β»ΒΉ*_ = inv
                                                  ; size:β»ΒΉ* = size-inv
                                                  ; preserves-π:β»ΒΉ* = lem-1
                                                  ; principalBase = lem-2
                                                  ; β = lem-4
                                                  }

  isEpiPrincipal:byPrincipalFamilyCat : β{a b : β¨ π β©} {f g : a βΆ b} -> isEpiPrincipal (asIdeal (f , g))
  isEpiPrincipal:byPrincipalFamilyCat {a} {b} {f} {g} = isPrincipal:Family (Free-πππππ­ π) _ (just (a , (f , g))) refl-β£

  instance
    hasSizedCoequalizerDecision:byPrincipalFamilyCat : β{a b : β¨ π β©} {f g : a βΆ b} -> hasSizedCoequalizerDecision (f , g)
    hasSizedCoequalizerDecision:byPrincipalFamilyCat = Backward isEpiPrincipal:byPrincipalFamilyCat

  hasUnification:byPrincipalFamilyCat : hasUnification π
  hasUnification:byPrincipalFamilyCat = hasUnification:byHasSizedCoequalizerDecision




