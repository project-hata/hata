
module Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2 where

open import Verification.Conventions

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Category.As.Monoid
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Subsetoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Core.Theory.Presentation.Signature.Definition


module _ {M : π° π} {{_ : Monoidβ (π , π) on M}} where

  record CoeqSolutions' (f g h : M) : π° π where
    constructor incl
    field β¨_β© : f β h βΌ g β h
  open CoeqSolutions' public

  CoeqSolutions : (f g : M) -> π« M
  CoeqSolutions f g = Ξ» h -> β£ CoeqSolutions' f g h β£

module _ {π : π° π} {{_ : isCategory {π} π}} where
  record hasProperty-isCoeq {a b x : π} (f : (a βΆ b) ^ 2) (h : b βΆ x) : π° (π ο½€ π) where
    constructor incl
    field β¨_β© : fst f β h βΌ snd f β h

module _ {M : Monoidβ (π , π)} {f g : β¨ M β©} where
  instance
    isSubsetoid:CoeqSolutions : isSubsetoid (CoeqSolutions f g)
    isSubsetoid.transp-βΌ isSubsetoid:CoeqSolutions (p) (incl P) = incl ((refl βββ p β»ΒΉ) β P β (refl βββ p))

  instance
    isIdeal-r:CoeqSolutions : isIdeal-r M β²(CoeqSolutions f g)β²
    isIdeal-r.ideal-r-β isIdeal-r:CoeqSolutions {h} (incl P) i =
      let Pβ : f β (h β i) βΌ g β (h β i)
          Pβ = f β (h β i)   β¨ assoc-r-β β©-βΌ
                (f β h) β i   β¨ P βββ refl β©-βΌ
                (g β h) β i   β¨ assoc-l-β β©-βΌ
                g β (h β i)   β
      in incl Pβ
    isIdeal-r.ideal-β isIdeal-r:CoeqSolutions = incl (absorb-r-β β absorb-r-β β»ΒΉ)
-- private
module _ {π : π° π} {{_ : isCategory {π} π}} where
  Pair : (a b : π) -> π° _
  Pair a x = Hom a x Γ-π° Hom a x

IxC : (π : Category π) -> π° _
IxC π = β Ξ» (a : β¨ π β©) -> β Ξ» b -> Pair a b

module _ (π : Category π) {{_ : isDiscrete β¨ π β©}} {{_ : isSet-Str β¨ π β©}} where
  πC : (i : IxC π) -> Ideal-r β²(PathMon π)β²
  πC (_ , _ , f , g) = β² (CoeqSolutions (arrow f) (arrow g)) β²

-- module _ {π : π° π} {{_ : isCategory {π} π}} {{_ : isDiscrete π}} {{_ : isSet-Str π}} where
  -- data isPrincipalC {a b : π} (f g : a βΆ b) : π° π where
  --   solved : hasCoequalizer f g
  --   field princobj : 




module _ (π : SizedCategory π) where
  record isSplittableC (n : δΊΊβ) {a b : β¨ π β©} (f : (a βΆ b) ^ 2) : π° π where
    field famC : n β tt -> β Ξ» a' -> (Pair a' b)
    field coversC : β{x} -> (h : b βΆ x) -> (f β 0 β h βΌ f β 1 β h) β (β p -> (famC p .snd) β 0 β h βΌ (famC p .snd) β 1 β h)
    -- field coversC : β-fin (Ξ» i -> πC π (famC i)) βΌ πC π i
    field fampropsC : β k -> sizeC (famC k .snd) βͺ sizeC f
    -- P (_ , _ , f) (_ , _ , famC k .snd)
  open isSplittableC public

record isPrincipalFamilyCat (π : SizedCategory π) : π° (π βΊ) where
  field isBase : β{a x : β¨ π β©} -> (Pair a x) -> π° (π β 1)
  field βC : β{x y : β¨ π β©} -> (i : Pair x y)
           -> (isBase i +-π° (β Ξ» n -> isSplittableC π n i))
  field isPrincipalC:Base : β{a b : β¨ π β©} -> β(f g : a βΆ b) -> isBase (f , g) -> Β¬ (hasCoequalizer f g) +-π° (hasReducingCoequalizer f g)

open isPrincipalFamilyCat {{...}} public

{-
module _ (π : Category π) {{_ : isDiscrete β¨ π β©}} {{_ : isSet-Str β¨ π β©}} where
  record isSplittableC (n : δΊΊβ) {a b : β¨ π β©} (f : (a βΆ b) ^ 2) (P : IxC π -> IxC π -> π°β) : π° π where
    field famC : n β tt -> β Ξ» a' -> (Pair a' b)
    field coversC : β{x} -> (h : b βΆ x) -> (f β 0 β h βΌ f β 1 β h) β (β p -> (famC p .snd) β 0 β h βΌ (famC p .snd) β 1 β h)
    -- field coversC : β-fin (Ξ» i -> πC π (famC i)) βΌ πC π i
    field fampropsC : β k -> P (_ , _ , f) (_ , _ , famC k .snd)
  open isSplittableC public

record isPrincipalFamilyCat (π : Category π) {{_ : isDiscrete β¨ π β©}} {{_ : isSet-Str β¨ π β©}} : π° (π βΊ) where
  field SizeC : WFT (ββ , ββ)
  field isBase : β{a x : β¨ π β©} -> (Pair a x) -> π° (π β 1)
  field sizeC : {a x : β¨ π β©} -> (Pair a x) -> β¨ SizeC β©

  -- field SizeCF : WFT (ββ , ββ)
  -- field sizeC : (x : β¨ π β©) -> β¨ SizeC β©
  -- field sizeCF : {x : β¨ π β©} -> (Pair a x) -> β¨ SizeCF β©
  -- field _βͺ_ : SizeC -> SizeC -> π°β
  -- field trans-SizeC : β{a b c} -> a βͺ b -> b βͺ c -> a βͺ c
  -- field isWellFounded:SizeC : WellFounded _βͺ_
  -- _βͺ£_ : SizeC -> SizeC -> π°β
  -- a βͺ£ b = (a β‘-Str b) β¨ (a βͺ b)

  field βC : β{x y : β¨ π β©} -> (i : Pair x y)
           -> (isBase (i)
              +-π° (β Ξ» n -> isSplittableC π n i (Ξ» (_ , _ , i) -> Ξ» (_ , _ , j) -> sizeC j βͺ sizeC i)))

  field size0 : β¨ SizeC β©
  field initial-size0 : β{a} -> size0 βͺ£ a
  field isPrincipalC:Base : β{a b : β¨ π β©} -> β(f g : a βΆ b) -> isBase (f , g) -> isDecidable (hasCoequalizer f g)
  -}


data Side : π°β where
  isLeft isRight : Side

module _ (π : Category (π , π , π)) {{X : isSizedCategory π}} {{F : isPrincipalFamilyCat β² β¨ π β© β²}} where
  private

    -- Ix generates our ideals
    -- Bx determines those which are base ideals, and thus trivially principal/good/+
    -- If Ix is nothing, this means that this is the whole monoid, i.e., the
    -- two arrows are already equal, we have no constraints

    Ix = Maybe (β Ξ» (a : β¨ π β©) -> β Ξ» (x : β¨ π β©) -> Pair a x)
    Bx = Maybe (β Ξ» (a : β¨ π β©) -> β Ξ» (x : β¨ π β©) -> β isBase {a = a} {x})
    -- Side Γ-π° ((β isBase a x) β§ Hom a x))

    -- record isSplittableCat (n : β) (i : Ix) (P : I -> π°β) : π° (π ο½€ π βΊ) where
    --   field fam : Fin-R n -> I
    --   field covers : β-fin (Ξ» i -> π (fam i)) βΌ π i
    --   field famprops : β k -> P (fam k)
    -- open isSplittable public

    size' : Ix -> β¨ SizeC β©
    size' nothing = β₯-WFT
    size' (just (a , x , f)) = sizeC f

    bb : Bx -> Ix
    bb nothing = nothing
    bb (just (x , a , (f , g) , _)) = just (x , a , (f , g))
    -- bb (just (x , a , isLeft , ((h , _) , f)))  = just (x , a , h , f)
    -- bb (just (x , a , isRight , ((h , _) , f))) = just (x , a , f , h)


    M : Monoidβ _
    M = β² PathMon π β²

    π : Ix -> Ideal-r M
    π nothing = β€
    π (just (_ , _ , f , g)) = β²(CoeqSolutions (arrow f) (arrow g))β²

    Good : π« (PathMon π)
    Good [] = β€
    Good idp = β€
    Good (arrow {x} {y} h) = β£ (β(a : β¨ π β©) -> (f g : a βΆ x) -> sizeC (f β h , g β h) βͺ sizeC (f , g)) β£


    _β»ΒΉ'_ : β¦ Good β¦ -> Ix -> Ix
    _β»ΒΉ'_ (a) nothing = nothing
    _β»ΒΉ'_ ([] β’ _) (just _) = nothing
    _β»ΒΉ'_ (idp β’ _) (just x) = just x
    _β»ΒΉ'_ (arrow {a} {b} h β’ _) (just (y , x , (f , g))) with (x β-Str a)
    ... | yes refl-β£ = just (y , b , (f β h) , (g β h))
    ... | no Β¬p = nothing

    lem-100 : {a b : PathMon π} β a βΌ-PathMon b β a β Good β b β Good
    lem-100 idp = id-π°
    lem-100 [] = id-π°
    lem-100 (arrow p) = {!!}

    instance
      isSubsetoid:Good : isSubsetoid Good
      isSubsetoid:Good = record { transp-βΌ = lem-100 }
      -- isSubsetoid.transp-βΌ isSubsetoid:Good (incl idp) P = tt
      -- isSubsetoid.transp-βΌ isSubsetoid:Good (incl []) P = P
      -- isSubsetoid.transp-βΌ isSubsetoid:Good (incl (arrow fβΌg)) (β₯ p) = β₯ p

      isSubmonoid:Good : isSubmonoid β² Good β²
      isSubmonoid:Good = record { closed-β = tt ; closed-β = {!!} }
      -- isSubmonoid.closed-β isSubmonoid:Good = tt
      -- isSubmonoid.closed-β isSubmonoid:Good {idp} {b} p1 p2 = p2
      -- isSubmonoid.closed-β isSubmonoid:Good {[]} {b} p1 p2 = p1
      -- isSubmonoid.closed-β isSubmonoid:Good {arrow f} {[]} p1 p2 = p2
      -- isSubmonoid.closed-β isSubmonoid:Good {arrow f} {idp} p1 p2 = p1
      -- isSubmonoid.closed-β isSubmonoid:Good {arrow {a} {b} f} {arrow {c} {d} g} (β₯ p1) (β₯ p2) with (b β-Str c)


    lem-10 : (g : β¦ Good β¦) (i : Ix) β (size' (g β»ΒΉ' i) βͺ£ size' i)
    lem-10 g nothing = left refl-β£
    lem-10 ([] β’ gp) (just x) = elim-β₯-WFT
    lem-10 (idp β’ gp) (just x) = left refl-β£
    lem-10 (arrow {a} {b} h β’ (hp)) (just (y , x , f , g)) with (x β-Str a)
    ... | no Β¬p = elim-β₯-WFT
    ... | yes refl-StrId = right (hp _ f g)

    lem-20 : {g : β¦ Good β¦} {i : Ix} β π (g β»ΒΉ' i) βΌ (β¨ g β© β»ΒΉβ·-Ide π i)
    lem-20 = {!!}
    -- lem-20 {g β’ gp} {nothing} = unit-r-β»ΒΉβ·-Ide β»ΒΉ
    -- lem-20 {[] β’ gp} {just (x , (f , g))} = absorb-l-β»ΒΉβ·-Ide β»ΒΉ
    -- lem-20 {idp β’ gp} {just (x , (f , g))} = unit-l-β»ΒΉβ·-Ide β»ΒΉ
    -- lem-20 {arrow {a} {b} h β’ gp} {just (x , (f , g))} with (x β-Str a)
    -- ... | no Β¬p =
    --   let Pβ : β€ β€ ((arrow h) β»ΒΉβ·-Ide β²(CoeqSolutions (arrow f) (arrow g))β²)
    --       Pβ = incl (Ξ» {a} xβ β incl (incl (
    --                 arrow f β (arrow h β a)    β¨ assoc-r-β {a = arrow f} {b = arrow h} β©-βΌ
    --                 (arrow f β arrow h) β a    β¨ PathMon-non-matching-arrows Β¬p f h βββ refl β©-βΌ
    --                 [] β a                     β¨ PathMon-non-matching-arrows Β¬p g h β»ΒΉ βββ refl β©-βΌ
    --                 (arrow g β arrow h) β a    β¨ assoc-l-β {a = arrow g} {b = arrow h} β©-βΌ
    --                 arrow g β (arrow h β a)    β
    --            )))
    --   in antisym Pβ terminal-β€
    -- ... | yes refl-StrId =
    --   let Pβ : β²(CoeqSolutions (arrow (f β h)) (arrow (g β h)))β² β€ ((arrow h) β»ΒΉβ·-Ide β²(CoeqSolutions (arrow f) (arrow g))β²)
    --       Pβ = incl (Ξ» {a} (incl P) β incl (incl (
    --                 arrow f β (arrow h β a)    β¨ assoc-r-β {a = arrow f} {b = arrow h} β©-βΌ
    --                 (arrow f β arrow h) β a    β¨ functoriality-arrow f h β»ΒΉ βββ refl β©-βΌ
    --                 (arrow (f β h)) β a        β¨ P β©-βΌ
    --                 (arrow (g β h)) β a        β¨ functoriality-arrow g h βββ refl β©-βΌ
    --                 (arrow g β arrow h) β a    β¨ assoc-l-β {a = arrow g} {b = arrow h} β©-βΌ
    --                 arrow g β (arrow h β a)    β
    --            )))
    --       Pβ : ((arrow h) β»ΒΉβ·-Ide β²(CoeqSolutions (arrow f) (arrow g))β²) β€ β²(CoeqSolutions (arrow (f β h)) (arrow (g β h)))β²
    --       Pβ = incl (Ξ» {a} (incl (incl P)) β incl (
    --                 (arrow (f β h)) β a        β¨ functoriality-arrow f h βββ refl β©-βΌ
    --                 (arrow f β arrow h) β a    β¨ assoc-l-β {a = arrow f} {b = arrow h} β©-βΌ
    --                 arrow f β (arrow h β a)    β¨ P β©-βΌ
    --                 arrow g β (arrow h β a)    β¨ assoc-r-β {a = arrow g} {b = arrow h} β©-βΌ
    --                 (arrow g β arrow h) β a    β¨ functoriality-arrow g h β»ΒΉ βββ refl β©-βΌ
    --                 (arrow (g β h)) β a        β
    --            ))
    --   in antisym Pβ Pβ

{-
    lem-20 : {g : β¦ Good β¦} {i : Ix} β π (g β»ΒΉ' i) βΌ (β¨ g β© β»ΒΉβ·-Ide π i)
    lem-20 {g β’ gp} {nothing} = unit-r-β»ΒΉβ·-Ide β»ΒΉ
    lem-20 {[] β’ gp} {just (x , (f , g))} = absorb-l-β»ΒΉβ·-Ide β»ΒΉ
    lem-20 {idp β’ gp} {just (x , (f , g))} = unit-l-β»ΒΉβ·-Ide β»ΒΉ
    lem-20 {arrow {a} {b} h β’ gp} {just (x , (f , g))} with (x β-Str a)
    ... | no Β¬p =
      let Pβ : β€ β€ ((arrow h) β»ΒΉβ·-Ide β²(CoeqSolutions (arrow f) (arrow g))β²)
          Pβ = incl (Ξ» {a} xβ β incl (incl (
                    arrow f β (arrow h β a)    β¨ assoc-r-β {a = arrow f} {b = arrow h} β©-βΌ
                    (arrow f β arrow h) β a    β¨ PathMon-non-matching-arrows Β¬p f h βββ refl β©-βΌ
                    [] β a                     β¨ PathMon-non-matching-arrows Β¬p g h β»ΒΉ βββ refl β©-βΌ
                    (arrow g β arrow h) β a    β¨ assoc-l-β {a = arrow g} {b = arrow h} β©-βΌ
                    arrow g β (arrow h β a)    β
               )))
      in antisym Pβ terminal-β€
    ... | yes refl-StrId =
      let Pβ : β²(CoeqSolutions (arrow (f β h)) (arrow (g β h)))β² β€ ((arrow h) β»ΒΉβ·-Ide β²(CoeqSolutions (arrow f) (arrow g))β²)
          Pβ = incl (Ξ» {a} (incl P) β incl (incl (
                    arrow f β (arrow h β a)    β¨ assoc-r-β {a = arrow f} {b = arrow h} β©-βΌ
                    (arrow f β arrow h) β a    β¨ functoriality-arrow f h β»ΒΉ βββ refl β©-βΌ
                    (arrow (f β h)) β a        β¨ P β©-βΌ
                    (arrow (g β h)) β a        β¨ functoriality-arrow g h βββ refl β©-βΌ
                    (arrow g β arrow h) β a    β¨ assoc-l-β {a = arrow g} {b = arrow h} β©-βΌ
                    arrow g β (arrow h β a)    β
               )))
          Pβ : ((arrow h) β»ΒΉβ·-Ide β²(CoeqSolutions (arrow f) (arrow g))β²) β€ β²(CoeqSolutions (arrow (f β h)) (arrow (g β h)))β²
          Pβ = incl (Ξ» {a} (incl (incl P)) β incl (
                    (arrow (f β h)) β a        β¨ functoriality-arrow f h βββ refl β©-βΌ
                    (arrow f β arrow h) β a    β¨ assoc-l-β {a = arrow f} {b = arrow h} β©-βΌ
                    arrow f β (arrow h β a)    β¨ P β©-βΌ
                    arrow g β (arrow h β a)    β¨ assoc-r-β {a = arrow g} {b = arrow h} β©-βΌ
                    (arrow g β arrow h) β a    β¨ functoriality-arrow g h β»ΒΉ βββ refl β©-βΌ
                    (arrow (g β h)) β a        β
               ))
      in antisym Pβ Pβ
      -}

    lem-30 : β(i : Ix) -> (β Ξ» b -> π (bb b) βΌ π i) +-π° (β Ξ» n -> isSplittable M β² Good β² bb π n i (Ξ» j -> size' j βͺ size' i))
    lem-30 = {!!}


      -- ... | yes refl-StrId = β₯ (p2 β‘-βͺ p1)
      -- ... | no Β¬p = tt
      -- record
      --   { closed-β = tt
      --   ; closed-β = Ξ» p1 p2 -> ?
      --   }

  by-PrincipalCat-Principal : isPrincipalFamily M β² Good β² bb π
  by-PrincipalCat-Principal = {!!}
  -- record
  --              { Size = SizeC
  --              ; size = size'
  --              ; _β»ΒΉ*_ = _β»ΒΉ'_
  --              ; size:β»ΒΉ* = lem-10
  --              ; preserves-π:β»ΒΉ* = Ξ» {g} {i} -> lem-20 {g} {i}
  --              ; β = lem-30
  --              ; principalBase = {!!}
  --              }

    -- lem-10 : (g : β¦ Good β¦) (i : Ix) β (size' (g β»ΒΉ' i) βͺ£ size' i)
    -- lem-10 (g β’ gp) nothing = left refl
    -- lem-10 ([] β’ hp) (just (x , (f , g))) = initial-size0
    -- lem-10 (idp β’ hp) (just (x , (f , g))) = left refl
    -- lem-10 (arrow {a} {b} h β’ (β₯ hp)) (just (x , (f , g))) with (x β-Str a)
    -- ... | no Β¬p = initial-size0
    -- ... | yes refl-StrId = right hp


  -- module _ {B I : π°β} (π· : B -> I) (π : I -> Ideal-r M) where

      -- field size : I -> Size
      -- field _<<_ : Size -> Size -> π°β
      -- field isWellFounded:Size : WellFounded _<<_
      -- field trans-Size : β{a b c} -> a << b -> b << c -> a << c
      -- field _β»ΒΉ*_ : β¦ β¨ Good β© β¦ -> I -> I
      -- field size:β»ΒΉ* : β g i -> (size (g β»ΒΉ* i) β‘-Str size i) +-π° (size (g β»ΒΉ* i) << size i)
      -- field preserves-π:β»ΒΉ* : β {g i} -> π (g β»ΒΉ* i) βΌ (β¨ g β© β»ΒΉβ·-Ide (π i))
      -- -- field π : Idx -> Ideal-r M
      -- field β : (i : I) -> (β Ξ» b -> π· b β‘-Str i) +-π° (β Ξ» n -> isSplittable n i (Ξ» j -> size j << size i))
      -- field principalBase : β b -> isPrincipal/βΊ-r Good (π (π· b))
