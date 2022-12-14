
module Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat where

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
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Theory.Computation.Unification.Definition
open import Verification.Core.Theory.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Core.Theory.Presentation.Signature.Definition

module _ {M : π° π} {{_ : Monoidβ (π , π) on M}} where

  record CoeqSolutions' (f g h : M) : π° π where
    constructor incl
    field β¨_β© : f β h βΌ g β h
  open CoeqSolutions' public

  CoeqSolutions : (f g : M) -> π« M
  CoeqSolutions f g = Ξ» h -> β£ CoeqSolutions' f g h β£

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
private
  module _ {π : π° π} {{_ : isCategory π π}} where
    Pair : (a b : π) -> π° _
    Pair a x = Hom a x β§ Hom a x

record PrincipalFamilyCat (π : Category π) (a : β¨ π β©) : π° (π βΊ) where
  field SizeC : WFT (ββ , ββ)
  field SizeCF : WFT (ββ , ββ)
  field isBase : β(x) -> (h : a βΆ x) -> π° (π β 1)
  field sizeC : (x : β¨ π β©) -> β¨ SizeC β©
  field sizeCF : {x : β¨ π β©} -> (Pair a x) -> β¨ SizeCF β©

  -- field _βͺ_ : SizeC -> SizeC -> π°β
  -- field trans-SizeC : β{a b c} -> a βͺ b -> b βͺ c -> a βͺ c
  -- field isWellFounded:SizeC : WellFounded _βͺ_
  -- _βͺ£_ : SizeC -> SizeC -> π°β
  -- a βͺ£ b = (a β‘-Str b) β¨ (a βͺ b)
  field size0 : β¨ SizeC β©
  field initial-size0 : β{a} -> size0 βͺ£ a

open PrincipalFamilyCat {{...}} public

data Side : π°β where
  isLeft isRight : Side

module _ (π : Category π) {{_ : isDiscrete β¨ π β©}} {{_ : isSet-Str β¨ π β©}} (a : β¨ π β©) {{F : PrincipalFamilyCat π a}} where
  private

    Ix = Maybe (β Ξ» (x : β¨ π β©) -> Pair a x)
    Bx = Maybe (β Ξ» (x : β¨ π β©) -> Side Γ-π° ((β isBase x) β§ Hom a x))

    -- record isSplittableCat (n : β) (i : Ix) (P : I -> π°β) : π° (π ο½€ π βΊ) where
    --   field fam : Fin-R n -> I
    --   field covers : β-fin (Ξ» i -> π (fam i)) βΌ π i
    --   field famprops : β k -> P (fam k)
    -- open isSplittable public

    size' : Ix -> β¨ SizeC β©
    size' nothing = size0
    size' (just (x , _)) = sizeC x

    bb : Bx -> Ix
    bb nothing = nothing
    bb (just (x , isLeft , ((h , _) , f)))  = just (x , h , f)
    bb (just (x , isRight , ((h , _) , f))) = just (x , f , h)


    M : Monoidβ _
    M = β² PathMon π β²

    π : Ix -> Ideal-r M
    π nothing = β€
    π (just (_ , f , g)) = β²(CoeqSolutions (arrow f) (arrow g))β²

    Good : π« (PathMon π)
    Good [] = β€
    Good idp = β€
    Good (arrow {x} {y} f) = β£ Lift (sizeC y βͺ sizeC x) β£

    _β»ΒΉ'_ : β¦ Good β¦ -> Ix -> Ix
    _β»ΒΉ'_ (a) nothing = nothing
    _β»ΒΉ'_ ([] β’ _) (just _) = nothing
    _β»ΒΉ'_ (idp β’ _) (just (x , (f , g))) = just (x , (f , g))
    _β»ΒΉ'_ (arrow {a} {b} h β’ _) (just (x , (f , g))) with (x β-Str a)
    ... | yes refl-StrId = just (b , (f β h , g β h))
    ... | no Β¬p = nothing

    lem-10 : (g : β¦ Good β¦) (i : Ix) β (size' (g β»ΒΉ' i) βͺ£ size' i)
    lem-10 (g β’ gp) nothing = left refl
    lem-10 ([] β’ hp) (just (x , (f , g))) = initial-size0
    lem-10 (idp β’ hp) (just (x , (f , g))) = left refl
    lem-10 (arrow {a} {b} h β’ (β₯ hp)) (just (x , (f , g))) with (x β-Str a)
    ... | no Β¬p = initial-size0
    ... | yes refl-StrId = right hp

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

    instance
      isSubsetoid:Good : isSubsetoid Good
      isSubsetoid.transp-βΌ isSubsetoid:Good (incl idp) P = tt
      isSubsetoid.transp-βΌ isSubsetoid:Good (incl []) P = P
      isSubsetoid.transp-βΌ isSubsetoid:Good (incl (arrow fβΌg)) (β₯ p) = β₯ p

      isSubmonoid:Good : isSubmonoid β² Good β²
      isSubmonoid.closed-β isSubmonoid:Good = tt
      isSubmonoid.closed-β isSubmonoid:Good {idp} {b} p1 p2 = p2
      isSubmonoid.closed-β isSubmonoid:Good {[]} {b} p1 p2 = p1
      isSubmonoid.closed-β isSubmonoid:Good {arrow f} {[]} p1 p2 = p2
      isSubmonoid.closed-β isSubmonoid:Good {arrow f} {idp} p1 p2 = p1
      isSubmonoid.closed-β isSubmonoid:Good {arrow {a} {b} f} {arrow {c} {d} g} (β₯ p1) (β₯ p2) with (b β-Str c)
      ... | yes refl-StrId = β₯ (p2 β‘-βͺ p1)
      ... | no Β¬p = tt
      -- record
      --   { closed-β = tt
      --   ; closed-β = Ξ» p1 p2 -> ?
      --   }

    lem-50 : isPrincipalFamily M β² Good β² bb π
    lem-50 = {!!} -- record
               -- { Size = SizeC
               -- ; size = size'
               -- ; _<<_ = _βͺ_
               -- ; isWellFounded:Size = wellFounded
               -- ; trans-Size = _
               -- ; _β»ΒΉ*_ = _β»ΒΉ'_
               -- ; size:β»ΒΉ* = lem-10
               -- ; preserves-π:β»ΒΉ* = Ξ» {g} {i} -> lem-20 {g} {i}
               -- ; β = {!!}
               -- ; principalBase = {!!}
               -- }

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
