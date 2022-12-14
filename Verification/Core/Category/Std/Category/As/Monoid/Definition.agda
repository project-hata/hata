
module Verification.Core.Category.Std.Category.As.Monoid.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Category.Std.Category.Definition

-- open import Verification.Core.Data.Universe.Definition


module _ {π : π° π} {{_ : isCategory {π} π}} where
    -- data isIdArrow {a b : β¨ π β©} (f : a βΆ b)
  isNotIdArrow-impl : {a b : π} -> (f : a βΆ b) -> (a β‘-Str b) -> π° _
  isNotIdArrow-impl f refl-StrId = Β¬ (f βΌ id)

  isNotIdArrow : {a b : π} -> (f : a βΆ b) -> π° _
  isNotIdArrow f = β(p) -> isNotIdArrow-impl f p

  isIdArrow-impl : {a b : π} -> (f : a βΆ b) -> (a β‘-Str b) -> π° _
  isIdArrow-impl f refl-StrId = f βΌ id

  isIdArrow : {a b : π} -> (f : a βΆ b) -> π° _
  isIdArrow f = β(p) -> isIdArrow-impl f p

  rexHom : {a b c : π} -> (f : a βΆ b) -> (b β‘-Str c) -> a βΆ c
  rexHom {a} f p = transport-Str (cong-Str (Hom a) p) f

  lexHom : {a b c : π} -> (f : b βΆ c) -> (a β‘-Str b) -> a βΆ c
  lexHom {a} {b} {c} f refl-β£ = f
  -- transport-Str (cong-Str (Ξ» x -> Hom x c) (p β»ΒΉ)) f

module _ (π : Category π) {{_ : isDiscrete β¨ π β©}} where
  data PathMon : π° π where
    [] : PathMon
    idp : PathMon
    arrow : {a b : β¨ π β©} -> (f : a βΆ b) -> PathMon

macro
  π―πΊπππ¬ππ : β(π : Category π) -> {{_ : isDiscrete β¨ π β©}} -> SomeStructure
  π―πΊπππ¬ππ π = #structureOn (PathMon π)

module _ {π : Category π} {{_ : isDiscrete β¨ π β©}} {{_ : isSet-Str β¨ π β©}} where

  data _βΌ-PathMon_ : (f g : PathMon π) -> π° (π) where
    -- idp : β{a : β¨ π β©} -> {f : a βΆ a} -> (f βΌ id) -> arrow f βΌ-PathMon idp
    idp : idp βΌ-PathMon idp
    [] : [] βΌ-PathMon []
    arrow : {a b : β¨ π β©} -> {f g : a βΆ b} -> (p : f βΌ g) -> arrow f βΌ-PathMon arrow g

  -- instance
  --   isEquivRel:βΌ-PathMon : isEquivRel (βΌ-Base _βΌ-PathMon_)
  --   isEquivRel.refl isEquivRel:βΌ-PathMon {[]} = incl []
  --   isEquivRel.refl isEquivRel:βΌ-PathMon {idp} = incl idp
  --   isEquivRel.refl isEquivRel:βΌ-PathMon {arrow f} = incl (arrow refl)
  --   isEquivRel.sym isEquivRel:βΌ-PathMon {.idp} (incl idp) = incl idp
  --   isEquivRel.sym isEquivRel:βΌ-PathMon {.[]} (incl []) = incl []
  --   isEquivRel.sym isEquivRel:βΌ-PathMon {.(arrow _)} (incl (arrow p)) = incl (arrow (p β»ΒΉ))
  --   (isEquivRel:βΌ-PathMon isEquivRel.β incl idp) (incl idp) = incl idp
  --   (isEquivRel:βΌ-PathMon isEquivRel.β incl []) (incl []) = incl []
  --   (isEquivRel:βΌ-PathMon isEquivRel.β incl (arrow p)) (incl (arrow q)) = incl (arrow (p β q))

  private
    lem-1 : β{a} -> a βΌ-PathMon a
    lem-1 {[]} = []
    lem-1 {idp} = idp
    lem-1 {arrow f} = (arrow refl)

    lem-2 : β{a b} -> a βΌ-PathMon b -> b βΌ-PathMon a
    lem-2 {.idp} (idp) = idp
    lem-2 {.[]} ([]) = []
    lem-2 {.(arrow _)} ((arrow p)) = (arrow (p β»ΒΉ))

    lem-3 : β{a b c} -> a βΌ-PathMon b -> b βΌ-PathMon c -> a βΌ-PathMon c
    lem-3 idp idp = idp
    lem-3 [] [] = []
    lem-3 (arrow p) (arrow q) = arrow (p β q)


  instance
    isSetoid:PathMon : isSetoid (PathMon π)
    isSetoid._βΌ_ isSetoid:PathMon = _βΌ-PathMon_
    isSetoid.refl isSetoid:PathMon = lem-1
    isSetoid.sym isSetoid:PathMon = lem-2
    isSetoid._β_ isSetoid:PathMon = lem-3

  _β-PathMon_ : (a b : PathMon π) -> PathMon π
  [] β-PathMon b = []
  idp β-PathMon b = b
  arrow f β-PathMon [] = []
  arrow f β-PathMon idp = arrow f
  arrow {a} {b} f β-PathMon arrow {b'} {c} g with (b β-Str b')
  ... | yes p = arrow (rexHom f p β g)
  ... | no Β¬p = []
  infixl 40 _β-PathMon_

  private
    lem-10 : β{a : PathMon π} -> idp β-PathMon a βΌ a
    lem-10 {[]} = refl
    lem-10 {idp} = refl
    lem-10 {arrow f} = refl

    lem-20 : β{a : PathMon π} -> a β-PathMon idp βΌ a
    lem-20 {[]} = refl
    lem-20 {idp} = refl
    lem-20 {arrow f} = refl

    lem-30 : β{a b c : PathMon π} -> (a β-PathMon b) β-PathMon c βΌ a β-PathMon (b β-PathMon c)
    lem-30 {[]} {b} {c} = refl
    lem-30 {idp} {b} {c} = refl
    lem-30 {arrow f} {[]} {c} = refl
    lem-30 {arrow f} {idp} {c} = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {[]} with (b β-Str b')
    ... | yes refl-StrId = refl
    ... | no Β¬p = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {idp} with (b β-Str b')
    ... | yes refl-StrId = refl
    ... | no Β¬p = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} fβ} with (b β-Str b') | (c β-Str c')
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} fβ} | yes p0 | yes q0 with (b β-Str b') | (c β-Str c')
    ... | yes p1 | no Β¬q = π-rec (Β¬q q0)
    ... | no Β¬p | Y = π-rec (Β¬p p0)
    ... | yes p1 | yes q1 with isset-Str p0 p1 | isset-Str q0 q1
    ... | refl-StrId | refl-StrId with p0 | q0
    ... | refl-StrId | refl-StrId = (arrow assoc-l-β)
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} fβ} | yes refl-StrId | no Β¬p with (c β-Str c')
    ... | yes p = π-rec (Β¬p p)
    ... | no Β¬pβ = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} fβ} | no Β¬p | yes refl-StrId with (b β-Str b')
    ... | yes p = π-rec (Β¬p p)
    ... | no Β¬pβ = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} fβ} | no Β¬p | no Β¬pβ = refl

    lem-35 : β{a0 b0 a1 b1 : PathMon π} -> (a0 βΌ-PathMon a1) -> (b0 βΌ-PathMon b1) -> (a0 β-PathMon b0) βΌ (a1 β-PathMon b1)
    lem-35 idp idp = refl
    lem-35 idp [] = refl
    lem-35 idp (arrow p) = (arrow p)
    lem-35 [] q = refl
    lem-35 (arrow p) idp = (arrow p)
    lem-35 (arrow p) [] = refl
    lem-35 (arrow {a} {b} {f0} {f1} p) (arrow {c} {d} {g0} {g1} q) with (b β-Str c)
    ... | yes refl-StrId = (arrow (p β q))
    ... | no Β¬p = refl

    lem-40 : β{a0 b0 a1 b1 : PathMon π} -> (a0 βΌ a1) -> (b0 βΌ b1) -> (a0 β-PathMon b0) βΌ (a1 β-PathMon b1)
    lem-40 p q = lem-35 p q

  instance
    isMonoid:PathMon : isMonoid (π―πΊπππ¬ππ π)
    isMonoid._β_ isMonoid:PathMon = _β-PathMon_
    isMonoid.β isMonoid:PathMon = idp
    isMonoid.unit-l-β isMonoid:PathMon = lem-10
    isMonoid.unit-r-β isMonoid:PathMon = lem-20
    isMonoid.assoc-l-β isMonoid:PathMon {a} {b} {c} = lem-30 {a} {b} {c}
    -- isMonoid.assoc-r-β isMonoid:PathMon {a} {b} {c} = lem-30 {a} {b} {c} β»ΒΉ
    isMonoid._βββ_ isMonoid:PathMon = lem-40


  instance
    hasZero:PathMon : hasZero (π―πΊπππ¬ππ π)
    hasZero.β hasZero:PathMon = []
    hasZero.absorb-r-β hasZero:PathMon {[]} = refl
    hasZero.absorb-r-β hasZero:PathMon {idp} = refl
    hasZero.absorb-r-β hasZero:PathMon {arrow f} = refl
    hasZero.absorb-l-β hasZero:PathMon = refl
    hasZero.decide-β hasZero:PathMon [] = right refl
    hasZero.decide-β hasZero:PathMon idp = left (Ξ» ())
    hasZero.decide-β hasZero:PathMon (arrow f) = left (Ξ» ())



  -- further statements
  functoriality-arrow : β{a b c : β¨ π β©} -> (f : a βΆ b) -> (g : b βΆ c) -> arrow (f β g) βΌ (arrow f β arrow g)
  functoriality-arrow {a} {b} {c} f g with (b β-Str b)
  ... | yes p = let Pβ : refl-StrId β‘-Str p
                    Pβ = isset-Str _ _
                in (transport-Str (cong-Str (Ξ» q -> arrow (f β g) βΌ arrow (rexHom f q β g)) Pβ) refl)
  ... | no Β¬p = π-rec (Β¬p refl-β£)

  PathMon-non-matching-arrows : β{a b c d : β¨ π β©} -> (b β’-Str c) -> (f : a βΆ b) -> (g : c βΆ d) -> arrow f β arrow g βΌ []
  PathMon-non-matching-arrows {a} {b} {c} {d} p f g with (b β-Str c)
  ... | yes q = π-rec (p q)
  ... | no Β¬p = refl

  PathMon-arrow-path-inv : β{a b c d : β¨ π β©} -> (f : a βΆ b) -> (g : c βΆ d) -> (p : a β‘-Str c) -> (q : b β‘-Str d) -> (arrow {π = π} f βΌ-PathMon arrow g) -> rexHom f q βΌ lexHom g p
  PathMon-arrow-path-inv f g p q (arrow P) =
    let Pβ : rexHom f refl-β£ βΌ lexHom g refl-β£
        Pβ = P
        qβ : refl-β£ β‘-Str q
        qβ = isset-Str _ _
        qβ : refl-β£ β‘-Str p
        qβ = isset-Str _ _
        Pβ : rexHom f q βΌ lexHom g refl-β£
        Pβ = transport-Str (cong-Str (Ξ» ΞΎ -> rexHom f ΞΎ βΌ lexHom g refl-β£) qβ) Pβ
        Pβ : rexHom f q βΌ lexHom g p
        Pβ = transport-Str (cong-Str (Ξ» ΞΎ -> rexHom f q βΌ lexHom g ΞΎ) qβ) Pβ
    in Pβ

  case-PathMon_of : β(x : PathMon π) -> {P : PathMon π -> π° π}
                  -> (β(p : x βΌ []) -> P x)
                  -> (β(p : x βΌ idp) -> P x)
                  -> (β{a b : β¨ π β©} {f : a βΆ b} -> (p : x βΌ arrow f) -> P x)
                  -> P x
  case-PathMon [] of {P} f1 f2 f3 = f1 refl
  case-PathMon idp of {P} f1 f2 f3 = f2 refl
  case-PathMon arrow f of {P} f1 f2 f3 = f3 refl

  PathMon-arrow-path-matching-codom : β{a b c d : β¨ π β©} -> (f : a βΆ b) -> (g : c βΆ d) -> (arrow {π = π} f βΌ-PathMon arrow g) -> b β‘-Str d
  PathMon-arrow-path-matching-codom f g (arrow p) = refl-β£
