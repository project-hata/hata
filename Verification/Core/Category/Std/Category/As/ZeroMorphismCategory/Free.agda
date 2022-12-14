
module Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Free where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Contradiction
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition

open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition

-- [Definition]
-- | Let |๐| be a category. We define |Free-๐๐๐๐๐ญ ๐| as the category obtained
--   from |๐| by freely adjoining an additional arrow to each hom-set.
--   This is done by defining each hom-set of |Free-๐๐๐๐๐ญ ๐| by a data type
--   with two constructors:
-- | - One which includes arrows from |๐| into |Free-๐๐๐๐๐ญ ๐|, namely |some : โจ a โฉ โถ โจ b โฉ โ Hom-Free-๐๐๐๐๐ญ a b|
-- | - And one which describes failure: |zero : Hom-Free-๐๐๐๐๐ญ a b|
-- |: This could have been done using the |Maybe| data type,
--    but as usual, dedicated data types are used for
--    better type inference.

-- //

-- [Lemma]
-- | There is indeed the structure of a category on |Free-๐๐๐๐๐ญ ๐|
--   which makes it into a category with zero morphisms,
--   with |0 = zero|

-- //

-- [Proof]
-- | The implementation of this structure is not difficult,
--   rather an exercise in many case distinctions
--   between |zero| and |some|.

-- //

-- [Hide]
record Free-๐๐๐๐๐ญ (๐ : Category ๐) : ๐ฐ (๐ โ 0) where
  constructor incl
  field โจ_โฉ : โจ ๐ โฉ

open Free-๐๐๐๐๐ญ public


module _ {๐แต : ๐ฐ ๐} {{_ : isCategory {๐} ๐แต}} where
  private
    ๐ : Category _
    ๐ = โฒ ๐แต โฒ

  data Hom-Free-๐๐๐๐๐ญ (a b : Free-๐๐๐๐๐ญ ๐) : ๐ฐ (๐ โ 0) where
    some : โจ a โฉ โถ โจ b โฉ -> Hom-Free-๐๐๐๐๐ญ a b
    zero : Hom-Free-๐๐๐๐๐ญ a b

  module _ {a b : Free-๐๐๐๐๐ญ ๐} where
    data _โผ-Hom-Free-๐๐๐๐๐ญ_ : (f g : Hom-Free-๐๐๐๐๐ญ a b) -> ๐ฐ ๐ where
      some : โ{f g} -> f โผ g -> some f โผ-Hom-Free-๐๐๐๐๐ญ some g
      zero : zero โผ-Hom-Free-๐๐๐๐๐ญ zero

    private
      lem-1 : โ{f : Hom-Free-๐๐๐๐๐ญ a b} -> f โผ-Hom-Free-๐๐๐๐๐ญ f
      lem-1 {some x} = some refl
      lem-1 {zero} = zero

      lem-2 : โ{f g : Hom-Free-๐๐๐๐๐ญ a b} -> f โผ-Hom-Free-๐๐๐๐๐ญ g -> g โผ-Hom-Free-๐๐๐๐๐ญ f
      lem-2 (some x) = some (x โปยน)
      lem-2 zero = zero

      lem-3 : โ{f g h : Hom-Free-๐๐๐๐๐ญ a b} -> f โผ-Hom-Free-๐๐๐๐๐ญ g -> g โผ-Hom-Free-๐๐๐๐๐ญ h -> f โผ-Hom-Free-๐๐๐๐๐ญ h
      lem-3 (some x) (some y) = some (x โ y)
      lem-3 zero zero = zero

    instance
      isSetoid:Hom-Free-๐๐๐๐๐ญ : isSetoid (Hom-Free-๐๐๐๐๐ญ a b)
      isSetoid:Hom-Free-๐๐๐๐๐ญ = isSetoid:byDef _โผ-Hom-Free-๐๐๐๐๐ญ_ lem-1 lem-2 lem-3

  id-Free-๐๐๐๐๐ญ : โ{a : Free-๐๐๐๐๐ญ ๐} -> Hom-Free-๐๐๐๐๐ญ a a
  id-Free-๐๐๐๐๐ญ = some id

  _โ-Free-๐๐๐๐๐ญ_ : โ{a b c : Free-๐๐๐๐๐ญ ๐} -> Hom-Free-๐๐๐๐๐ญ a b -> Hom-Free-๐๐๐๐๐ญ b c -> Hom-Free-๐๐๐๐๐ญ a c
  some f โ-Free-๐๐๐๐๐ญ some g = some (f โ g)
  some f โ-Free-๐๐๐๐๐ญ zero = zero
  zero โ-Free-๐๐๐๐๐ญ g = zero

  private
    lem-1 : โ{a b : Free-๐๐๐๐๐ญ ๐} -> โ{f : Hom-Free-๐๐๐๐๐ญ a b}
          -> (id-Free-๐๐๐๐๐ญ โ-Free-๐๐๐๐๐ญ f) โผ-Hom-Free-๐๐๐๐๐ญ f
    lem-1 {f = some x} = some unit-l-โ
    lem-1 {f = zero} = refl

    lem-2 : โ{a b : Free-๐๐๐๐๐ญ ๐} -> โ{f : Hom-Free-๐๐๐๐๐ญ a b}
          -> (f โ-Free-๐๐๐๐๐ญ id-Free-๐๐๐๐๐ญ) โผ-Hom-Free-๐๐๐๐๐ญ f
    lem-2 {f = some x} = some unit-r-โ
    lem-2 {f = zero} = refl

    lem-3 : โ{a b c d : Free-๐๐๐๐๐ญ ๐} -> โ{f : Hom-Free-๐๐๐๐๐ญ a b} {g : Hom-Free-๐๐๐๐๐ญ b c} {h : Hom-Free-๐๐๐๐๐ญ c d}
          -> ((f โ-Free-๐๐๐๐๐ญ g) โ-Free-๐๐๐๐๐ญ h) โผ-Hom-Free-๐๐๐๐๐ญ (f โ-Free-๐๐๐๐๐ญ (g โ-Free-๐๐๐๐๐ญ h))
    lem-3 {f = some x} {some xโ} {some xโ} = some assoc-l-โ
    lem-3 {f = some x} {some xโ} {zero} = refl
    lem-3 {f = some x} {zero} {h} = refl
    lem-3 {f = zero} {g} {h} = refl

    lem-4 : โ{a b c : Free-๐๐๐๐๐ญ ๐} -> โ{f g : Hom-Free-๐๐๐๐๐ญ a b} {h i : Hom-Free-๐๐๐๐๐ญ b c}
          -> f โผ-Hom-Free-๐๐๐๐๐ญ g -> h โผ-Hom-Free-๐๐๐๐๐ญ i
          -> (f โ-Free-๐๐๐๐๐ญ h) โผ-Hom-Free-๐๐๐๐๐ญ (g โ-Free-๐๐๐๐๐ญ i)
    lem-4 (some x) (some y) = some (x โ y)
    lem-4 (some x) zero = refl
    lem-4 zero q = refl

    lem-5 : โ{a b c : Free-๐๐๐๐๐ญ ๐} -> โ{f : Hom-Free-๐๐๐๐๐ญ a b}
          -> (f โ-Free-๐๐๐๐๐ญ zero {a = b} {b = c}) โผ-Hom-Free-๐๐๐๐๐ญ zero
    lem-5 {f = some x} = refl
    lem-5 {f = zero} = refl

  instance
    isCategory:Free-๐๐๐๐๐ญ : isCategory (Free-๐๐๐๐๐ญ ๐)
    isCategory.Hom isCategory:Free-๐๐๐๐๐ญ = Hom-Free-๐๐๐๐๐ญ
    isCategory.isSetoid:Hom isCategory:Free-๐๐๐๐๐ญ = isSetoid:Hom-Free-๐๐๐๐๐ญ
    isCategory.id isCategory:Free-๐๐๐๐๐ญ = id-Free-๐๐๐๐๐ญ
    isCategory._โ_ isCategory:Free-๐๐๐๐๐ญ = _โ-Free-๐๐๐๐๐ญ_
    isCategory.unit-l-โ isCategory:Free-๐๐๐๐๐ญ = lem-1
    isCategory.unit-r-โ isCategory:Free-๐๐๐๐๐ญ = lem-2
    isCategory.unit-2-โ isCategory:Free-๐๐๐๐๐ญ = lem-1
    isCategory.assoc-l-โ isCategory:Free-๐๐๐๐๐ญ = lem-3
    isCategory.assoc-r-โ isCategory:Free-๐๐๐๐๐ญ = lem-3 โปยน
    isCategory._โ_ isCategory:Free-๐๐๐๐๐ญ = lem-4

  instance
    isZeroMorphismCategory:Free-๐๐๐๐๐ญ : isZeroMorphismCategory โฒ(Free-๐๐๐๐๐ญ ๐)โฒ
    isZeroMorphismCategory:Free-๐๐๐๐๐ญ = record
      { pt = zero
      ; absorb-r-โ = lem-5
      ; absorb-l-โ = refl
      }

  ยฌisEpi:zero : โ{a b : Free-๐๐๐๐๐ญ ๐} -> ยฌ isEpi (zero {a = a} {b})
  ยฌisEpi:zero {a} {b} P = lem-p3
    where
      instance _ = P

      f g : b โถ b
      f = zero
      g = id

      lem-p1 : zero {a = a} โ f โผ zero {a = a} โ g
      lem-p1 = refl

      lem-p2 : f โผ g
      lem-p2 = cancel-epi lem-p1

      lem-p3 : ๐-๐ฐ
      lem-p3 with lem-p2
      ... | ()

  reflect-isEpi-Free-๐๐๐๐๐ญ : โ{a b : โจ ๐ โฉ} -> {f : a โถ b} -> isEpi (some f) -> isEpi f
  isEpi.cancel-epi (reflect-isEpi-Free-๐๐๐๐๐ญ {f = f} P) {z} {g} {h} fgโผfh = lem-p3
    where
      instance _ = P

      lem-p1 : some f โ some g โผ some f โ some h
      lem-p1 = some fgโผfh

      lem-p2 : some g โผ some h
      lem-p2 = cancel-epi lem-p1

      lem-p3 : g โผ h
      lem-p3 with lem-p2
      ... | some p = p

  preserve-isEpi-Free-๐๐๐๐๐ญ : โ{a b : โจ ๐ โฉ} -> {f : a โถ b} -> isEpi (f) -> isEpi (some f)
  isEpi.cancel-epi (preserve-isEpi-Free-๐๐๐๐๐ญ P) {z} {some x} {some xโ} (some fgโผfh) = some (cancel-epi fgโผfh)
    where instance _ = P
  isEpi.cancel-epi (preserve-isEpi-Free-๐๐๐๐๐ญ P) {z} {zero} {zero} fgโผfh = refl


instance
  hasFree:๐๐๐ญ,๐๐๐๐๐ญ : hasFree (Category ๐) (๐๐๐๐๐ญ _)
  hasFree:๐๐๐ญ,๐๐๐๐๐ญ = record { ๐๐๐๐แต = ฮป ๐ -> โฒ Free-๐๐๐๐๐ญ ๐ โฒ }

module _ {๐ : Category ๐} {{SP : isSizedCategory ๐}} where
  -- private
  --   sizeC' : โ{a b : Free-๐๐๐๐๐ญ ๐} -> (p : HomPair a b) -> โจ SizeC โฉ
  --   sizeC' (some x , g) = {!!}
  --   sizeC' (zero , some x) = {!!}
  --   sizeC' (zero , zero) = โฅ-WFT

  instance
    isSizedCategory:Free-๐๐๐๐๐ญ : isSizedCategory โฒ(Free-๐๐๐๐๐ญ ๐)โฒ
    isSizedCategory.SizeO isSizedCategory:Free-๐๐๐๐๐ญ = SizeO {{SP}}
    isSizedCategory.sizeO isSizedCategory:Free-๐๐๐๐๐ญ = ฮป (incl x) โ sizeO x

module _ {๐ : Category ๐} where
  instance
    isContradiction:zeroโฃsome : โ{a b : โจ ๐ โฉ} -> {f : a โถ b} -> isContradiction (StrId {A = Hom-Free-๐๐๐๐๐ญ (incl a) (incl b)} (zero) (some f))
    isContradiction:zeroโฃsome = contradiction (ฮป ())

    isContradiction:zeroโผsome : โ{a b : โจ ๐ โฉ} -> {f : a โถ b} -> isContradiction (_โผ-Hom-Free-๐๐๐๐๐ญ_ {a = incl a} {b = incl b}  (zero) (some f))
    isContradiction:zeroโผsome = contradiction (ฮป ())

  cancel-injective-some-Free-๐๐๐๐๐ญ : โ{a b : โจ ๐ โฉ} -> {f g : a โถ b} -> _โผ-Hom-Free-๐๐๐๐๐ญ_ {a = incl a} {b = incl b} (some f) (some g) -> f โผ g
  cancel-injective-some-Free-๐๐๐๐๐ญ (some x) = x


-- //

