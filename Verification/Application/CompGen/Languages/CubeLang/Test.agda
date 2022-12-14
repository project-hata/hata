
module Verification.Application.CompGen.Languages.CubeLang.Test where

open import Verification.Conventions hiding (_โ_; _==_ ; refl ; zero)


data _==_ {a} {A : ๐ฐ a} (x : A) : A โ ๐ฐ a where
  refl : x == x

data โฅ : ๐ฐโ where

infixl 5 _==_

_โ _ : {A : ๐ฐโ} โ A โ A โ ๐ฐโ
a โ  b = a == b โ โฅ


record isField (K : ๐ฐโ) : ๐ฐโ where
  field
    zero : K
    one  : K

    _ยท_ : K โ K โ K
    _+_ : K โ K โ K

    assoc-+-l : โ(a b c : K) โ (a + b) + c == a + (b + c)
    assoc-ยท-l : โ(a b c : K) โ (a ยท b) ยท c == a ยท (b ยท c)

    comm-+ : โ(a b : K) โ a + b == b + a
    comm-ยท : โ(a b : K) โ a ยท b == b ยท a

    - : K โ K
    mulInv : (a : K) โ (proof : a โ  zero) โ K

    _/_ : K โ K

    plusZero : โ(a : K) โ a + zero == a
    timesOne : โ(a : K) โ a ยท one == a

    aMinusAIsZero : โ(a : K) โ a + (- a) == zero

    distributive : โ(a b c : K) โ a ยท (b + c) == (a ยท b) + (a ยท c)

open isField {{...}} public

record Vector (K V : ๐ฐโ) : ๐ฐโ where
  field
    scalar : isField K
    vector : V

record isKVectorSpace (K V : ๐ฐโ) {{_ : isField K}} : ๐ฐโ where
  field
  ...

    distributiveScaAdd : {a b : K} {v : Vector K V} โ (a + b) โ v == (a โ v) ++ (b โ v)

