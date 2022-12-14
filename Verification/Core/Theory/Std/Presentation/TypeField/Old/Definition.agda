
module Verification.Core.Theory.Syndetic.v2.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Theory.Presentation.Signature.SingleSorted.Definition


data Var (Ï : ğ°â) (A : ğ°â) : ğ°â where
  tok : Ï -> Var Ï A
  var : A -> Var Ï A
  -- nil : Var Ï A

record isDirSet (X : Setoid ğ) : ğ° (ğ âº) where
  field Dir : ğ°â
open isDirSet public

DirSet : â ğ -> ğ° _
DirSet ğ = Setoid ğ :& isDirSet

-- record DirSet ğ : ğ° ğ where
--   â¨_â© : Setoid ğ
--   Dir : ğ°â
-- open DirSet public

record Tâ (X : DirSet ğ) (Ï : ğ°â) : ğ° (ğ âº) where
  inductive
  field map0 : â¨ X â© -> (Bool) +-ğ° ((â Var Ï) Ã-ğ° (Dir (of X) -> Tâ X Ï))
  -- field map1 : â¨ X â© -> Dir (of X) -> Dir (of X) -> â Var Ï

Tree : ğ°â
Tree = (List â)

pattern v0 = left false
pattern v1 = left true

instance
  isSetoid:Tree : isSetoid _ Tree
  isSetoid._â¼'_ isSetoid:Tree = _â¡-Str_
  isSetoid.isEquivRel:â¼ isSetoid:Tree = {!!}

instance
  isDirSet:Tree : isDirSet â² Tree â²
  isDirSet:Tree = record { Dir = Maybe â }

ğ : DirSet _
ğ = â² Tree â²

module to-Tâ {Ï : Signature} where
  data ğ : ğ°â where
    * : ğ
    sig : â {n} -> Ï n -> ğ

  V = â Var ğ
  FF = Maybe â -> Tâ â² Tree â² ğ
  Zero : Tâ ğ ğ
  Tâ.map0 Zero x = v0

  One : Tâ ğ ğ
  One = {!!}

  Star : Tâ ğ ğ
  Tâ.map0 Star [] = right ((ğ-ğ° , tok *) , either (Î» _ -> One) (Î» _ -> Zero))
  Tâ.map0 Star (x â· xâ) = v0
  mutual
    kinded : â{n} -> Ï n -> FF
    kinded {n} _ nothing = Star
    kinded {n} _ (just x) = <? n x
      where <? : â -> â -> Tâ ğ ğ
            <? zero zero = Zero
            <? (suc a) zero = Zero
            <? zero (suc b) = Star
            <? (suc a) (suc b) = <? a b

    walks : {A : ğ°â} -> â{n} -> (ts : Terms Ï A n) -> â -> List â -> Bool +-ğ° ((V) Ã-ğ° FF)
    walks {A} {.0} [] i is = v0
    walks {A} {.(suc _)} (x â· ts) zero is = walk x is
    walks {A} {.(suc _)} (x â· ts) (suc i) is = walks ts i is

    walk : {A : ğ°â} (x : Term Ï A) -> (List â) -> Bool +-ğ° ((V) Ã-ğ° FF)
    walk {A} (te x ts) (i â· is) = walks ts i is
    walk {A} (var x) (i â· is) = v0
    walk {A} (te s ts) [] = just ((A , tok (sig s)) , kinded s)
    walk {A} (var x) [] = just ((A , var x) , either (Î» _ -> Star) (Î» _ -> Zero))

  module _ {A : ğ°â} (x : Term Ï A) where
    -- map0 : Tree -> â Var (â Ï)
    -- map0 = walk x

    done : Tâ â² Tree â² ğ
    done = record { map0 = walk x }

{-
-}

{-
data RST {A : ğ° ğ} (R : A -> A -> ğ° ğ) : A -> A -> ğ° (ğ ï½¤ ğ) where
  incl : â{a b} -> R a b -> RST R a b
  refl-RST : â{a} -> RST R a a
  sym-RST : â{a b} -> RST R a b -> RST R b a
  trans-RST : â{a b c} -> RST R a b -> RST R b c -> RST R a c

data _â¼-Tree_ : Tree -> Tree -> ğ°â where
  cancel-Tree : â{xs ys : Tree} -> {a : â} -> (xs <> (a â· 0 â· []) <> ys) â¼-Tree (xs <> ys)
  -- inside-Tree : â{xs ys : Tree} -> {a : â} -> (xs <> (a â· 0 â· []) <> ys) â¼-Tree (xs <> ys)

instance
  isEquivRel:RST : {A : ğ° ğ} {R : A -> A -> ğ° ğ} -> isEquivRel (â¼-Base (RST R))
  isEquivRel:RST = {!!}
  -}
