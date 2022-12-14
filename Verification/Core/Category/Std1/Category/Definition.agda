
{-# OPTIONS --warning=noInstanceWithExplicitArg #-}

module Verification.Core.Category.Std1.Category.Definition where

open import Verification.Conventions
-- open import Verification.Core.Setoid


record CategoryType (๐ : ๐ ^ 3) : ๐ฐ (๐ โบ) where
  constructor [_,_,_]
  field Cellโแต : ๐ฐ (๐ โ 0)
  field Cellโแต : Cellโแต -> Cellโแต -> ๐ฐ (๐ โ 1)
  field Cellโแต : โ{a b : Cellโแต} -> (f g : Cellโแต a b) -> ๐ฐ (๐ โ 2)

  _โโถ_ = Cellโแต
  _โโถ_ = Cellโแต

-- open CategoryType public

open CategoryType {{...}} hiding (Cellโแต) public
open CategoryType using (Cellโแต) public

record CategoryFun {๐ : ๐ ^ 3} (๐แต : CategoryType ๐) : ๐ฐ (๐) where
  instance _ = ๐แต
  field idโแต : โ{a : Cellโแต ๐แต} -> Cellโแต a a
  field idโแต : โ{a b : Cellโแต ๐แต} -> {f : Cellโแต a b} -> Cellโแต f f

  field compแตโโ : โ{a b c : Cellโแต ๐แต} -> (Cellโแต a b ร-๐ฐ Cellโแต b c) -> Cellโแต a c
  field _โโแตโ_ : โ{a b c : Cellโแต ๐แต} -> (f : Cellโแต a b) -> (g : Cellโแต b c) -> Cellโแต a c

  -- constructor [_,_,_โฃ_,_โฃ_,_,_]
  -- field Cellโแต : ๐ฐ (๐ โ 0)
  -- field Cellโแต : Cellโแต -> Cellโแต -> ๐ฐ (๐ โ 1)
  -- field Cellโแต : โ{a b : Cellโแต} -> (f g : Cellโแต a b) -> ๐ฐ (๐ โ 2)

open CategoryFun {{...}} public

record CategoryEq {๐ : ๐ ^ 3} {๐แต : CategoryType ๐} (๐แถ  : CategoryFun ๐แต) : ๐ฐ ๐ where
  instance _ = ๐แต
  instance _ = ๐แถ 
  field unit-l-โ : โ{a b : Cellโแต ๐แต} {f : a โโถ b} -> (idโแต โโแตโ f) โโถ f

record is1Category {๐ : ๐ ^ 2} {๐ : ๐} (๐ : ๐ฐ ๐) : ๐ฐ (๐ โ ๐ โบ) where
  field Hom : ๐ -> ๐ -> ๐ฐ (๐ โ 0)
  field _โผ_ : โ{a b : ๐} -> (f g : Hom a b) -> ๐ฐ (๐ โ 1)
  -- field Cells : CategoryType ๐
  field Funs : CategoryFun ([ ๐ , Hom , _โผ_ ])
  field Eqs : CategoryEq (Funs)


open is1Category โฆ...โฆ public

1Category : (๐ : ๐ ^ 3) -> ๐ฐ _
1Category ๐ = ๐ฐ (๐ โ 0) :& is1Category {๐ โ 1 โฏ 2}

HomOf : (๐ : 1Category ๐) -> (a b : โจ ๐ โฉ) -> ๐ฐ _
HomOf ๐ a b = Hom a b

IsoOf : (๐ : 1Category ๐) -> (a b : โจ ๐ โฉ) -> ๐ฐ _
IsoOf ๐ a b = Hom a b ร-๐ฐ Hom b a

ObjOf : (๐ : 1Category ๐) -> ๐ฐ _
ObjOf ๐ = โจ ๐ โฉ

module _ (๐ : 1Category ๐) (๐ : 1Category ๐) where
  isFunctor : (f : โจ ๐ โฉ -> โจ ๐ โฉ) -> ๐ฐ (๐ ๏ฝค ๐)
  isFunctor = {!!}

_ร-1๐๐๐ญ_ : 1Category ๐ -> 1Category ๐ -> 1Category ๐
_ร-1๐๐๐ญ_ ๐ ๐ = โจ ๐ โฉ ร-๐ฐ โจ ๐ โฉ since {!!}


record is2Category {๐ : ๐ ^ 3} {๐ : ๐} (๐ : ๐ฐ ๐) : ๐ฐ (๐ โ ๐ โบ) where
  field Cells : ๐ -> ๐ -> 1Category ๐
  field Funsโ : CategoryFun [ ๐ , (ฮป a b -> ObjOf (Cells a b)) , (IsoOf (Cells _ _)) ]
  field Eqsโ : CategoryEq Funsโ


  field isFunctor:comp : โ{a b c : ๐} -> isFunctor (Cells a b ร-1๐๐๐ญ Cells b c) (Cells a c) (compแตโโ {{Funsโ}})

  -- field funsโ : CategoryFun [ ๐ , (ฮป a b -> Cellโแต (Cells a b)) , (ฮป a b -> Cellโแต {{Cells _ _}} a b) ]
  -- field eqsโ : CategoryEq funsโ

{-
  _โโถ_ = Cellโแต
  _โโถ_ = Cellโแต

  field idโแต : โ{a : Cellโแต} -> Cellโแต a a
  field idโแต : โ{a b : Cellโแต} -> {f : Cellโแต a b} -> Cellโแต f f

  field _โโแตโ_ : โ{a b c : Cellโแต} -> (f : Cellโแต a b) -> (g : Cellโแต b c) -> Cellโแต a c
  field _โโแตโ_ : โ{a b c : Cellโแต}
                 -> {f f' : Cellโแต a b}
                 -> {g g' : Cellโแต b c}
                 -> (ฮฑ : Cellโแต f f') -> (ฮฒ : Cellโแต g g')
                 -> Cellโแต (f โโแตโ g) (f' โโแตโ g')
  field _โโแตโ_ : โ{a b : Cellโแต} -> {f g h : Cellโแต a b} -> Cellโแต f g -> Cellโแต g h -> Cellโแต f h

open โฅ1CategoryData {{...}} hiding (Cellโแต ; Cellโแต ; Cellโแต) public
open โฅ1CategoryData using (Cellโแต ; Cellโแต ; Cellโแต) public


record isโฅ1Category {๐ : ๐ ^ 3} (๐แต : โฅ1CategoryData ๐) : ๐ฐ (๐) where
  instance _ = ๐แต
  field unit-l-โ : โ{a b : Cellโแต ๐แต} {f : a โโถ b} -> (idโแต โโแตโ f) โโถ f

record โฅ2CategoryData (๐ : ๐ ^ 4) : ๐ฐ (๐ โบ) where
  field Cellโแต : ๐ฐ (๐ โ 0)
  field Cells : Cellโแต -> โฅ1CategoryData (๐ โ 1 โฏ 3)
-}



{-
record isCategory {๐ : ๐ ^ 2} {๐ : ๐} (๐ : ๐ฐ ๐) : ๐ฐ ((๐ โ 0) โ ๐ โบ) where
  constructor category
  infixl 50 _โ_ _โ_

-- | 1. A type family [..], assigning to every pair of objects |a b : ๐|
--      a type of /homomorphisms/ |Hom a b| between them.
--      We call elements of this type also simply /morphisms/ or /arrows/.
  field Hom : ๐ -> ๐ -> ๐ฐ (๐ โ 0)

  -- Hom : ๐ -> ๐ -> ๐ฐ (๐ โ 0)
  -- Hom a b = Hom-Base Hom' a b
  field {{isSetoid:Hom}} : โ{a b : ๐} -> isSetoid {๐ โ 1} (Hom a b)

-- | 3. An operation [..], assigning to every object |a| an identity morphism on this object.
  field id : โ{a : ๐} -> Hom a a

-- | 4. A composition operation [..], which allows us to compose morphisms whose domain and codomain are compatible.
        _โ_ : โ{a b c : ๐} -> Hom a b -> Hom b c -> Hom a c

-- | 5. Proofs that |id| is a unit for composition.
        unit-l-โ          : โ{a b : ๐} -> โ{f : Hom a b} -> id โ f โผ f
        unit-r-โ          : โ{a b : ๐} -> โ{f : Hom a b} -> f โ id โผ f
        unit-2-โ          : โ{a : ๐} -> id โ id โผ id {a = a}
-- | 6. Proofs that composition is associative.
        assoc-l-โ         : โ{a b c d : ๐} -> โ{f : Hom a b} -> โ{g : Hom b c} -> โ{h : Hom c d} -> (f โ g) โ h โผ f โ (g โ h)
        assoc-r-โ         : โ{a b c d : ๐} -> โ{f : Hom a b} -> โ{g : Hom b c} -> โ{h : Hom c d} -> f โ (g โ h) โผ (f โ g) โ h
-- | 7. A proof that composition is compatible with the equivalence relation.
        _โ_               : โ{a b c : ๐} -> โ{f g : Hom a b} -> โ{h i : Hom b c} -> f โผ g -> h โผ i -> f โ h โผ g โ i

open isCategory โฆ...โฆ public

-}



