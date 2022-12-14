
module Verification.Core.Order.Linearorder where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Type

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Everything

open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder

--------------------------------------------------------------------
-- == Linear order
-- mainly from https://ncatlab.org/nlab/show/linear+order

private
  â¥ = ð-ð°

record Base< {A : ð° ð} (R : A -> A -> ð° ð) (a b : A) : ð° ð where
  constructor incl
  field Proof : (R a b)

open Base< public

record isLinearorder ð (A : ð° ð :& isSetoid {ð}) : ð° (ð âº ï½¤ ð ï½¤ ð) where
  field my< : â¨ A â© -> â¨ A â© -> ð° ð
  _<_ : â¨ A â© -> â¨ A â© -> ð° ð
  _<_ = Base< my<

  _â®_ : â¨ A â© -> â¨ A â© -> ð° ð
  _â®_ a b = Â¬ a < b

  field irrefl-< : {a : â¨ A â©} -> a â® a
        asym-< : â{a b : â¨ A â©} -> a < b -> b â® a
        compare-< : â{a c : â¨ A â©} -> a < c -> (b : â¨ A â©) -> (a < b) +-ð° (b < c)
        connected-< : â{a b : â¨ A â©} -> a â® b -> b â® a -> a â¼ b
        transp-< : â{aâ aâ bâ bâ : â¨ A â©} -> aâ â¼ aâ -> bâ â¼ bâ -> aâ < bâ -> aâ < bâ

  infixl 40 _<_

open isLinearorder {{...}} public

Linearorder : â (ð : ð ^ 3) -> ð° (ð âº)
Linearorder ð = ð° (ð â 0) :& isSetoid {ð â 1} :& isLinearorder (ð â 2)

record isUnbound {ð : ð ^ 3} (L : Linearorder ð) : ð° ð where
  field getLess     : (a : â¨ L â©) -> â¦ (Î» x -> â£ x < a â£) â¦
  field getGreater  : (a : â¨ L â©) -> â¦ (Î» x -> â£ a < x â£) â¦
open isUnbound {{...}} public

record isDense {ð : ð ^ 3} (L : Linearorder ð) : ð° ð where
  field between : {a b : â¨ L â©} -> a < b -> â¦ (Î» x -> â£ a < x Ã-ð° x < b â£) â¦
open isDense {{...}} public

--------------------------------------------------------------------
-- as Totalorderâ»

module LinearAsTotal {ð : ð ^ 2} {ð : ð} {A : ð° (fst ð)} {{_ : isSetoid {snd ð} A}} {{_ : isLinearorder ð â² A â²}} where
  instance
    isTotal:Linear : isPreorder ð â² A â²
    isPreorder._â¤_ isTotal:Linear a b = b â® a
    isPreorder.reflexive isTotal:Linear = irrefl-<
    isPreorder._â¡_ isTotal:Linear {a} {b} {c} (p) (q) = P
      where
          P : c < a -> â¥
          P r with compare-< r b
          ... | left x = q x
          ... | just x = p x
    isPreorder.transp-â¤ isTotal:Linear = {!!}

  instance
    isPartialorder:Linear : isPartialorder â² A â²
    isPartialorder.antisym isPartialorder:Linear (p) (q) = connected-< q p

  instance
    isTotalorderâ»:Linear : isTotalorderâ» â² A â²
    isTotalorderâ».totalâ» isTotalorderâ»:Linear _ _ p = (Î» a<b -> p ((Î» {b<a -> asym-< a<b b<a})))


--------------------------------------------------------------------
-- Totalorder as Linearorder
isLinearorder:Totalorderâº : (X : Totalorderâº ð) -> isLinearorder _ â² â¨ X â© â²
isLinearorder:Totalorderâº X = record
  { my< = Î» a b â b â° a
  ; irrefl-< = Î» (incl x) â x reflexive
  ; asym-< = Î» {a} {b} aâ°b bâ°a -> let q = totalâº a b
                                  in case-Trichotomy q of
                                  (Î» (bâ¤a , _) â bâ°a .Proof bâ¤a)
                                  (Î» aâ¼b -> bâ°a .Proof (by-â¼-â¤_ aâ¼b ) )
                                  (Î» (aâ¤b , _) â aâ°b .Proof aâ¤b)
  ; compare-< = lem-10
  ; connected-< = lem-20
  ; transp-< = lem-30
  }
  where
    _<'_ : â¨ X â© -> â¨ X â© -> ð° _
    _<'_ x y = Base< (Î» a b -> b â° a) x y

    lem-10 : â{a c : â¨ X â©} -> a <' c -> â(b : â¨ X â©) -> (a <' b) +-ð° (b <' c)
    lem-10 {a} {c} (incl câ°a) b with totalâº a b | totalâº b c
    ... | gt (bâ¤a , bâa) | Y = right (incl Î» câ¤b â câ°a (câ¤b â¡ bâ¤a))
    ... | eq bâ¼a         | Y = right (incl Î» câ¤b â câ°a (câ¤b â¡ (by-â¼-â¤ (bâ¼a â»Â¹))))
    ... | lt (aâ¤b , aâb) | _ = left (incl Î» bâ¤a â aâb (antisym aâ¤b bâ¤a))

    lem-20 : â{a b} -> Â¬ (a <' b) -> Â¬ (b <' a) -> a â¼ b
    lem-20 {a} {b} Â¬a<b Â¬b<a with totalâº a b
    ... | lt (aâ¤b , aâb) = ð-rec (Â¬a<b (incl Î» bâ¤a â aâb (antisym aâ¤b bâ¤a)))
    ... | eq aâ¼b = aâ¼b
    ... | gt (bâ¤a , bâa) = ð-rec (Â¬b<a (incl Î» aâ¤b â bâa (antisym bâ¤a aâ¤b)))

    lem-30 : â{a0 a1 b0 b1} -> (a0 â¼ a1) -> (b0 â¼ b1) -> a0 <' b0 -> a1 <' b1
    lem-30 p q (incl a0<b0) = incl Î» b1â¤a1 â a0<b0 (transp-â¤ (q â»Â¹) (p â»Â¹) b1â¤a1)


--------------------------------------------------------------------
-- Syntax

module _ {ð : ð ^ 3} {A : ð° _} {{_ : Linearorder ð on A}} where
  -- by-â¼-<_ : {a b : A} -> (a â¼ b) -> a < b
  -- by-â¼-<_ p = {!!} -- transp-< refl p refl-<
  -- infixl 10 by-â¼-<_
  by-<-â : â{a b : A} -> a < b -> Â¬ a â¼ b
  by-<-â p q = irrefl-< (transp-< q refl p)

  _â-<_ : {x : A} {y : A} {z : A} â x < y â y < z â x < z
  _â-<_ {x} {y} {z} x<y y<z with compare-< x<y z
  ... | left x<z = x<z
  ... | just z<y = ð-rec (asym-< y<z z<y)

  _â¨_â©-<_ : (x : A) {y : A} {z : A} â x < y â y < z â x < z
  _ â¨ x<y â©-< y<z = x<y â-< y<z

  â¨â©-<-syntax : (x : A) {y z : A} â x < y â y < z â x < z
  â¨â©-<-syntax = _â¨_â©-<_
  infixr 2 â¨â©-<-syntax
  -- infix  3 _â¨_â©-<-â
  infixr 2 _â¨_â©-<_

  -- _â¨_â©-<-â : (x : A) -> â x < x
  -- _ â-< = refl-<

  _â¨_â©-â¼-<_ : (x : A) {y : A} {z : A} â x â¼ y â y < z â x < z
  _ â¨ xâ¼y â©-â¼-< y<z = transp-< (xâ¼y â»Â¹) refl y<z
  -- x<y â-< y<z

  â¨â©-â¼-<-syntax : (x : A) {y z : A} â x â¼ y â y < z â x < z
  â¨â©-â¼-<-syntax = _â¨_â©-â¼-<_
  infixr 2 â¨â©-â¼-<-syntax
  infixr 2 _â¨_â©-â¼-<_

  _â¨_â©-<-â¼_ : (x : A) {y : A} {z : A} â x < y â y â¼ z â x < z
  _ â¨ x<y â©-<-â¼ yâ¼z = transp-< refl yâ¼z x<y
  -- x<y â-< y<z

  â¨â©-<-â¼-syntax : (x : A) {y z : A} â x < y â y â¼ z â x < z
  â¨â©-<-â¼-syntax = _â¨_â©-<-â¼_
  infixr 2 â¨â©-<-â¼-syntax
  infixr 2 _â¨_â©-<-â¼_


