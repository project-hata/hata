
module Verification.Core.Order.Preorder where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Type
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Universe.Definition

--------------------------------------------------------------------
-- == Preorder

record â¤-Base {A : ð° ð} (R : A -> A -> ð° ð) (a b : A) : ð° ð where
  constructor incl
  field â¨_â© : (R a b)
open â¤-Base public

record isPreorder ð (A : ð° ð :& isSetoid {ð}) : ð° (ð âº ï½¤ ð ï½¤ ð) where
  field _â¤_ : â¨ A â© -> â¨ A â© -> ð° ð
  -- _â¤_ : â¨ A â© -> â¨ A â© -> ð° ð
  -- _â¤_ = â¤-Base _â¤_

  field reflexive : {a : â¨ A â©} -> a â¤ a
        _â¡_ : {a b c : â¨ A â©} -> a â¤ b -> b â¤ c -> a â¤ c
        transp-â¤ : â{aâ aâ bâ bâ : â¨ A â©} -> aâ â¼ aâ -> bâ â¼ bâ -> aâ â¤ bâ -> aâ â¤ bâ
  infixl 40 _â¤_
  infixl 40 _â¡_

open isPreorder {{...}} public

Preorder : â (ð : ð ^ 3) -> ð° (ð âº)
Preorder ð = ð° (ð â 0) :& isSetoid {ð â 1} :& isPreorder (ð â 2)

module _ {ð : ð ^ 3} {A : ð° _} {{_ : Preorder ð on A}} where
  _â°_ : A -> A -> ð° _
  a â° b = Â¬ a â¤ b

  _â¦_ : A -> A -> ð° _
  a â¦ b = (a â¤ b) Ã-ð° (a â b)

  -- â§

--------------------------------------------------------------------
-- == Partial order

module _ {ð : ð ^ 3} where
  record isPartialorder (A : Preorder ð) : ð° ð where
   field antisym : â{a b : â¨ A â©} -> (a â¤ b) -> (b â¤ a) -> a â¼ b
open isPartialorder {{...}} public

Partialorder : (ð : ð ^ 3) -> ð° _
Partialorder ð = Preorder ð :& isPartialorder

----------------------------------------------------------
-- Derived instances

module _ {A : ð° ð} {{_ : isSetoid {ð} A}} {{_ : isPreorder ð â² A â²}} where
  instance
    isPreorder:Family : â{I : ð° ð} -> isPreorder _ (â² (I -> A) â²)
    isPreorder._â¤_ isPreorder:Family f g = â a -> f a â¤ g a
    isPreorder.reflexive isPreorder:Family = Î» aâ â reflexive
    isPreorder._â¡_ isPreorder:Family = Î» f g a â f a â¡ g a
    isPreorder.transp-â¤ isPreorder:Family = {!!}
    -- isPreorder._â¤_      isPreorder:Family f g = â{a} -> f a â¤ g a
    -- isPreorder.reflexive isPreorder:Family = incl â¨ reflexive â©
    -- isPreorder._â¡_       isPreorder:Family (incl f) (incl g) = incl (â¨ incl f â¡ incl g â©)
    -- isPreorder.transp-â¤  isPreorder:Family (p) (q) f = incl (â¨ transp-â¤ (p) (q) (incl â¨ f â©) â©)

module _ {A : ð° ð} {{_ : isSetoid {ð} A}} {{_ : isPreorder ð â² A â²}} {{_ : isPartialorder â² A â²}} where
  instance
    isPartialorder:Family : â{I : ð° ð} -> isPartialorder (â² (I -> A) â²)
    isPartialorder:Family = {!!}
    -- isPartialorder.antisym isPartialorder:Family (incl p) (incl q) = antisym (incl p) (incl q)
{-
-}
----------------------------------------------------------
-- Category of preorders

record isMonotone (A : Preorder ð) (B : Preorder ð) (f : SetoidHom â² â¨ A â© â² â² â¨ B â© â²) : ð° (ð ï½¤ ð) where
  field monotone : â{a b : â¨ A â©} -> (a â¤ b) -> â¨ f â© a â¤ â¨ f â© b

-- record isMonotone {A : ð° _} {B : ð° _} {{_ : Preorder ð on A}} {{_ : Preorder ð on B}} (f : (A -> B) :& isSetoidHom) : ð° (ð ï½¤ ð) where
--   field monotone : â{a b : A} -> (a â¤ b) -> â¨ f â© a â¤ â¨ f â© b
open isMonotone {{...}} public

-- record isMonotone {A : ð° ð} {B : ð° ð} {{_ : isPreorder A}} {{_ : isPreorder B}} (f : A -> B) : ð° (ð ï½¤ ð) where
--   field monotone : â{a b : A} -> (a â¤ b) -> f a â¤ f b

Monotone : (A : Preorder ð) (B : Preorder ð) -> ð° (ð ï½¤ ð)
Monotone A B = _ :& isMonotone A B

module _ {A : Preorder ð} {B : Preorder ð} where
  instance
    isSetoid:Monotone : isSetoid (Monotone A B)
    isSetoid:Monotone = isSetoid:byDef (Î» f g -> â¨ f â© â¼ â¨ g â©) refl sym _â_
    -- isSetoid._â¼'_ isSetoid:Monotone f g = â¨ f â© â¼' â¨ g â©
    -- isSetoid.isEquivRel:â¼ isSetoid:Monotone = {!!}

-- unquoteDecl Monotone makeMonotone = #struct "Monotone" (quote isMonotone) "f" Monotone makeMonotone

{-
Category:Preorder : (ð : ð) -> Category _
â¨ Category:Preorder ð â© = Preorder ð
ICategory.Hom (of Category:Preorder ð) = Monotone
ICategory._â£_ (of Category:Preorder ð) f g = El f â¡ El g
ICategory.IEquiv:â£ (of Category:Preorder ð) = {!!}
ICategory.id (of Category:Preorder ð) = {!!}
ICategory._â_ (of Category:Preorder ð) = {!!}
ICategory.unit-l-â (of Category:Preorder ð) = {!!}
ICategory.unit-r-â (of Category:Preorder ð) = {!!}
ICategory.unit-2-â (of Category:Preorder ð) = {!!}
ICategory.assoc-l-â (of Category:Preorder ð) = {!!}
ICategory.assoc-r-â (of Category:Preorder ð) = {!!}
ICategory._â_ (of Category:Preorder ð) = {!!}
-}







{-
  record _<_ (a b : A) : ð° ð where
    constructor _,_
    field Ï-â¤ : a â¤ b
    field Ï-â : Â¬ a â¼ b

  open _<_ public
-}
  -- a < b = a â¤ b Ã-ð° (a â¼ b -> ð-ð°)



module _ {ð : ð ^ 3} {A : ð° _} {{_ : Preorder ð on A}} where
  by-â¼-â¤_ : {a b : A} -> (a â¼ b) -> a â¤ b
  by-â¼-â¤_ p = transp-â¤ refl p reflexive

  å½reflexive = by-â¼-â¤_

  infixl 10 by-â¼-â¤_

  _â¨_â©-â¤_ : (x : A) {y : A} {z : A} â x â¤ y â y â¤ z â x â¤ z
  _ â¨ xâ¤y â©-â¤ yâ¤z = xâ¤y â¡ yâ¤z

  â¨â©-â¤-syntax : (x : A) {y z : A} â x â¤ y â y â¤ z â x â¤ z
  â¨â©-â¤-syntax = _â¨_â©-â¤_
  infixr 2 â¨â©-â¤-syntax
  infix  3 _â-â¤
  infixr 2 _â¨_â©-â¤_

  _â-â¤ : (x : A) â x â¤ x
  _ â-â¤ = reflexive

  _â¨_â©-â¼-â¤_ : (x : A) {y : A} {z : A} â x â¼ y â y â¤ z â x â¤ z
  _ â¨ xâ¤y â©-â¼-â¤ yâ¤z = {!!} -- xâ¤y â¡ yâ¤z

  â¨â©-â¼-â¤-syntax : (x : A) {y z : A} â x â¼ y â y â¤ z â x â¤ z
  â¨â©-â¼-â¤-syntax = _â¨_â©-â¼-â¤_
  infixr 2 â¨â©-â¼-â¤-syntax
  infixr 2 _â¨_â©-â¼-â¤_

  _â¨_â©-â¤-â¼_ : (x : A) {y : A} {z : A} â x â¤ y â y â¼ z â x â¤ z
  _ â¨ xâ¤y â©-â¤-â¼ yâ¤z = {!!} -- xâ¤y â¡ yâ¤z

  â¨â©-â¤-â¼-syntax : (x : A) {y z : A} â x â¤ y â y â¼ z â x â¤ z
  â¨â©-â¤-â¼-syntax = _â¨_â©-â¤-â¼_
  infixr 2 â¨â©-â¤-â¼-syntax
  infixr 2 _â¨_â©-â¤-â¼_

{-

-}








{-
  _â¨_â©-â¤_ : (x : A) {y : A} {z : A} â x â¤ y â y â¤ z â x â¤ z
  _ â¤â¨ xâ¤y â© yâ¤z = xâ¤y â¡ yâ¤z

  â¤â¨â©-syntax : (x : A) {y z : A} â x â¤ y â y â¤ z â x â¤ z
  â¤â¨â©-syntax = _â¨_â©-â¤_
  infixr 2 â¤â¨â©-syntax
  infix  3 _â-â¤
  infixr 2 _â¨_â©-â¤_

  _â-â¤ : (x : A) â x â¤ x
  _ â-â¤ = reflexive

  _â¨_â©-â¼-â¤_ : (x : A) {y : A} {z : A} â x â¼ y â y â¤ z â x â¤ z
  _ â¼â¨ xâ¤y â©â¤ yâ¤z = {!!} -- xâ¤y â¡ yâ¤z

  â¨â©-â¼-â¤-syntax : (x : A) {y z : A} â x â¼ y â y â¤ z â x â¤ z
  â¨â©-â¼-â¤-syntax = _â¨_â©-â¼-â¤_
  infixr 2 â¨â©-â¼-â¤-syntax
  infixr 2 _â¨_â©-â¼-â¤_

  _â¨_â©-â¤-â¼_ : (x : A) {y : A} {z : A} â x â¤ y â y â¼ z â x â¤ z
  _ â¤â¨ xâ¤y â©â¼ yâ¤z = {!!} -- xâ¤y â¡ yâ¤z

  â¨â©-â¤-â¼-syntax : (x : A) {y z : A} â x â¤ y â y â¼ z â x â¤ z
  â¨â©-â¤-â¼-syntax = _â¨_â©-â¤-â¼_
  infixr 2 â¨â©-â¤-â¼-syntax
  infixr 2 _â¨_â©-â¤-â¼_
-}




  -- _â¼â¨_â©-â¤_ : (x : A) {y : A} {z : A} â x â¼ y â y â¤ z â x â¤ z
  -- _ â¼â¤â¨ xâ¤y â© yâ¤z = {!!} -- xâ¤y â¡ yâ¤z

  -- â¼â¤â¨â©-syntax : (x : A) {y z : A} â x â¼ y â y â¤ z â x â¤ z
  -- â¼â¤â¨â©-syntax = _â¼â¨_â©-â¤_
  -- infixr 2 â¼â¤â¨â©-syntax
  -- -- infix  3 _â-â¤
  -- infixr 2 _â¼â¨_â©-â¤_



{-
{-
unquoteDecl Preorder preorder = #struct "PreOrd" (quote isPreorder) "A" Preorder preorder

-}


-}
{-
module _ {A : ð° ð} {{_ : isPreorder A}} where
  infix 30 _<_
  _<_ : A -> A -> ð° ð
  a < b = (a â¤ b) Ã-ð° (a â¡ b -> ð-ð°)

  instance
    Cast:â¡ââ¤ : â{a b : A} -> Cast (a â¡ b) IAnything (a â¤ b)
    Cast.cast (Cast:â¡ââ¤ {a = a} {b}) e = transport (Î» i -> e (~ i) â¤ b) reflexive


-- record isPreorderHom {A B : Preorder} (f : â¨ A â© -> â¨ B â©) : ð°â where

-- record PreorderHom (A B : Preorder) : ð°â where

instance
  -- ICategory:Preorder : ICategory Preorder (ð , ð ,-)
  -- ICategory:Preorder = {!!}
{-
  ICategory.Hom ICategory:Preorder = PreorderHom
  ICategory.id ICategory:Preorder = {!!}
  ICategory._â_ ICategory:Preorder = {!!}
-}

  isPreorder:â : isPreorder â
  isPreorder._â¤_ isPreorder:â = _â¤-â_
  isPreorder.reflexive isPreorder:â = reflexive-â
  isPreorder.trans-â¤ isPreorder:â = trans-â¤-â




--------------------------------------------------------------------
-- == Concatenation of preorders

module _ {A : ð° ð} {B : ð° ð} {{_ : isPreorder A}} {{_ : isPreorder B}} where

  data _â¤-â_ : (a b : A +-ð° B) -> ð° ð where
    left-â¤ : â{a b : A} -> a â¤ b -> left a â¤-â left b
    right-â¤ : â{a b : B} -> a â¤ b -> right a â¤-â right b
    left-right-â¤ : â{a : A} {b : B} -> left a â¤-â right b


  trans-â¤-â : â{a b c} -> (a â¤-â b) -> (b â¤-â c) -> a â¤-â c
  trans-â¤-â (left-â¤ p) (left-â¤ q) = left-â¤ (trans-â¤ p q)
  trans-â¤-â (left-â¤ x) left-right-â¤ = left-right-â¤
  trans-â¤-â (right-â¤ p) (right-â¤ q) = right-â¤ (trans-â¤ p q)
  trans-â¤-â left-right-â¤ (right-â¤ x) = left-right-â¤

  reflexive-â : â{a} -> (a â¤-â a)
  reflexive-â {left x} = left-â¤ reflexive
  reflexive-â {just x} = right-â¤ reflexive


  instance
    isPreorder:+ : isPreorder (A +-ð° B)
    isPreorder._â¤_ isPreorder:+ = _â¤-â_
    isPreorder.reflexive isPreorder:+ {a = a} = reflexive-â {a}
    isPreorder.trans-â¤ isPreorder:+ {a = a} = trans-â¤-â {a = a}


_â-Preorder_ : Preorder ð -> Preorder ð -> Preorder ð
A â-Preorder B = preorder (â¨ A â© +-ð° â¨ B â©)

instance
  INotation:DirectSum:Preorder : INotation:DirectSum (Preorder ð)
  INotation:DirectSum._â_ INotation:DirectSum:Preorder = _â-Preorder_


--------------------------------------------------------------------
-- == Example instances

instance
  isPreorder:â¤ : â{ð} -> isPreorder (Lift {j = ð} ð-ð°)
  isPreorder._â¤_ isPreorder:â¤ a b = `ð`
  isPreorder.reflexive isPreorder:â¤ = lift tt
  isPreorder.trans-â¤ isPreorder:â¤ a b = lift tt

-}
