
module Verification.Core.Setoid.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition


record โผ-Base {A : ๐ฐ ๐} (R : A -> A -> ๐ฐ ๐) (a : A) (b : A) : ๐ฐ (๐) where
  constructor incl
  field โจ_โฉ : R a b
  -- incl : R a b -> โผ-Base R a b -- a โผ[ R ] b
open โผ-Base public

module _ {A : ๐ฐ ๐} (S : isSetoid {๐} A) where
  private instance _ = S

  isSetoid:โผ-Base : isSetoid A
  isSetoid:โผ-Base = isSetoid:byDef
    (โผ-Base (_โผ_ {{S}}))
    (incl refl)
    (ฮป p -> incl (sym โจ p โฉ))
    (ฮป p q -> incl (โจ p โฉ โ โจ q โฉ))



module _ {A : ๐ฐ ๐} {B : ๐ฐ ๐} {{_ : isSetoid {๐โ} A}} {{_ : isSetoid {๐โ} B}} where
  instance
    isSetoid:ร : isSetoid (A ร B)
    isSetoid:ร = isSetoid:byDef (ฮป (aโ , bโ) (aโ , bโ) -> (aโ โผ aโ) ร (bโ โผ bโ))
                 (refl , refl)
                 (ฮป (p , q) -> (p โปยน , q โปยน))
                 (ฮป (pโ , qโ) (pโ , qโ) -> (pโ โ pโ , qโ โ qโ))

-- instance
--   isEquivRel:โกโผ-Base : โ{A : ๐ฐ ๐} -> isEquivRel (โผ-Base (_โก_ {A = A}))
--   isEquivRel.refl isEquivRel:โกโผ-Base = incl refl-Path
--   isEquivRel.sym isEquivRel:โกโผ-Base (incl p) = incl (sym-Path p)
--   isEquivRel._โ_ isEquivRel:โกโผ-Base (incl p) (incl q) = incl (trans-Path p q)

-- instance
--   isEquivRel:โฃโผ-Base : โ{A : ๐ฐ ๐} -> isEquivRel (โผ-Base (_โฃ_ {A = A}))
--   isEquivRel.refl isEquivRel:โฃโผ-Base = incl refl-StrId
--   isEquivRel.sym isEquivRel:โฃโผ-Base (incl p) = incl (p โปยน)
--   isEquivRel._โ_ isEquivRel:โฃโผ-Base (incl p) (incl q) = incl (p โ q)

-- record isSetoid ๐ A {{_ : From (๐ฐ ๐) A}} : ๐ฐ (๐ ๏ฝค ๐ โบ) where
-- open isTypoid {{...}} public


{-
record isSetoid {๐ ๐ : ๐} (A : ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐ โบ) where
  constructor setoid
  field _โผ_ : A -> A -> ๐ฐ ๐
        refl : โ{x : A} -> x โผ x
        sym : โ{x y : A} -> x โผ y -> y โผ x
        _โ_ : โ{x y z : A} -> x โผ y -> y โผ z -> x โผ z

  infixl 30 _โ_

  -- _โผ_ : A -> A -> ๐ฐ (๐)
  -- _โผ_ = โผ-Base _โผ'_

  -- field {{isEquivRel:โผ}} : isEquivRel _โผ_

  _โ_ : A -> A -> ๐ฐ (๐)
  _โ_ a b = ยฌ a โผ b
open isSetoid {{...}} public

module _ {X : ๐ฐ _} {{_ : X is Setoid ๐}} where
  instance
    Notation-Inverse:Equiv : {x y : X} -> Notation-Inverse (x โผ y) (y โผ x)
    Notation-Inverse:Equiv Notation-Inverse.โปยน = sym

-}


Setoid : (๐ : ๐ ^ 2) -> ๐ฐ _
Setoid ๐ = ๐ฐ (๐ โ 0) :& isSetoid {๐ โ 1}

record isSetoidHom {๐ ๐ : ๐ ^ 2} (A : Setoid ๐) (B : Setoid ๐) (f : โจ A โฉ -> โจ B โฉ) : ๐ฐ (๐ ๏ฝค ๐) where
-- record isSetoidHom {๐ ๐ : ๐ ^ 2} {A : ๐ฐ _} {B : ๐ฐ _} {{_ : Setoid ๐ on A}} {{_ : Setoid ๐ on B}} (f : A -> B) : ๐ฐ (๐ ๏ฝค ๐)where
  field cong-โผ : โ{a b} -> a โผ b -> f a โผ f b
open isSetoidHom {{...}} public


SetoidHom : (A : Setoid ๐) (B : Setoid ๐) -> ๐ฐ _
SetoidHom A B = (โจ A โฉ -> โจ B โฉ) :& isSetoidHom A B

module _ {A : Setoid ๐} {B : Setoid ๐} where
  congOf-โผ : (f : SetoidHom A B) -> โ{a b : โจ A โฉ} -> a โผ b -> โจ f โฉ a โผ โจ f โฉ b
  congOf-โผ f = cong-โผ

  infixl 200 _-cong-โผ_
  _-cong-โผ_ = congOf-โผ


module _ {A : Setoid ๐} {B : Setoid ๐} where
  _โผ-SetoidHom_ : (f g : SetoidHom A B) -> ๐ฐ _
  _โผ-SetoidHom_ f g = โ{a} -> โจ f โฉ a โผ โจ g โฉ a

  instance
    isSetoid:SetoidHom : isSetoid (SetoidHom A B)
    isSetoid:SetoidHom = isSetoid:byDef _โผ-SetoidHom_ refl (ฮป p -> sym p) (ฮป p q -> p โ q)



{-
module _ {A : Setoid ๐} {B : Setoid ๐} where
  _โผ-SetoidHom_ : (f g : SetoidHom A B) -> ๐ฐ _
  _โผ-SetoidHom_ f g = โ{a} -> โจ f โฉ a โผ โจ g โฉ a

  instance
    isEquivRel:โผ-SetoidHom : isEquivRel (โผ-Base _โผ-SetoidHom_)
    isEquivRel.refl isEquivRel:โผ-SetoidHom = incl (ฮป {a} โ refl)
    isEquivRel.sym isEquivRel:โผ-SetoidHom (incl p) = incl (p โปยน)
    isEquivRel._โ_ isEquivRel:โผ-SetoidHom (incl p) (incl q) = incl (p โ q)

  instance
    isSetoid:SetoidHom : isSetoid _ (SetoidHom A B)
    isSetoid._โผ'_ isSetoid:SetoidHom = _โผ-SetoidHom_


instance
  isSetoid:โฆ๐ซโฆ : โ{๐ ๐ : ๐} {A : ๐ฐ ๐} -> {{_ : isSetoid ๐ A}} -> {P : ๐ซ A} -> isSetoid _ โฆ P โฆ
  isSetoid._โผ'_ isSetoid:โฆ๐ซโฆ (a โข _) (b โข _) = a โผ b
  isEquivRel.refl (isSetoid.isEquivRel:โผ isSetoid:โฆ๐ซโฆ) {x = a โข x} = incl refl
  isEquivRel.sym (isSetoid.isEquivRel:โผ isSetoid:โฆ๐ซโฆ) {a โข x} {aโ โข xโ} (incl p) = incl (sym p)
  isEquivRel._โ_ (isSetoid.isEquivRel:โผ isSetoid:โฆ๐ซโฆ) {a โข x} {aโ โข xโ} {aโ โข xโ} (incl p) (incl q) = incl (p โ q)


-------------------------------------------------------------------------------
-- inheriting setoid structures

-}
module _ {UU : ๐ฐ ๐} {{U : hasU UU ๐ ๐}} {{_ : isSetoid {๐} (getU U)}} where
  _โผ-hasU_ : UU -> UU -> ๐ฐ _
  _โผ-hasU_ a b = destructEl U a โผ destructEl U b

  -- isEquivRel:hasU : isEquivRel (โผ-Base _โผ-hasU_)
  -- isEquivRel.refl isEquivRel:hasU = incl โจ refl โฉ
  -- isEquivRel.sym isEquivRel:hasU (incl p) = incl (โจ sym (incl p) โฉ)
  -- isEquivRel._โ_ isEquivRel:hasU (incl p) (incl q) = incl โจ ((incl p) โ (incl q)) โฉ

  isSetoid:hasU : isSetoid UU
  isSetoid._โผ_ isSetoid:hasU = โผ-Base _โผ-hasU_
  isSetoid.refl isSetoid:hasU = incl refl
  isSetoid.sym isSetoid:hasU = ฮป p -> incl (sym โจ p โฉ)
  isSetoid._โ_ isSetoid:hasU = ฮป p q -> incl ( โจ p โฉ โ โจ q โฉ )
  -- isSetoid._โผ'_ isSetoid:hasU = _โผ-hasU_
  -- isSetoid.isEquivRel:โผ isSetoid:hasU = isEquivRel:hasU



--------------------------------------------------------------------------------
-- Subsetoids




--
-- NOTE: We (probably) use the instance argument form of passing the setoid structure here,
--       such that we can state `isSubsetoid P` instead of saying `isSubsetoid X P`.
--
--       The same pattern is used for submonoid, etc. in Core/Algebra.
--
--       The alternative, that we don't use, would be:
--       '''
--       record isSubsetoid {๐ : ๐ ^ 2} (X : Setoid ๐) (P : ๐ซ โจ X โฉ) : ๐ฐ ๐ where
--       '''
--
record isSubsetoid {๐ : ๐ ^ 2} {X : ๐ฐ' _} {{_ : Setoid ๐ on X}} (P : X -> Prop (๐ โ 0)) : ๐ฐ ๐ where
  field transp-โผ : โ{a b : X} -> a โผ b -> a โ P -> b โ P

open isSubsetoid {{...}} public

Subsetoid : {๐ : ๐ ^ 2} (X : Setoid ๐) -> ๐ฐ _
Subsetoid X = ๐ซ-๐ฐ โจ X โฉ :& isSubsetoid

module _ {X : ๐ฐ' _} {{SX : Setoid ๐ on X}} where
  transpOf-โผ : (V : Subsetoid โฒ X โฒ) -> โ{a b : X} -> a โผ b -> a โ V -> b โ V
  transpOf-โผ V aโผb aโV = transp-โผ aโผb aโV


---------------------------------------------------------------
-- induced subsetoid


isSetoid:FullSubsetoid : (X : Setoid ๐) {A : ๐ฐ ๐} (ฯ : A -> โจ X โฉ) -> isSetoid A
isSetoid:FullSubsetoid X ฯ = isSetoid:byDef (โผ-Base (ฮป a b -> ฯ a โผ ฯ b))
  (incl refl)
  (ฮป p -> incl (sym โจ p โฉ))
  (ฮป p q -> incl (โจ p โฉ โ โจ q โฉ))

-- isSetoid._โผ'_ (isSetoid:FullSubsetoid X ฯ) = ฮป a b -> ฯ a โผ ฯ b
-- isSetoid.isEquivRel:โผ (isSetoid:FullSubsetoid X ฯ) = equivRel (incl refl) (ฮป p -> incl (sym โจ p โฉ)) (ฮป p q -> incl (โจ p โฉ โ โจ q โฉ))

isContr-Std : (A : ๐ฐ _) {{_ : Setoid ๐ on A}} -> ๐ฐ _
isContr-Std A = โ ฮป (a : A) -> โ (b : A) -> a โผ b


{-

-- instance
--   isEquivRel:โซ : โ{A : ๐ฐ ๐} -> isEquivRel (โผ-Base (ฮป (P Q : A -> ๐ฐ ๐) -> P โซ Q))
--   isEquivRel.refl isEquivRel:โซ = incl ((ฮป x -> x) , (ฮป x -> x))
--   isEquivRel.sym isEquivRel:โซ (incl (P , Q)) = incl (Q , P)
--   isEquivRel._โ_ isEquivRel:โซ (incl (Pโ , Qโ)) (incl (Pโ , Qโ)) = incl ((ฮป x -> Pโ (Pโ x)) , (ฮป x -> Qโ (Qโ x)))

-- instance
--   isEquivRel:โซ : โ{๐ : ๐ ^ 2} -> โ{A : Setoid ๐} -> isEquivRel (โผ-Base (ฮป (P Q : Subsetoid A) -> โจ P โฉ โซ โจ Q โฉ))
--   isEquivRel.refl isEquivRel:โซ = incl ((ฮป x -> x) , (ฮป x -> x))
--   isEquivRel.sym isEquivRel:โซ (incl (P , Q)) = incl (Q , P)
--   isEquivRel._โ_ isEquivRel:โซ (incl (Pโ , Qโ)) (incl (Pโ , Qโ)) = incl ((ฮป x -> Pโ (Pโ x)) , (ฮป x -> Qโ (Qโ x)))

-- instance
--   isSetoid:Subsetoid : โ{๐ : ๐ ^ 2} -> {X : Setoid ๐} -> isSetoid _ (Subsetoid X)
--   isSetoid._โผ'_ isSetoid:Subsetoid A B = โจ A โฉ โซ โจ B โฉ

--------------------------------------------------------------------------------
-- Quotients
-}

data _/-๐ฐ_ {๐ ๐ : ๐} (A : ๐ฐ ๐) (R : A -> A -> ๐ฐ ๐) : ๐ฐ (๐ ) where
  [_] : A -> A /-๐ฐ R

-- private
--   module _ {๐ ๐ : ๐} {A : ๐ฐ ๐} -> {R : A -> A -> ๐ฐ ๐} -> {{_ : isEquivRel R}} where
--     lem-10 : โ{a : A /-๐ฐ R} -> 



instance
  isSetoid:/-๐ฐ : {๐ ๐ : ๐} {A : ๐ฐ ๐} -> {R : A -> A -> ๐ฐ ๐} -> {{_ : isEquivRel R}} -> isSetoid (A /-๐ฐ R)
  isSetoid._โผ_ (isSetoid:/-๐ฐ {R = R}) = โผ-Base (ฮป {[ a ] [ b ] -> R a b}) -- ฮป {[ a ] [ b ] -> โผ-Base R a b}
  isSetoid.refl (isSetoid:/-๐ฐ {R = R}) {[ x ]} = incl refl-Equiv
  isSetoid.sym (isSetoid:/-๐ฐ {R = R}) {[ x ]} {[ y ]} (incl p) = incl (sym-Equiv p)
  isSetoid._โ_ (isSetoid:/-๐ฐ {R = R}) {[ x ]} {[ y ]} {[ z ]} (incl p) (incl q) = incl (p โ-Equiv q)
  -- setoid (ฮป {[ a ] [ b ] -> โผ-Base R a b})
  --                        (ฮป {x} โ {!!})
  --                        {!!}
  --                        {!!}
    -- (ฮป {[ x ]} -> refl-Equiv)
    -- {!!} {!!}
  -- isSetoid._โผ'_ (isSetoid:/-๐ฐ {R = R}) [ a ] [ b ] = R a b
  -- isEquivRel.refl (isSetoid.isEquivRel:โผ isSetoid:/-๐ฐ) {x = [ x ]} = incl refl-Equiv
  -- isEquivRel.sym (isSetoid.isEquivRel:โผ isSetoid:/-๐ฐ) {x = [ x ]} {y = [ y ]} (incl p) = incl (sym-Equiv p)
  -- isEquivRel._โ_ (isSetoid.isEquivRel:โผ isSetoid:/-๐ฐ) {x = [ x ]} {y = [ y ]} {z = [ z ]} (incl p) (incl q) = incl (p โ-Equiv q)

--------------------------------------------------------------------------------
-- Induced setoid


module _ {A : ๐ฐ ๐} {{_ : isSetoid {๐} A}} {I : ๐ฐ ๐} where
  _โผ-Family_ : (f g : I -> A) -> ๐ฐ _
  _โผ-Family_ f g = โ{i} -> f i โผ g i

  -- instance
  --   isEquivRel:โผ-Family : isEquivRel (โผ-Base _โผ-Family_)
  --   isEquivRel.refl isEquivRel:โผ-Family {f} = incl (ฮป {a} -> โจ refl {a = f a} โฉ)
  --   isEquivRel.sym isEquivRel:โผ-Family (incl p) = incl (โจ incl p โปยน โฉ)
  --   isEquivRel._โ_ isEquivRel:โผ-Family (incl p) (incl q) = incl (โจ incl p โ incl q โฉ)

  instance
    isSetoid:Family : isSetoid (I -> A)
    isSetoid:Family = isSetoid:byDef _โผ-Family_
      refl
      (ฮป p {i} -> sym (p {i}))
      (ฮป p q {i} -> p {i} โ q {i})

    -- isSetoid._โผ'_ isSetoid:Family f g = f โผ-Family g

    -- isEquivRel.refl (isSetoid.isEquivRel:โผ isSetoid:Family) = incl (โจ refl โฉ)
    -- isEquivRel.sym (isSetoid.isEquivRel:โผ isSetoid:Family) (incl p) = incl (โจ incl p โปยน โฉ)
    -- isEquivRel._โ_ (isSetoid.isEquivRel:โผ isSetoid:Family) (incl p) (incl q) = incl (โจ incl p โ incl q โฉ)

-------------------------------------------------------------------------------
-- Isomorphism of setoids




