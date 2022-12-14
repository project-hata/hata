
module Verification.Core.Category.Std.RelativeMonad.Finitary.Construction.Abstracted where

open import Verification.Conventions hiding (_β_)

open import Verification.Core.Setoid
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits

open import Verification.Core.Category.Std.RelativeMonad.Definition
-- open import Verification.Core.Category.Std.Monad.Definition

open import Verification.Core.Data.Indexed.Duplicate
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.FiniteIndexed.Definition
-- open import Verification.Core.Data.FiniteIndexed.Instance.Category
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element

open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition




-----------------------------------------
-- NOTE: it seems that this concept does
--       not work.
--
-- At least, it is likely that there is no
-- monad instance here. The problem is that
-- when defining substitution (reext), that
-- we have to substitute quantified terms.
-- But since we do not have quantifications
-- on the inside, we need to move them to the outside.
-- Even if this works, this is rather messy,
-- since then all the quantifications of all
-- the terms to be substituted accumulate.
--

module _ {I : π° π} (t' : FinitaryRelativeMonad I) where

  private macro t = #structureOn β¨ t' β©

  record Abstractedα΅ (a : ππ’π§ππ± I) (i : I) : π° π where
    constructor β[_]_
    field fst : ππ’π§ππ± I
    field snd : t (a β fst) β i


  πππ π‘α΅ : ππ’π§ππ± I -> ππ± I (ππ§π’π― π)
  πππ π‘α΅ = indexed β Abstractedα΅

  macro πππ π‘ = #structureOn πππ π‘α΅

module _ {I : π° π} {t' : FinitaryRelativeMonad I} where
  private macro t = #structureOn β¨ t' β©

  map-πππ π‘ : β{a b : ππ’π§ππ± I} -> a βΆ b -> πππ π‘ t a βΆ πππ π‘ t b
  map-πππ π‘ f i (β[ x ] term)= β[ x ] mapOf t (f βββ id) i term

  instance
    isFunctor:Abstracted : isFunctor (ππ’π§ππ± I) (ππ± I (ππ§π’π― π)) (πππ π‘ t)
    isFunctor.map isFunctor:Abstracted = map-πππ π‘
    isFunctor.isSetoidHom:map isFunctor:Abstracted = {!!}
    isFunctor.functoriality-id isFunctor:Abstracted = {!!}
    isFunctor.functoriality-β isFunctor:Abstracted = {!!}

  repure-πππ π‘ : β {a} -> πππ I a βΆ πππ π‘ t a
  repure-πππ π‘ i x = β[ β₯ ] (mapOf t ΞΉβ i (repure i x))

  reext-πππ π‘ : β {a b} -> πππ I a βΆ πππ π‘ t b -> πππ π‘ t a βΆ πππ π‘ t b
  reext-πππ π‘ f i (β[ v ] term) = β[ v ] (reext {!!} i term)


  instance
    isRelativeMonad:πππ π‘ : isRelativeMonad (πππ I) (πππ π‘ t)
    isRelativeMonad.repure isRelativeMonad:πππ π‘ = repure-πππ π‘
    isRelativeMonad.reext isRelativeMonad:πππ π‘ = reext-πππ π‘
    isRelativeMonad.reunit-l isRelativeMonad:πππ π‘ = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:πππ π‘ = {!!}
    isRelativeMonad.reassoc isRelativeMonad:πππ π‘ = {!!}


