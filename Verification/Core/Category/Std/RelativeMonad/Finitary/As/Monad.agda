
module Verification.Core.Category.Std.RelativeMonad.Finitary.As.Monad where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category

open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Duplicate
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition

-----------------------------------------
-- making finitary relative (sorted) monads into real monads

module _ {I : π° π} where
  record Reβ»ΒΉα΅ (M : FinitaryRelativeMonad I) (A : ππ± I (ππ§π’π― π)) (i : I) : π° π where
    constructor relβ»ΒΉ
    field fst : ππ’π§ππ± I
    field snd : ix (β¨ M β© fst) i
    field thd : πππ I fst βΆ A

  open Reβ»ΒΉα΅ public

  module _ (M : FinitaryRelativeMonad I) where
    Reβ»ΒΉα΅ : (A : ππ± I (ππ§π’π― π)) -> ππ± I (ππ§π’π― π)
    Reβ»ΒΉα΅ A = indexed (Reβ»ΒΉα΅ M A)

    macro Reβ»ΒΉ = #structureOn Reβ»ΒΉα΅


  module _ {Mα΅ : FinitaryRelativeMonad I} where

    private
      macro M = #structureOn β¨ Mα΅ β©

    map-Reβ»ΒΉ : β{a b : ππ± I (ππ§π’π― π)} -> (a βΆ b) -> Reβ»ΒΉ M a βΆ Reβ»ΒΉ M b
    map-Reβ»ΒΉ f i (relβ»ΒΉ as term values) = relβ»ΒΉ as term (values β f)

    instance
      isSetoidHom:map-Reβ»ΒΉ : β{a b : ππ± I (ππ§π’π― π)} -> isSetoidHom β² IndexedHom a b β² β² IndexedHom (Reβ»ΒΉα΅ M a) (Reβ»ΒΉα΅ M b) β² map-Reβ»ΒΉ
      isSetoidHom:map-Reβ»ΒΉ = record { cong-βΌ = Ξ» x i j β map-Reβ»ΒΉ (funExt x j) i }


    instance
      isFunctor:Reβ»ΒΉ : isFunctor (ππ± I (ππ§π’π― π)) (ππ± I (ππ§π’π― π)) (Reβ»ΒΉ M)
      isFunctor.map isFunctor:Reβ»ΒΉ = map-Reβ»ΒΉ
      isFunctor.isSetoidHom:map isFunctor:Reβ»ΒΉ = it
      isFunctor.functoriality-id isFunctor:Reβ»ΒΉ = Ξ» i β refl-β‘
      isFunctor.functoriality-β isFunctor:Reβ»ΒΉ = Ξ» i β refl-β‘

    -- isFunctor:M : isFunctor _ _ β¨ M β©
    -- isFunctor:M = it

    pure-Reβ»ΒΉ : β(a : ππ± I (ππ§π’π― π)) -> a βΆ Reβ»ΒΉ M a
    pure-Reβ»ΒΉ a i x = relβ»ΒΉ (incl (incl i)) (repure i incl) (Ξ» {iβ incl β x})

    join-Reβ»ΒΉ : β(a : ππ± I (ππ§π’π― π)) -> Reβ»ΒΉ M (Reβ»ΒΉ M a) βΆ Reβ»ΒΉ M a
    join-Reβ»ΒΉ _ i (relβ»ΒΉ as term values) =
      let

        -- the map `values` which gives us a `Reβ»ΒΉ M a` value for every `a` in `as`,
        -- can be projected to give us only the list of holes of the monad for a given `a`
        j : [ β¨ as β© ]αΆ  -> ππ’π§ππ± I
        j = (Ξ» (a , ap) β values a ap .fst)

        -- the sum of all these lists is the sum in the `ππ’π§ππ±` category
        β¨j = β¨αΆ  (indexed j)

        -- the `snd` part of the `Reβ»ΒΉ M a` value then gives us a `M ?` value
        -- for each a in as
        terms : β (a : [ β¨ as β© ]αΆ ) -> ix (M (j a)) (fst a)
        terms = Ξ»(a , ap) -> values a ap .snd

        -- we do have the injection functions
        ΞΉ-j : β(a : [ β¨ as β© ]αΆ ) -> j a βΆ β¨j
        ΞΉ-j = {!!}

        -- with which we can extend the terms
        terms' : β (a : [ β¨ as β© ]αΆ ) -> ix (M β¨j) (fst a)
        terms' = Ξ» a -> (mapOf M) (ΞΉ-j a) _ (terms a)

        -- these terms, since the dependency on a in the `β¨j` index of the monad
        -- is now gone, can be seen as morphisms in `ππ±`
        termsβ : πππ I as βΆ M β¨j
        termsβ = Ξ» a ap β terms' (a , ap)

        -- and can be lifted to a morphism on monads
        termsβ : M as βΆ M β¨j
        termsβ = reext termsβ

        -- which can finally be applied to the term value which we have,
        -- thus substituting the holes of the top level term with the smaller
        -- values for them
        term' : ix (M β¨j) i
        term' = termsβ i term


      in relβ»ΒΉ β¨j term' {!!}


    instance
      isMonad:Reβ»ΒΉ : isMonad (Reβ»ΒΉ M)
      isMonad.pure isMonad:Reβ»ΒΉ = pure-Reβ»ΒΉ
      isMonad.join isMonad:Reβ»ΒΉ = join-Reβ»ΒΉ
      isMonad.isNatural:pure isMonad:Reβ»ΒΉ = {!!}
      isMonad.isNatural:join isMonad:Reβ»ΒΉ = {!!}
      isMonad.unit-l-join isMonad:Reβ»ΒΉ = {!!}
      isMonad.unit-r-join isMonad:Reβ»ΒΉ = {!!}
      isMonad.assoc-join isMonad:Reβ»ΒΉ = {!!}



