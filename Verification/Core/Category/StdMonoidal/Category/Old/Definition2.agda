
-- {-# OPTIONS --syntactic-equality=1 #-}

{-# OPTIONS --warning=noInstanceWithExplicitArg #-}


module Verification.Core.Category.Std.Category.Structured.Monoidal.Definition2 where

open import Verification.Conventions
open import Verification.Core.Setoid
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Iso
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition


-- aaa = unit-l-ร

module _ {๐ : ๐ฐ ๐} {{_ : isCategory {๐} ๐}} {{_ : hasFiniteProducts โฒ ๐ โฒ}} where

  private instance
    _ : isSetoid ๐
    _ = isSetoid:byCategory

    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:โงผโงฝ

  -- TODO: embed these ones in the proofs below
  unit-l-โ : โ{a : ๐} -> a โ โค โถ a
  unit-l-โ = ฯโ

  โฯ : โ{a : ๐} -> a โถ โค โ a
  โฯ = โงผ intro-โค , id โงฝ

  [_]โฯc : โ{a : ๐} -> (โค โถ a) -> a โถ a โ a
  [_]โฯc f = โงผ intro-โค โ f , id โงฝ


{-
record isMonoidal (๐ : Category ๐) : ๐ฐ ๐ where
  field [โ]แต : โจ ๐ โฉ ร-๐ฐ โจ ๐ โฉ -> โจ ๐ โฉ
  field [Id]แต : โจ โค-๐๐๐ญ {๐} โฉ -> โจ ๐ โฉ
  field unit-l-โ : โ(a) -> [โ]แต ([Id]แต (lift tt) , a) โถ a

  field isFunctor:[โ] : isFunctor (๐ ร-๐๐๐ญ ๐) ๐ [โ]แต
  field isFunctor:[Id] : isFunctor (โค-๐๐๐ญ) ๐ [Id]แต

  [โ] : Functor (๐ ร-๐๐๐ญ ๐) ๐
  [โ] = [โ]แต since isFunctor:[โ]

  [Id] : Functor โค-๐๐๐ญ ๐
  [Id] = [Id]แต since isFunctor:[Id]

  -- field isNatural:unit-l-โ : isNatural ([ [Id] ]โฯc โ-๐๐๐ญ [โ]) id-๐๐๐ญ unit-l-โ
  field isNatural:unit-l-โ : isNatural (โงผ intro-โค โ [Id] , id-๐๐๐ญ {๐ = ๐} โงฝ โ-๐๐๐ญ [โ]) id-๐๐๐ญ unit-l-โ
-}


module _ {๐ : Category ๐} {๐ : Category ๐} {โฐ : Category ๐} {โฑ : Category ๐} where
  postulate
    _โโโ-๐๐๐ญ_ : Functor ๐ ๐ -> Functor โฐ โฑ -> Functor (๐ ร-๐๐๐ญ โฐ) (๐ ร-๐๐๐ญ โฑ)
  -- _โโโ-๐๐๐ญ_ = {!!}

module _ {๐ : Category ๐} {๐ : Category ๐} {โฐ : Category ๐} where
  ฮฑ-๐๐๐ญ : Functor ((๐ ร-๐๐๐ญ ๐) ร-๐๐๐ญ โฐ) (๐ ร-๐๐๐ญ (๐ ร-๐๐๐ญ โฐ))
  ฮฑ-๐๐๐ญ = {!!}

private
  โงผ_โงฝโจ = โงผ_โงฝ-๐๐๐ญ
  infixl 40 _โโจ_
  _โโจ_ = _โ-๐๐๐ญ_
  idโจ = id-๐๐๐ญ
  idโฎ = id-๐๐๐ญ
  ฯโโฎ = ฯโ-๐๐๐ญ
  ฯโโฎ = ฯโ-๐๐๐ญ


record MonoidalType (๐ : Category ๐) : ๐ฐ ๐ where
  field [โ] : Functor (๐ ร-๐๐๐ญ ๐) ๐
  field [Id] : Functor (โค-๐๐๐ญ {๐}) ๐

open MonoidalType {{...}} public


module _ {๐ : Category ๐} {{_ : MonoidalType ๐}} where
  โ- : โ{๐ณ : Category ๐} -> Functor ๐ณ (๐ ร-๐๐๐ญ ๐) -> Functor ๐ณ ๐
  โ- F = F โ-๐๐๐ญ [โ]

  module _ {๐ณ ๐ด : Category ๐} where
    postulate
      _โ_ : (F : Functor ๐ณ ๐) -> (G : Functor ๐ด ๐) -> Functor (๐ณ ร-๐๐๐ญ ๐ด) ๐

    module _ {F F' : Functor ๐ณ ๐} {G G' : Functor ๐ด ๐} where
      postulate
        _โโโ_ : F โ F' -> G โ G' -> (F โ G) โ (F' โ G')

  module _ {๐ณ ๐ด ๐ตโ ๐ตโ : Category ๐} where
    postulate
      factor-โ-โ : {Aโ : Functor ๐ตโ ๐ณ} {Aโ : Functor ๐ตโ ๐ด}
                   -> {F : Functor ๐ณ ๐} -> {G : Functor ๐ด ๐}
                   -> ((Aโ โโจ F) โ (Aโ โโจ G)) โ (Aโ โโโ-๐๐๐ญ Aโ) โโจ (F โ G)

    -- _โ_ F G = (F โโโ-๐๐๐ญ G) โ-๐๐๐ญ [โ]

        -- _โโโ_ F G = {!!}

  postulate cong-โ : โ{๐ณ : Category ๐} {F G : Functor ๐ณ (๐ ร-๐๐๐ญ ๐)}
                  -> F โ G -> โ- F โ โ- G

  -- _โ_ : โ{๐ณ ๐ด : Category ๐} -> (F : Functor ๐ณ ๐) -> (G : Functor ๐ด ๐) -> Functor (๐ณ ร-๐๐๐ญ ๐ด) ๐
  -- _โ_ F G = (F โโโ-๐๐๐ญ G) โ-๐๐๐ญ [โ]


  !Id : โ{๐ณ : Category ๐} -> Functor ๐ณ ๐
  !Id = intro-โค-๐๐๐ญ โ-๐๐๐ญ [Id]

  Id = [Id]


module _ {๐ : Category ๐} where -- {๐ : Category ๐} where
  -- s-๐๐๐ญ : Functor (๐ ร-๐๐๐ญ ๐) (๐ ร-๐๐๐ญ ๐)
  -- s-๐๐๐ญ = โงผ ฯโ-๐๐๐ญ , ฯโ-๐๐๐ญ โงฝ-๐๐๐ญ

  -- ฯ-๐๐๐ญ : โ{๐ณ : Category ๐}
  --         -> {F : Functor ๐ณ (๐ ร-๐๐๐ญ ๐)}
  --         -> {G : Functor ๐ณ (๐ ร-๐๐๐ญ ๐)}
  --         -> F โ-๐๐๐ญ s-๐๐๐ญ โ G
  -- ฯ-๐๐๐ญ = {!!}

  ฯ-๐๐๐ญ : โ{๐ณ : Category ๐}
          -> {F : Functor ๐ณ (๐)}
          -> {G : Functor ๐ณ (๐)}
          -> โงผ F , G โงฝ-๐๐๐ญ โ โงผ G , F โงฝ-๐๐๐ญ
  ฯ-๐๐๐ญ = {!!}


  -- idแถ 

module _ {๐ : Category ๐} {๐ : Category ๐} {โฐ : Category ๐} where
  NaturalOverLeft : (Functor ๐ ๐) -> (Functor ๐ โฐ) -> Functor ๐ โฐ -> ๐ฐ _
  NaturalOverLeft Over F G = Natural F (Over โ-๐๐๐ญ G)

record MonoidalFunc {๐ : Category ๐} (๐แต : MonoidalType ๐) : ๐ฐ (๐ โบ) where
  private instance _ = ๐แต

  field unit-l-โ : โ{X : Category ๐} -> โ(F : Functor X ๐) -> (Id โ F) โ ฯโโฎ โโจ F
  field unit-r-โ : โ{X : Category ๐} -> โ(F : Functor X ๐) -> (F โ Id) โ ฯโโฎ โโจ F
  field assoc-l-โ : โ{๐ณ ๐ด ๐ต : Category ๐}
                    -> โ{F : Functor ๐ณ ๐}
                    -> โ{G : Functor ๐ด ๐}
                    -> โ{H : Functor ๐ต ๐}
                    -> ((F โ G) โ H) โ ฮฑ-๐๐๐ญ โโจ (F โ (G โ H))

open MonoidalFunc {{...}} public


-- record MonoidalFunc {๐ : Category ๐} (๐แต : MonoidalType ๐) : ๐ฐ (๐ โบ) where
module _ {๐ : Category ๐} {{๐แต : MonoidalType ๐}} {{๐แถ? : MonoidalFunc ๐แต}} where

  lhs : โ{๐ณ ๐ด : Category ๐} -> {F : Functor ๐ณ ๐} {G : Functor ๐ด ๐}
      -- -> ((F โ Id) โ G) โ ((ฯโโฎ โโจ F) โ (idโฎ โโจ G))
      -> ((F โ Id) โ G) โ ((ฯโโฎ โโโ-๐๐๐ญ idโฎ {๐ = ๐ด}) โโจ (F โ G))
  lhs {F = F} {G} = (unit-r-โ F โโโ sym-โ (unit-l-โ-๐๐๐ญ {F = G})) โ-โ factor-โ-โ

  rhs : โ{๐ณ ๐ด : Category ๐} -> {F : Functor ๐ณ ๐} {G : Functor ๐ด ๐}
      -- -> ((F โ Id) โ G) โ ((ฯโโฎ โโจ F) โ (idโฎ โโจ G))
      -> _
  rhs {F = F} {G = G}
    = ((F โ Id) โ G)            โจ assoc-l-โ {F = F} {Id} {G} โฉ-โ
      ฮฑ-๐๐๐ญ โโจ (F โ (Id โ G))    โจ refl-โ {A = ฮฑ-๐๐๐ญ} โโโ-๐๐๐ญ (refl-โ {A = F} โโโ unit-l-โ G) โฉ-โ
      ฮฑ-๐๐๐ญ โโจ (F โ (ฯโโฎ โโจ G))    โ-โ


    -- ((F โ Id) โ G) โ ((ฯโโฎ โโโ-๐๐๐ญ idโฎ {๐ = ๐ด}) โโจ (F โ G))


    -- let X = unit-r-โ {F = F}
    --     Y : G โ (id โโจ G)
    --     Y = sym-โ unit-l-โ-๐๐๐ญ
    -- in _โโโ_ X Y


  -- (unit-r-โ {F = F} โโโ refl-โ {A = G})

  -- field triangle-โ : (refl-โ โโโ unit-l-โ) โ-โ {!!} โก assoc-l-โ โ-โ ?


  --โ- โงผ !Id , idโจ โงฝโจ) โ idโจ

-- record MonoidalFunc {๐ : Category ๐} (๐แต : MonoidalType ๐) : ๐ฐ ๐ where
--   private instance _ = ๐แต

--   field unit-l-โ : (โ- โงผ !Id , idโจ โงฝโจ) โ idโจ
--   field unit-r-โ : (โ- โงผ idโจ , !Id โงฝโจ) โ idโจ
--   field assoc-l-โ : NaturalOverLeft ฮฑ-๐๐๐ญ
--                             (โ-(โ-( idโจ โโโ-๐๐๐ญ idโจ) โโโ-๐๐๐ญ idโจ))
--                             (โ-(idโจ โโโ-๐๐๐ญ โ-( idโจ โโโ-๐๐๐ญ idโจ)))





  -- field triangle-โ : ((sym-โ unit-l-โ โ-โ cong-โ (ฯ-๐๐๐ญ {F = !Id} {G = idโจ})) โ-โ unit-r-โ) โก (id-๐๐ฎ๐ง๐ since {!!})
  -- field triangle-โ : unit-l-โ โ-โ 


  -- field isIso:unit-l-โ : isIso _ _ unit-l-โ
                            -- {!(ฮฑ-๐๐๐ญ โ-๐๐๐ญ (โ- โงผ id-๐๐๐ญ , โ- โงผ id-๐๐๐ญ , id-๐๐๐ญ โงฝ-๐๐๐ญ โงฝ-๐๐๐ญ))!}


  -- unitแต-l-โ : โ(a : โจ ๐ โฉ) -> โจ [โ] โฉ (โจ [Id] โฉ (lift tt) , a) โถ a
  -- unitแต-l-โ = โจ unit-l-โ โฉ


  -- field unit-l-โ : โ(a) -> [โ]แต ([Id]แต (lift tt) , a) โถ a


