
module Verification.Core.Data.Indexed.Xiix where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Adjoint

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

module _ {ð' : ð° ð} {{_ : isCategory {ð} ð'}} {I : ð° ð} where

  private
    ð : Category _
    ð = â² ð' â²

  ix' : I -> ðð± I ð -> â¨ ð â©
  ix' i a = ix a i

  macro
    ðð¥ : â(i : I) -> SomeStructure
    ðð¥ i = #structureOn (ix' i)

  map-ðð¥ : â i -> â{a b : ðð± I ð} -> (Ï : a â¶ b) -> ix a i â¶ ix b i
  map-ðð¥ i Ï = Ï i

  module _ {i : I} where
    instance
      isFunctor:ðð¥ : isFunctor (ðð± I ð) ð (ðð¥ i)
      isFunctor.map isFunctor:ðð¥               = map-ðð¥ _ -- Î» x â x i
      isFunctor.isSetoidHom:map isFunctor:ðð¥   = record { cong-â¼ = Î» x â x i }
      isFunctor.functoriality-id isFunctor:ðð¥  = refl
      isFunctor.functoriality-â isFunctor:ðð¥   = refl


module _ {ð' : ð° ð} {{_ : isCategory {ð} ð'}} {I : ð° ð} {{_ : hasInitial â² ð' â²}} {{_ : isDiscrete I}} where
-- module _ {ð : Category ð} {I : ð° ð} {{_ : hasInitial ð}} {{_ : isDiscrete I}} where
  private
    ð : Category _
    ð = â² ð' â²

  xiâ : (i : I) -> â¨ ð â© -> ðð± I ð
  xiâ i a = indexed f
    where
      f : I -> â¨ ð â©
      f j with (i â-Str j)
      ... | yes p = a
      ... | no Â¬p = â¥

  macro
    ð¥ðâ : â(i : I) -> SomeStructure
    ð¥ðâ i = #structureOn (xiâ i)

  module _ {i : I} where
    map-ð¥ðâ : â{a b : â¨ ð â©} -> (f : a â¶ b) -> ð¥ðâ i a â¶ ð¥ðâ i b
    map-ð¥ðâ f j with i â-Str j
    ... | yes p = f
    ... | no Â¬p = id

    instance
      isFunctor:ð¥ðâ : isFunctor ð (ðð± I ð) (ð¥ðâ i)
      isFunctor.map              isFunctor:ð¥ðâ = map-ð¥ðâ
      isFunctor.isSetoidHom:map  isFunctor:ð¥ðâ = {!!}
      isFunctor.functoriality-id isFunctor:ð¥ðâ = {!!}
      isFunctor.functoriality-â  isFunctor:ð¥ðâ = {!!}

    private
      coadj-ð¥ðâ' : â{a : â¨ ð â©} {j} -> j â£ i -> a â¶ ðð¥ i (ð¥ðâ j a)
      coadj-ð¥ðâ' {a} {j} p with j â-Str i
      ... | yes pâ = id
      ... | no Â¬p = impossible (Â¬p p)

    coadj-ð¥ðâ : â(a : â¨ ð â©) -> a â¶ ðð¥ i (ð¥ðâ i a)
    coadj-ð¥ðâ _ = coadj-ð¥ðâ' refl-â£

    adj-ð¥ðâ : â(a : ðð± I ð) -> ð¥ðâ i (ðð¥ i a) â¶ a
    adj-ð¥ðâ a j with i â-Str j
    ... | yes refl-â£ = id
    ... | no Â¬p = elim-â¥

    instance
      isAdjoint:ð¥ðâðð¥ : isAdjoint (ð¥ðâ i) (ðð¥ i)
      isAdjoint.adj              isAdjoint:ð¥ðâðð¥ = adj-ð¥ðâ
      isAdjoint.coadj            isAdjoint:ð¥ðâðð¥ = coadj-ð¥ðâ
      isAdjoint.isNatural:adj    isAdjoint:ð¥ðâðð¥ = {!!}
      isAdjoint.isNatural:coadj  isAdjoint:ð¥ðâðð¥ = {!!}
      isAdjoint.reduce-coadj     isAdjoint:ð¥ðâðð¥ = {!!}
      isAdjoint.reduce-adj       isAdjoint:ð¥ðâðð¥ = {!!}
      -- record
      --                   { adj    = adj-ð¥ðâ
      --                   ; coadj  = coadj-ð¥ðâ
      --                   }



