
module Verification.Core.Data.List.Variant.Unary.Instance.Traversable where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Data.List.Variant.Unary.Instance.Functor
open import Verification.Core.Data.List.Variant.Unary.Instance.Monoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category

open import Verification.Core.Category.Std.Monad.Definition

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Monad.TypeMonadNotation

-- instance
--   isFunctor:List : isFunctor (ππ§π’π― π) (ππ§π’π― π) List
--   isFunctor.map isFunctor:List = map-List
--   isFunctor.isSetoidHom:map isFunctor:List = {!!}
--   isFunctor.functoriality-id isFunctor:List = {!!}
--   isFunctor.functoriality-β isFunctor:List = {!!}

instance
  isTraversable:List : isTraversable β²(List {π})β²
  isTraversable:List {π} = traversable (Ξ» {M} {{MM}} {A} xs -> f {M} {MM} {A} xs)
    where
      module _ {M : π°' π β π°' π} { MM : Monad β² π°' π β² on M } where
          f : {A : π°' π} β List (M A) β M (List A)
          f [] = return []
          f (x β· xs) = do
            x <- x
            xs <- f xs
            return (x β· xs)

module _ {A : π° π} where
  join-List : List (List A) -> List A
  join-List [] = []
  join-List (xs β· xss) = xs β join-List xss

  pure-List : A -> List A
  pure-List a = a β· []


{-
module _ {A : π° π} where
  ListβVec : List A -> β Vec A
  ListβVec [] = zero , []
  ListβVec (x β· xs) = _ , x β· ListβVec xs .snd

  VecβList : Vec A n -> List A
  VecβList β¦β¦ = []
  VecβList (x β· xs) = x β· VecβList xs

-}

