
module Verification.Core.Category.Std.Monad.Opposite where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Monad.Definition



module _ {๐ : Category ๐} where
  OpFunctor : (Functor ๐ ๐) -> Functor (๐ แตแต) (๐ แตแต)
  OpFunctor F = โจ F โฉ since P
    where
      P : isFunctor (๐ แตแต) (๐ แตแต) โจ F โฉ
      isFunctor.map P = map
      isFunctor.isSetoidHom:map P = it
      isFunctor.functoriality-id P = functoriality-id
      isFunctor.functoriality-โ P = functoriality-โ

  -- note, this does not work. We do have that "F แตแต" is a comonad!
  OpMonad : โ{F : ๐ โถ ๐} -> {{_ : isMonad F}} -> isMonad (OpFunctor F)
  OpMonad = {!!}




