
module Verification.Core.Category.Std.Category.Opposite.LiftFunctor where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Opposite.Definition


module _ {๐ : Category ๐} {๐ : Category ๐} where
  liftFunctor-แตแตโฏ : (F : Functor ๐ ๐) -> Functor (๐ แตแตโฏ) (๐ แตแตโฏ)
  liftFunctor-แตแตโฏ F = G since P
    where
      G : (๐ แตแตโฏ) -> (๐ แตแตโฏ)
      G (incl a) = incl (โจ F โฉ a)

      map-G : โ{a b : ๐ แตแตโฏ} -> (f : a โถ b) -> G a โถ G b
      map-G (incl f) = incl (map f)

      P : isFunctor _ _ G
      isFunctor.map P = map-G
      isFunctor.isSetoidHom:map P = {!!}
      isFunctor.functoriality-id P = {!!}
      isFunctor.functoriality-โ P = {!!}



