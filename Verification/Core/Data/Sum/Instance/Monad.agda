
module Verification.Core.Data.Sum.Instance.Monad where

open import Verification.Conventions
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.Monoidal
open import Verification.Core.Data.Sum.Instance.Functor



module _ {A : π° π} where
  instance
    isMonad:+β§Ώ : isMonad {π = ππ²π©π π} (A +β§Ώ)
    isMonad:+β§Ώ = monad pure-+ join-+ {{{!!}}} {{{!!}}} {!!} {!!} {!!}

      where
        pure-+ : β(B : π° π) -> (B βΆ A + B)
        pure-+ _ = right

        join-+ : β(B : π° π) -> (A +-π° (A + B)) βΆ (A + B)
        join-+ _ = (either left idf)

instance
  isLaxMonoidalFunctor:Maybe : isLaxMonoidalFunctor {π = ππ§π’π― π} {π = ππ§π’π― π} (β€-π° {π} +β§Ώ)
  isLaxMonoidalFunctor.lax-unit isLaxMonoidalFunctor:Maybe = right
  isLaxMonoidalFunctor.lax-mult isLaxMonoidalFunctor:Maybe = Ξ» (a , b) -> do a' <- a
                                                                             b' <- b
                                                                             return (a' , b')
  -- isLaxMonoidalFunctor.lax-unit-l isLaxMonoidalFunctor:Maybe i (fstβ , left x) = left x
  -- isLaxMonoidalFunctor.lax-unit-l isLaxMonoidalFunctor:Maybe i (fstβ , just x) = just x

instance
  isMonoidalMonad:Maybe : isMonoidalMonad {π = ππ§π’π― π} (β€-π° {π} +β§Ώ)
  isMonoidalMonad.isLaxMonoidalFunctor:this isMonoidalMonad:Maybe = isLaxMonoidalFunctor:Maybe
  isMonoidalMonad.compat-lax-unit isMonoidalMonad:Maybe = refl-β‘
  -- isMonoidalMonad.compat-lax-mult isMonoidalMonad:Maybe = refl-β‘



