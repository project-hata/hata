
module Verification.Core.Category.Std.Functor.Equivalence.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Setoid.Morphism
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid


module _ {ð : Category ð} {ð : Category ð} where
  record isIso-ððð­ (F : Functor ð ð) : ð° (ð ï½¤ ð) where
    field inverse-â-ððð­ : Functor ð ð
    field inv-r-â-ððð­ : F â-ððð­ inverse-â-ððð­ â¼ id
    field inv-l-â-ððð­ : inverse-â-ððð­ â-ððð­ F â¼ id

  open isIso-ððð­ public

module _ (ð : Category ð) (ð : Category ð) where
  _â-ððð­_ = (Functor ð ð) :& isIso-ððð­

pattern _since_andAlso_ a b c = â²_â² a {makeâi {{b}}} {{c}}

module _ {ð : Category ð} {ð : Category ð} where
  sym-â-ððð­ : ð â-ððð­ ð -> ð â-ððð­ ð
  sym-â-ððð­ p = â¨ inverse-â-ððð­ (of p) â© since of inverse-â-ððð­ (of p) andAlso record
    { inverse-â-ððð­ = â¨ p â© since it
    ; inv-r-â-ððð­ = inv-l-â-ððð­ (of p)
    ; inv-l-â-ððð­ = inv-r-â-ððð­ (of p)
    }
