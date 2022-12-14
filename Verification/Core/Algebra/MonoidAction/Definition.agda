
module Verification.Core.Algebra.MonoidAction.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Algebra.Monoid.Definition


record isActed {π π} (M : Monoid π) (A : Setoid π) : π° (π ο½€ π) where
  field _β·_ : β¨ M β© -> β¨ A β© -> β¨ A β©
        assoc-l-β· : β{m n a} -> (m β n) β· a βΌ m β· (n β· a)
        _ββ·β_ : β{a b} {m n} -> (a βΌ b) -> (m βΌ n) -> (a β· m) βΌ (b β· n)

  infixr 30 _β·_
open isActed {{...}} public

Acted : (M : Monoid π) -> β π -> _
Acted M π = _ :& isActed {π} M

module _ {M : Monoid π} where

  record isTransitiveActed (A : Acted M π) : π° (π ο½€ π) where
    field _β_ : β¨ A β© -> β¨ A β© -> β¨ M β©
    field trans-β· : β{a b} -> (b β a) β· a βΌ b

  record isFreeActed (A : Acted M π) : π° (π ο½€ π) where
    field free-β· : β{m : β¨ M β©} {a : β¨ A β©} -> m β· a βΌ a -> m βΌ β






module Old where
  module _ {M : π° _} {A : π° _} {{_ : Monoid π on M}} {{_ : Setoid π on A}} {{_ : isActed β² M β² β² A β²}} where
    -- _ββ·β'_ : β{a b : β¨ M β©} {m n : β¨ A β©} -> (a βΌ b) -> (m βΌ n) -> (a β· m) βΌ (b β· n)
    _ββ·β'_ : β{a b : M} {m n : A} -> (a βΌ b) -> (m βΌ n) -> (a β· m) βΌ (b β· n)
    _ββ·β'_ = {!!}


  record hasDistributiveActionβ (M : Monoid π) (A : Setoid π :& (isMonoid :, isActed M)) : π° (π ο½€ π) where
    private
      βA : β¨ A β©
      βA = β
    field absorb-r-β· : β{m : β¨ M β©} -> m β· βA βΌ βA
    field distr-l-β· : β{m : β¨ M β©} {a b : β¨ A β©} -> m β· (a β b) βΌ ((m β· a) β (m β· b))

  open hasDistributiveActionβ {{...}} public



