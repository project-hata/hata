
module Verification.Core.Data.List.Variant.Binary.Element.Properties where

open import Verification.Core.Conventions hiding (β)


open import Verification.Core.Set.Decidable
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Free
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Set.Contradiction
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition


module _ {A : π° π} where

  module _ {a b : βList A} {x : A} where

    instance
      isInjective-π°:left-β : isInjective-π° (left-β {a = a} {b} {x})
      isInjective-π°.cancel-injective-π° (isInjective-π°:left-β) {m1} {m2} p = Ξ» i -> f (p i) m1
        where f : (p : a β b β x) -> a β x -> a β x
              f (left-β p) def = p
              f (right-β p) def = def

      isInjective-π°:right-β : isInjective-π° (right-β {a = a} {b} {x})
      isInjective-π°:right-β = injective (Ξ» {m1} {m2} p i β f (p i) m1)
        where f : (p : a β b β x) -> b β x -> b β x
              f (left-β p) def = def
              f (right-β p) def = p

  instance
    isContradiction:left-ββ‘right-β : β {a b : βList A} {x : A} {p : a β x} -> {q : b β x} -> isContradiction (left-β p β‘ right-β q)
    isContradiction:left-ββ‘right-β {a} {b} {x} {p} {q} = contradiction (Ξ» r β transport (cong P r) tt)
      where P : (a β b β x) -> π°β
            P (left-β a) = β€-π°
            P (right-β a) = β₯-π°

    isContradiction:right-ββ‘left-β : β {a b : βList A} {x : A} {p : a β x} -> {q : b β x} -> isContradiction (right-β p β‘ left-β q)
    isContradiction:right-ββ‘left-β = contradiction (Ξ» x β contradict (Ξ» i -> (x (~ i))))

  -- the element relation is discrete
  instance
    isDiscrete:β : β{as : βList A} {a : A} -> isDiscrete (as β a)
    isDiscrete._β-Str_ (isDiscrete:β {as} {a}) = h
      where
        -- TODO prove this part with the additional fact that A is a set (needs to be added).
        g : β{a b} -> (p : a β‘ b) -> (x : incl b β a) -> PathP (Ξ» i -> incl (p i) β a) incl x
        g p incl = {!!}

        f : β{as a} -> (x y : as β a) -> Decision (x β‘ y)
        f incl y = yes (g refl-β‘ y)
        f (right-β x) (right-β y) with f x y
        ... | yes p = yes (cong right-β p)
        ... | no Β¬p = no (Ξ» q -> Β¬p (cancel-injective-π° q))
        f (right-β x) (left-β y) = no impossible
        f (left-β x) (right-β y) = no impossible
        f (left-β x) (left-β y) with f x y
        ... | yes p = yes (cong left-β p)
        ... | no Β¬p = no (Ξ» q -> Β¬p (cancel-injective-π° q))

        h : β{as a} -> (x y : as β a) -> Decision (x β£ y)
        h x y with f x y
        ... | yes p = yes (β‘ββ‘-Str p)
        ... | no Β¬p = no (Ξ» q -> Β¬p (β‘-Strββ‘ q))
