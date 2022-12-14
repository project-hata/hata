
module Verification.Core.Data.List.Variant.Binary.Element.Instance.Functor where

open import Verification.Core.Conventions hiding (β)


open import Verification.Core.Set.Decidable
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Functor
open import Verification.Core.Data.List.Variant.Binary.Element.Definition


module _ {A : π° π} {B : π° π} where
  map-β : (f : A -> B) -> {as : βList A} {a : A} -> as β a -> map-βList f as β f a
  map-β f incl = incl
  map-β f (right-β x) = right-β (map-β f x)
  map-β f (left-β x) = left-β (map-β f x)


