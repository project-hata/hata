
module Verification.Core.Data.List.Variant.Binary.Element.Definition where

open import Verification.Core.Conventions hiding (β)


open import Verification.Core.Set.Decidable
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid

-- the element relation

-- [Definition]
-- | Let [..] be a type.
module _ {A : π° π} where

  -- |> The element relation [..] is defined similar to
  --    the definition for unary lists.
  data _β_ : βList A -> A -> π° π where
    incl : β {x} -> incl x β x
    right-β : β {a b x} -> b β x -> (a β b) β x
    left-β : β {a b x} -> a β x -> (a β b) β x

-- //




