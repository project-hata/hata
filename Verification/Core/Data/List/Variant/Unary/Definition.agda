
module Verification.Core.Data.List.Variant.Unary.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete



--------------------------------------------------------------------
-- [Definition]
-- (NOTE: Lists are actually defined in Agda.Builtin.List,
--        we merely reproduce the definition here for introduction
--        purposes.)
--
private
  -- | For any type |A|, lists with elements of type |A| are defined
  --   as the data type [..] with two constructors.
  data List' (A : π° π) : π° π where

  -- | - The constructor [..], which denotes the empty list.
    []  : List' A

  -- | - The constructor [..], which denotes the operation
  --     of prepending an element |a| to a list |as|,
  --     resulting in the larger list |a β· as|.
    _β·_ : A -> List' A β List' A

-- #Notation/Rewrite# List' = List
-- //



--------------------------------------------------------------------
-- [Hide]
-- Some proofs which should be moved somewhere else.
module _ {A : π° π} where
  module _ {{_ : isDiscrete A}} where
    private
      lem-1 : (a b : List A) β Decision (a β‘-Str b)
      lem-1 [] [] = yes refl-β£
      lem-1 [] (x β· b) = no Ξ» ()
      lem-1 (x β· a) [] = no Ξ» ()
      lem-1 (x β· a) (y β· b) with x β-Str y | lem-1 a b
      ... | yes p | yes q = yes (congβ-Str _β·_ p q)
      ... | yes p | no Β¬p = no Ξ» {refl-β£ β Β¬p refl-β£}
      ... | no Β¬p | Y = no Ξ» {refl-β£ β Β¬p refl-β£}

    instance
      isDiscrete:List : isDiscrete (List A)
      isDiscrete:List = record { _β-Str_ = lem-1 }

  instance
    isSet-Str:List : {{_ : isSet-Str A}} -> isSet-Str (List A)
    isSet-Str:List = {!!}


module _ {A : π° π} where
  instance
    isSetoid:List : isSetoid (List A)
    isSetoid:List = isSetoid:byId
-- //

--------------------------------------------------------------------
-- [Hide]
-- | We provide patterns for using lists with a few elements

pattern β¦β¦ = []
-- pattern β¦_β¦ a = a β· []
pattern β¦_Ψ_β¦ a b = a β· b β· []
pattern β¦_Ψ_Ψ_β¦ a b c = a β· b β· c β· []
pattern β¦_Ψ_Ψ_Ψ_β¦ a b c d = a β· b β· c β· d β· []
pattern β¦_Ψ_Ψ_Ψ_Ψ_β¦ a b c d e = a β· b β· c β· d β· e β· []

-- //
