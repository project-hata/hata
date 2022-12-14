
module Verification.Core.Setoid.Power.Instance.IsDistributive where

open import Verification.Core.Conventions hiding (_ā_)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Setoid.Codiscrete
open import Verification.Core.Setoid.Power.Definition

open import Verification.Core.Setoid.Power.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Definition
open import Verification.Core.Setoid.Power.Union
open import Verification.Core.Setoid.Power.Intersection

open import Verification.Core.Setoid.Power.Instance.HasCoproducts
open import Verification.Core.Setoid.Power.Instance.HasProducts


module _ {A : šš­š š} where
  lem1 : ā{U V W : š« A} -> U ā (V ā W) ā (U ā V ā U ā W)
  lem1 {U} {V} {W} = f since P
    where
      f : U ā (V ā W) ā¶ (U ā V ā U ā W)
      f = incl (Ī» (xāU , xāVāW) ā case xāVāW of
                                       (Ī» xāV -> left (xāU , xāV))
                                       (Ī» xāW -> right (xāU , xāW)))

      g : (U ā V ā U ā W) ā¶ U ā (V ā W)
      g = incl (Ī» x ā case x of
                           (Ī» (xāU , xāV) -> xāU , left xāV)
                           (Ī» (xāU , xāW) -> xāU , right xāW)
        )

      P : isIso (hom f)
      P = record
        { inverse-ā = g
        ; inv-r-ā = tt
        ; inv-l-ā = tt
        }

  lem2 : ā{U V W : š« A} -> U ā (V ā W) ā (U ā V) ā (U ā W)
  lem2 {U} {V} {W} = f since P
    where
      f : U ā (V ā W) ā¶ (U ā V) ā (U ā W)
      f = incl (Ī» x ā case x of
                           (Ī» xāU -> left xāU , left xāU)
                           (Ī» (xāV , xāW) -> right xāV , right xāW))

      g : (U ā V) ā (U ā W) ā¶ U ā (V ā W)
      g = incl (Ī» (xāUāV , xāUāW) ā case xāUāV of
                                         (Ī» xāU -> left xāU)
                                         (Ī» xāV -> case xāUāW of
                                                          (Ī» xāU -> left xāU)
                                                          (Ī» xāW -> right (xāV , xāW))))

      P : isIso (hom f)
      P = record
          { inverse-ā = g
          ; inv-r-ā = tt
          ; inv-l-ā = tt
          }

  module _ {I : š°ā} {U : š« A} {V : I -> š« A} where
    lem3 : U ā (āØįµ¢ V) ā āØ[ i ] (U ā V i)
    lem3 = f since P
      where
        f : U ā (āØįµ¢ V) ā¶ āØ[ i ] (U ā V i)
        āØ f ā© (xāU , (i , xāVįµ¢)) = i , xāU , xāVįµ¢

        g : āØ[ i ] (U ā V i) ā¶ U ā (āØįµ¢ V)
        āØ g ā© (i , xāU , xāVįµ¢) = xāU , (i , xāVįµ¢)

        P : isIso (hom f)
        P = record
          { inverse-ā = g
          ; inv-r-ā = tt
          ; inv-l-ā = tt
          }

    --
    -- Constructively we cannot prove the following.
    -- This means that š« A is completely distributive only in
    -- one direction, not in both.
    --
    -- lem4 : (U ā (āØįµ¢ V) ā āØ[ i ] (U ā V i))
    --


