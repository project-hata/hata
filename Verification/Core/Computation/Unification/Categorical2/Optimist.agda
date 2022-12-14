
module Verification.Core.Computation.Unification.Categorical2.Optimist where

open import Verification.Conventions
open import Verification.Core.Setoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition
open import Verification.Core.Computation.Unification.Categorical2.Ideal
open import Verification.Core.Computation.Unification.Categorical2.ForwardAction
open import Verification.Core.Computation.Unification.Categorical2.SemilatticeStructure
open import Verification.Core.Computation.Unification.Categorical2.ZeroIdeal
open import Verification.Core.Computation.Unification.Categorical2.EpiPrincipal
open import Verification.Core.Computation.Unification.Categorical2.InverseAction


-- ===* Statement and proof of the lemma
-- | With this, the optimist's lemma can finally be stated and proved


-- [Hide]
module _ (๐ : ๐ฐ ๐)
  {{_ : isCategory {๐} ๐ }}
  {{_ : isSizedCategory โฒ ๐ โฒ}}
  {{_ : isZeroMorphismCategory โฒ ๐ โฒ}} where

  private variable a : ๐

-- //

-- [Lemma]
-- | Let [..] be two ideals at |a|.
  module _ {U V : Ideal a} where
    -- |> Assume that we have a proof [..].
    module _ (PU : isEpiPrincipal U) where
      private instance _ = PU
      -- |> Let the representing morphism of |U| be called |u|:
      u : a โถ repObjOf U
      u = repOf U

      -- |> and assume that we also have a proof [....]
      module _ (PV : isEpiPrincipal (u โปยนโท V)) where

      -- |> Then |isEpiPrincipal (V โง U)| is true.

-- //

-- [Proof]
        private instance _ = PV

        -- | Denote the representing morphism of |u โปยนโท V| by |v|.
        v : repObjOf U โถ repObjOf (u โปยนโท V)
        v = repOf (u โปยนโท V)

        -- |> Then the following chain of equations holds:
        lem-1 : (V โง U) โผ (u โ v) โท โค
        lem-1 =  V โง U                      โจ refl โโงโ principal-r โฉ-โผ
                  (V โง (u โท โค))              โจ inv-โท-r โปยน โฉ-โผ
                  (u โท (u โปยนโท V))            โจ refl โโทโ (principal-r)  โฉ-โผ
                  (u โท (v โท โค))              โจ assoc-l-โท โปยน โฉ-โผ
                  ((u โ v) โท โค)              โ

        -- |> Using |u โ v| as representing morphism, we conclude.
        Proof : isEpiPrincipal (V โง U)
        Proof = record
                  { repObj       = _
                  ; rep          = u โ v
                  ; principal-r  = lem-1
                  ; zeroOrEpi    = isZeroOrEpi:โ {๐' = โฒ ๐ โฒ} zeroOrEpi zeroOrEpi
                  ; isGoodRep    = isGood:โ isGoodRep isGoodRep
                  }

        -- |> We also need to use the fact that the property |isZeroOrEpi|
        --    is preserved by composition. Furthermore, the field |isGoodRep|
        --    needs to be set. This is part of the infrastructure for the induction.

-- //

{-
    module _  (PV : isEpiPrincipal (repOf U {{PU}} โปยนโท V)) where

    optimist : 
              -> isEpiPrincipal (V โง U)
    optimist {a} {U} {V} PU PV =
      let
          instance _ = PV


          V' = u โปยนโท V

          v : repObjOf U โถ repObjOf V'
          v = repOf V'

          Pโ : (V โง U) โผ (u โ v) โท โค
          Pโ = V โง U                                          โจ refl โโงโ principal-r โฉ-โผ
                (V โง (u โท โค))                                 โจ inv-โท-r โปยน โฉ-โผ
                (u โท ((u โปยนโท V)))                              โจ refl โโทโ (principal-r)  โฉ-โผ
                (u โท ((v โท โค)))                                โจ assoc-l-โท โปยน โฉ-โผ
                ((u โ v) โท โค)                                   โ

      in record
         { repObj = _
         ; rep = u โ v
         ; principal-r = Pโ
         ; isGoodRep = isGood:โ isGoodRep isGoodRep
         ; zeroOrEpi = isZeroOrEpi:โ {๐' = โฒ ๐ โฒ} zeroOrEpi zeroOrEpi
         }
-}

