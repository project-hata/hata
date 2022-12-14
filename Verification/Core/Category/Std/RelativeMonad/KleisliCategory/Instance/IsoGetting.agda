
module Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting where

open import Verification.Conventions hiding (_โ_)

open import Verification.Core.Setoid
open import Verification.Core.Setoid.Morphism
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Functor.EssentiallySurjective

record hasIsoGetting (๐ : Category ๐) : ๐ฐ ๐ where
  field getIso : โ(a b : โจ ๐ โฉ) -> Maybe (a โ b)

open hasIsoGetting {{...}} public


module _ {๐ : Category ๐} {๐ : Category ๐} {F : Functor ๐ ๐} {{_ : isFull F}} {{_ : isFaithful F}}  {{_ : isEssentiallySurjective F}} where

  hasIsoGetting:byFFEso : hasIsoGetting ๐ -> hasIsoGetting ๐
  hasIsoGetting:byFFEso P = record { getIso = lem-1 }
    where
      instance _ = P

      lem-1 : (a b : โจ ๐ โฉ) โ Maybe (a โ b)
      lem-1 a b with getIso (โจ F โฉ a) (โจ F โฉ b)
      ... | left x = nothing
      ... | just ฯ = right (ฯ since Q)
        where
          -- a' = eso (โจ F โฉ a)
          -- b' = eso (โจ F โฉ b)
          ฯ : a โถ b
          ฯ = surj โจ ฯ โฉ

          ฯโปยน : b โถ a
          ฯโปยน = surj (inverse-โ (of ฯ))

          Q = record { inverse-โ = ฯโปยน ; inv-r-โ = {!!} ; inv-l-โ = {!!} }




module _ {๐ : Category ๐} {{_ : hasFiniteCoproducts ๐}} {๐ : Category ๐} where
  module _ {J : Functor ๐ ๐} {T : RelativeMonad J}  where

    hasIsoGetting:RelativeKleisli : {{_ : hasIsoGetting ๐}} -> hasIsoGetting (๐๐๐๐ฅ๐ฌ T)
    hasIsoGetting:RelativeKleisli = record { getIso = lem-1 }
      where
        lem-1 : (a b : RelativeKleisli T) โ Maybe (a โ b)
        lem-1 a b with getIso โจ a โฉ โจ b โฉ
        ... | nothing = nothing
        ... | just ฯ = right (ฯ since P)
          where
            ฯ : a โถ b
            ฯ = incl (map โจ ฯ โฉ โ repure)

            ฯโปยน : b โถ a
            ฯโปยน = incl (map (inverse-โ (of ฯ)) โ repure)

            P = record { inverse-โ = ฯโปยน ; inv-r-โ = {!!} ; inv-l-โ = {!!} }






