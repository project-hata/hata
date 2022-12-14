
module Verification.Core.Data.FiniteIndexed.Property.IsoGetting where

open import Verification.Core.Conventions hiding (_โ_)

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Set.Definition

open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.Universe.Instance.Category

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed
open import Verification.Core.Data.List.VariantTranslation.Definition



module _ {A : ๐ฐ ๐} {{_ : isDiscrete A}} where
  instance
    hasIsoGetting:๐๐ข๐ง๐๐ฑ : hasIsoGetting (๐๐ข๐ง๐๐ฑ A)
    hasIsoGetting:๐๐ข๐ง๐๐ฑ = record { getIso = lem-1 }
      where
        lem-1 : (a b : FiniteIndexed A) โ Maybe (a โ b)
        lem-1 a b with โฎ โจ a โฉ โ-Str โฎ โจ b โฉ
        ... | yes p = let q : โจ a โฉ โผ โจ b โฉ
                          q = injective-โฎ-โList {a = โจ a โฉ} {b = โจ b โฉ} (โก-Strโโก p)
                          r : ๐๐ โจ a โฉ โ ๐๐ โจ b โฉ
                          r = cong-โผ q
                      in right (incl โจ r โฉ since record { inverse-โ = incl (inverse-โ (of r)) ; inv-r-โ = {!!} ; inv-l-โ = {!!} })
        ... | no ยฌp = nothing




