
--
-- Hata/LSS: Language for self-referential state
--
module Verification.Research.HataLSS.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Category.Std.Category.Construction.Coproduct
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Category.StdMonoidal.Category.Definition


--
-- We define memory regions. A region consists of files at multiple memory locations,
-- which can be referenced inside the files.
--



record isLocationCategory (𝒟 : Monoidal 𝑖) : 𝒰 𝑖 where
  field Loc : ⟨ 𝒟 ⟩

module _ 𝑖 where
  LocationCategory = Monoidal 𝑖 :& isLocationCategory

module _ {𝒟 : LocationCategory 𝑖} where






