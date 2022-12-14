
module Verification.Core.Category.Std.Category.Opposite.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition



record _α΅α΅β―α΅ (A : π° π) : π° π where
  constructor incl
  field β¨_β© : A

open _α΅α΅β―α΅ public

macro
  _α΅α΅β― : β{π : π} {π : π ^ 2} -> (π°' π) [ π ]β SomeStructure
  _α΅α΅β― = Ξ»str A β¦ #structureOn (A α΅α΅β―α΅)


module _ {π : π° π} {{πP : isCategory {π} π}} where
  record Hom-α΅α΅β― (a b : π α΅α΅β―α΅) : π° (π β 0) where
    constructor incl
    field β¨_β© : β¨ b β© βΆ β¨ a β©

  open Hom-α΅α΅β― public

  module _ {a b : π α΅α΅β―α΅} where
    -- _βΌ-Hom-α΅α΅β―_ : (f g : Hom-α΅α΅β― a b) -> π° _
    -- _βΌ-Hom-α΅α΅β―_ f g = β¨ f β© βΌ β¨ g β©

    record _βΌ-Hom-α΅α΅β―_ (f g : Hom-α΅α΅β― a b) : π° (π β 1) where
      field β¨_β© : β¨ f β© βΌ β¨ g β©

    -- instance
    isSetoid:Hom-α΅α΅β― : isSetoid (Hom-α΅α΅β― a b)
    isSetoid:Hom-α΅α΅β― = isSetoid:byDef _βΌ-Hom-α΅α΅β―_ {!!} {!!} {!!}

  id-α΅α΅β― : β{a : π α΅α΅β―α΅} -> Hom-α΅α΅β― a a
  id-α΅α΅β― = {!!}

  instance
    isCategory:α΅α΅β― : isCategory (π α΅α΅β―)
    isCategory.Hom isCategory:α΅α΅β― = Hom-α΅α΅β―
    -- Ξ» a b -> Hom β¨ b β© β¨ a β©
    isCategory.isSetoid:Hom isCategory:α΅α΅β― = isSetoid:Hom-α΅α΅β―
    isCategory.id isCategory:α΅α΅β― = id-α΅α΅β―
    isCategory._β_ isCategory:α΅α΅β― = Ξ» f g -> incl (β¨ g β© β β¨ f β©)
    isCategory.unit-l-β isCategory:α΅α΅β―  = {!!} -- unit-r-β
    isCategory.unit-r-β isCategory:α΅α΅β―  = {!!} -- unit-l-β
    isCategory.unit-2-β isCategory:α΅α΅β―  = {!!} -- unit-2-β {{πP}}
    isCategory.assoc-l-β isCategory:α΅α΅β― = {!!} -- assoc-r-β
    isCategory.assoc-r-β isCategory:α΅α΅β― = {!!} -- assoc-l-β
    isCategory._β_ isCategory:α΅α΅β― = {!!}
{-
-}


-- -- [Definition]
-- _α΅α΅ : Category π -> Category π
-- _α΅α΅ π = β² β¨ π β© β² {{Op}}
--   where Op : isCategory β¨ π β©
--         isCategory.Hom Op a b = Hom b a
--         isCategory.isSetoid:Hom Op = isSetoid:Hom {{of π}}
--         isCategory.id Op = id
--         isCategory._β_ Op f g = g β f
--         isCategory.unit-l-β Op = unit-r-β
--         isCategory.unit-r-β Op    = unit-l-β       -- incl β¨ unit-l-β β©
--         isCategory.unit-2-β Op    = unit-2-β       -- incl β¨ unit-2-β β©
--         isCategory.assoc-l-β Op   = assoc-r-β      -- incl β¨ assoc-r-β β©
--         isCategory.assoc-r-β Op   = assoc-l-β      -- incl β¨ assoc-l-β β©
--         isCategory._β_ Op (p) (q) = q β p -- incl β¨ incl q β incl p β©

-- module _ {π : Category π} where
--   α΅α΅α΅α΅ : (π α΅α΅ α΅α΅) β‘-Str π
--   α΅α΅α΅α΅ = refl-β£
