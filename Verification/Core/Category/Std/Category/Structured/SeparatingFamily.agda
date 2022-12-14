
module Verification.Core.Category.Std.Category.Structured.SeparatingFamily where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition


module _ (π : Category π) where

  record isSeparatingFamily {π : π} {I : π° π} (F : I -> β¨ π β©) : π° (π ο½€ π) where
    field separate : β{a b : β¨ π β©} -> (Ο Ο : a βΆ b) -> (β {i : I} -> β (ΞΎ : F i βΆ a) -> ΞΎ β Ο βΌ ΞΎ β Ο) -> Ο βΌ Ο

  open isSeparatingFamily {{...}} public

record hasSeparatingFamily (π : π) (π : Category π) : π° (π ο½€ π βΊ) where
  field {Separator} : π° π
  field separator : Separator -> β¨ π β©
  field {{isSeparatingFamily:seperators}} : isSeparatingFamily π separator

open hasSeparatingFamily {{...}} public





