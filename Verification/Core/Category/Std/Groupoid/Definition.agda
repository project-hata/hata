
module Verification.Core.Category.Std.Groupoid.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso

record isGroupoid (๐ : Category ๐) : ๐ฐ ๐ where
  field isIso:hom : โ{a b : โจ ๐ โฉ} -> (ฯ : a โถ b) -> isIso (hom ฯ)

open isGroupoid {{...}} public

module _ {๐ : Category ๐} {{X : isGroupoid ๐}} where
  _โปยน-๐๐ซ๐ฉ๐ : โ{a b : โจ ๐ โฉ} -> a โถ b -> b โถ a
  _โปยน-๐๐ซ๐ฉ๐ ฯ = (inverse-โ (isIso:hom ฯ) )

module _ ๐ where
  Groupoid = Category ๐ :& isGroupoid



