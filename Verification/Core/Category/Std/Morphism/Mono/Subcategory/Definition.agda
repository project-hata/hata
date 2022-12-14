
module Verification.Core.Category.Std.Morphism.Mono.Subcategory.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.Mono.Definition
open import Verification.Core.Category.Std.Morphism.Iso


module _ (๐ : Category ๐) where
  record Subโโโโ : ๐ฐ (๐ โ 0) where
    constructor incl
    field โจ_โฉ : โจ ๐ โฉ

  open Subโโโโ public

  macro ๐๐ฎ๐โโโโ = #structureOn Subโโโโ

module _ {๐ : Category ๐} where
  private
    subโโโโ : SubcategoryData ๐ (Subโโโโ ๐)
    subโโโโ = subcatdata โจ_โฉ isMono

    lem-1 : โ{a : โจ ๐ โฉ} -> isMono (id {a = a})
    lem-1 = mono (ฮป p โ unit-r-โ โปยน โ p โ unit-r-โ)

    lem-2 : โ{a b c : โจ ๐ โฉ} -> {f : a โถ b} -> {g : b โถ c}
            -> isMono f -> isMono g -> isMono (f โ g)
    lem-2 {a} {b} {c} {f} {g} fp gp = mono P
      where
        P : โ{x : โจ ๐ โฉ} {ฮฑ ฮฒ : x โถ a} -> (ฮฑ โ (f โ g)) โผ (ฮฒ โ (f โ g)) -> ฮฑ โผ ฮฒ
        P {ฮฑ = ฮฑ} {ฮฒ} p =
          let q : (ฮฑ โ f) โ g โผ (ฮฒ โ f) โ g
              q = assoc-l-โ โ p โ assoc-r-โ
              Q : ฮฑ โ f โผ ฮฒ โ f
              Q = cancel-mono {{_}} {{gp}} q
          in cancel-mono {{_}} {{fp}} Q

  instance
    isSubcategory:subโโโโ : isSubcategory (subโโโโ)
    isSubcategory:subโโโโ =
      record
      { closed-โ  = lem-2
      ; closed-id = lem-1
      }

  instance
    isCategory:Subโโโโ : isCategory (๐๐ฎ๐โโโโ ๐)
    isCategory:Subโโโโ = isCategory:bySubcategory

  instance
    isSetoid:๐๐ฎ๐โโโโ : isSetoid (๐๐ฎ๐โโโโ ๐)
    isSetoid:๐๐ฎ๐โโโโ = isSetoid:byCategory


