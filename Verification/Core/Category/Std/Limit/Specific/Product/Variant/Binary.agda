
module Verification.Core.Category.Std.Limit.Specific.Product.Variant.Binary where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition


module _ {๐ : ๐ฐ ๐} {{_ : isCategory {๐} ๐}} where
  record isTerminal (x : ๐) : ๐ฐ (๐ ๏ฝค ๐) where
    field intro-โค : โ{a} -> a โถ x
    field expand-โค : โ{a} -> {f : a โถ x} -> f โผ intro-โค

  open isTerminal {{...}} public

  record isProduct (a b x : ๐) : ๐ฐ (๐ ๏ฝค ๐) where
    field ฯโ : x โถ a
    field ฯโ : x โถ b
    field โงผ_โงฝ : โ{c} -> ((c โถ a) ร-๐ฐ (c โถ b)) -> c โถ x
    field {{isSetoidHom:โงผโงฝ}} : โ{c} -> isSetoidHom โฒ((c โถแต a) ร-๐ฐ (c โถแต b))โฒ (c โถ x) (โงผ_โงฝ {c})
    field reduce-ฯโ : โ{c} {f : c โถ a} {g : c โถ b} -> โงผ f , g โงฝ โ ฯโ โผ f
    field reduce-ฯโ : โ{c} {f : c โถ a} {g : c โถ b} -> โงผ f , g โงฝ โ ฯโ โผ g
    field expand-ฯโ,ฯโ  : โ{c} {f : c โถ x} -> f โผ โงผ f โ ฯโ , f โ ฯโ โงฝ

  open isProduct {{...}} public


record hasTerminal (๐ : Category ๐) : ๐ฐ ๐ where
  field โค : โจ ๐ โฉ
  field {{isTerminal:โค}} : isTerminal โค

open hasTerminal {{...}} public

record hasProducts (๐ : Category ๐) : ๐ฐ ๐ where
  infixl 100 _โ_
  field _โ_ : โจ ๐ โฉ -> โจ ๐ โฉ -> โจ ๐ โฉ
  field {{isProduct:โ}} : โ{a b} -> isProduct a b (a โ b)
open hasProducts {{...}} public

record hasFiniteProducts (๐ : Category ๐) : ๐ฐ ๐ where
  field {{hasTerminal:this}} : hasTerminal ๐
  field {{hasProducts:this}}    : hasProducts ๐

open hasFiniteProducts {{...}} public

module _ {๐ : Category ๐} {{_ : hasProducts ๐}} {{_ : hasTerminal ๐}} where
  hasFiniteProducts:default : hasFiniteProducts ๐
  hasFiniteProducts.hasTerminal:this hasFiniteProducts:default  = it
  hasFiniteProducts.hasProducts:this hasFiniteProducts:default     = it





module _ {๐ : Category ๐} {{_ : hasFiniteProducts ๐}} where
  macro
    โโจ : SomeStructure
    โโจ = #structureOn (ฮปโ _โ_)


module _ {๐แต : ๐ฐ ๐} {{_ : isCategory {๐} ๐แต}} {{_ : hasProducts โฒ ๐แต โฒ }} where

  private macro ๐ = #structureOn ๐แต
  private instance _ = isSetoidHom:โงผโงฝ

  โงผโ_โโงฝ : โ{a b c : ๐} {fโ fโ : c โถ a} {gโ gโ : c โถ b} -> (fโ โผ fโ) ร (gโ โผ gโ) -> โงผ fโ , gโ โงฝ โผ โงผ fโ , gโ โงฝ
  โงผโ_โโงฝ = cong-โผ



