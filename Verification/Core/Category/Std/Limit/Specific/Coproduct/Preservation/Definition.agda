
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition where

open import Verification.Conventions hiding (_โ_)
open import Verification.Core.Setoid
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Notation.Associativity

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition


-- module _ {๐ : ๐ฐ ๐} {{_ : isCategory {๐} ๐}} {๐ : ๐ฐ ๐} {{_ : isCategory {๐} ๐}} where


module _ {๐ : Category ๐} {๐ : Category ๐} where
  record preservesCoproduct (F : Functor ๐ ๐) (a b x : โจ ๐ โฉ) {{_ : isCoproduct a b x}} : ๐ฐ (๐ ๏ฝค ๐) where
    field {{preserve-isCoproduct}} : isCoproduct (โจ F โฉ a) (โจ F โฉ b) (โจ F โฉ x)
    field preserve-ฮนโ : map {{of F}} ฮนโ โผ ฮนโ
    field preserve-ฮนโ : map {{of F}} ฮนโ โผ ฮนโ

  open preservesCoproduct {{...}} public

  record preservesInitial (F : Functor ๐ ๐) (a : โจ ๐ โฉ) {{_ : isInitial a}} : ๐ฐ (๐ ๏ฝค ๐) where
    field {{preserve-Initial}} : isInitial (โจ F โฉ a)

  open preservesInitial {{...}} public

  module _ {{_ : hasFiniteCoproducts ๐}} where
    record isFiniteCoproductPreserving (F : Functor ๐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
      field {{preservesCoproducts:this}} : โ{a b : โจ ๐ โฉ} -> preservesCoproduct F a b (a โ b)
      field {{preservesInitial:this}} : preservesInitial F โฅ

    open isFiniteCoproductPreserving {{...}} public


    module _ {F : Functor ๐ ๐} {{_ : isFiniteCoproductPreserving F}} {{_ : hasFiniteCoproducts ๐}} where
      preserves-โ : โ{a b : โจ ๐ โฉ} -> โจ F โฉ (a โ b) โ โจ F โฉ a โ โจ F โฉ b
      preserves-โ {a} {b} = โ:byIsCoproduct
        where
          instance
            _ : isCoproduct (โจ F โฉ a) (โจ F โฉ b) (โจ F โฉ (a โ b))
            _ = preserve-isCoproduct

      preserves-โฅ : โจ F โฉ โฅ โ โฅ
      preserves-โฅ = โ:byIsInitial





