
module Verification.Core.Category.Std.Bicategory.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Category.Std.Natural.Instance.Category

record isBicategory {π : π ^ 3} {π : π} (π : π° π) : π° (π ο½€ (π βΊ)) where
  field Cellβ : π -> π -> π° (π β 0)
  field {{isCategory:Cellβ}} : β{a b} -> isCategory {π β 1 β― 2} (Cellβ a b)

  Cell : π -> π -> Category π
  Cell a b = β² Cellβ a b β²


  field idβ : β{a} -> Cellβ a a
  field ββ¨β : β{a b c : π} -> Functor (Cell a b Γ-πππ­ Cell b c) (Cell a c)

  field unitβ-r-β : β{a b : π} -> β§Ό Const idβ , id-πππ­ β§½-πππ­ β-πππ­ ββ¨β βΌ idOn (Cell a b)
  field unitβ-l-β : β{a b : π} -> β§Ό Const idβ , id-πππ­ β§½-πππ­ β-πππ­ ββ¨β βΌ idOn (Cell a b)
  -- field assocβ-l-β : β{a b c d : π} -> 


  -- Cellβ : π -> π -> π° (π β 0)
  -- Cellβ a b = β¨ Cell a b β©



  -- field Cellβ : π -> π -> π° (π β 0)
  -- field {{isCategory:Cellβ}} : β{a b} -> isCategory {π β 1 β― 2} (Cellβ a b)

  -- field idβ : β{a} -> Cellβ a a
  -- field ββ¨βα΅ : β{a b c} -> (Cellβ a b Γ Cellβ b c) -> Cellβ a c

  -- field {{isFunctor:ββ¨β}} : β{a b c} -> isFunctor β²(Cellβ a b Γ-π° Cellβ b c)β² β² Cellβ a c β² ββ¨βα΅

  -- field unitβ-l-β : β{a} -> 




  -- Cellβ : β{a b} -> (f g : Cellβ a b) -> π° _
  -- Cellβ f g = f βΆ g

  -- field Cellβ : β{a b : π} -> (f g : Cellβ a b) -> π° (π β 1)












