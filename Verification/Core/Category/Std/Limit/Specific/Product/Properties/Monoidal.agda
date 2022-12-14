
module Verification.Core.Category.Std.Limit.Specific.Product.Properties.Monoidal where

open import Verification.Conventions hiding (_β_)
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product.Definition



module _ {π' : Category π} {{_ : hasFiniteProducts π'}} where
  private
    macro π = #structureOn β¨ π' β©
    instance
      _ : isSetoid π
      _ = isSetoid:byCategory

  byExpand-Οβ,Οβ : β{a b c : π} -> {f g : c βΆ a β b}
                   -> f β Οβ βΌ g β Οβ
                   -> f β Οβ βΌ g β Οβ
                   -> f βΌ g
  byExpand-Οβ,Οβ {f = f} {g} pβ pβ =
    f                   β¨ expand-Οβ,Οβ β©-βΌ
    β§Ό f β Οβ , f β Οβ β§½ β¨ β§Όβ pβ , pβ ββ§½ β©-βΌ
    β§Ό g β Οβ , g β Οβ β§½ β¨ expand-Οβ,Οβ β»ΒΉ β©-βΌ
    g                   β

  open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.FiniteCoproduct
  open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal


  fromα΅α΅-β : β{a b : π} -> IsoOf (π α΅α΅) a b -> IsoOf π a b
  fromα΅α΅-β Ο = inverse-β {{isCategory:α΅α΅}} (of Ο) since
    record
      { inverse-β = β¨ Ο β©
      ; inv-r-β = inv-r-β {{isCategory:α΅α΅}} (of Ο)
      ; inv-l-β = inv-l-β {{isCategory:α΅α΅}} (of Ο)
      }

  assoc-l-β : β{a b c : π} -> (a β b) β c β a β (b β c)
  assoc-l-β {a} {b} {c} = fromα΅α΅-β (assoc-l-β {π' = β¨ π' β© since isCategory:α΅α΅ })

