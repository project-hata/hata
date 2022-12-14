
module Verification.Core.Category.Std.Category.Opposite.Strict.Instance.Monoid where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Opposite.Strict


module _ {ð : Category ð} where
  -- private instance
  --   _ : isSetoid â¨ ð â©
  --   _ = isSetoid:byCategory

  -- module _ {{Mp : isMonoid (â¨ ð â© since isSetoid:byCategory)}} where
  --   instance
  --     isMonoid:áµáµ :  isMonoid (â¨ ð â© since isSetoid:byCategory {{of ð áµáµ}})
  --     isMonoid._â_ isMonoid:áµáµ = _â_ {{Mp}}
  --     isMonoid.â isMonoid:áµáµ = â {{Mp}}
  --     isMonoid.unit-l-â isMonoid:áµáµ = â¨ sym-â unit-l-â â© since {!!}
  --     isMonoid.unit-r-â isMonoid:áµáµ = {!!}
  --     isMonoid.assoc-l-â isMonoid:áµáµ = {!!}
  --     isMonoid._âââ_ isMonoid:áµáµ = {!!}

  âáµáµâ»Â¹ : â{a b : â¨ ð â©} -> (_â_ {{of ð áµáµ}} a b) -> (a â b)
  âáµáµâ»Â¹ f = inverse-â {{of ð áµáµ}} (of f) since
            record
            { inverse-â = â¨ f â©
            ; inv-r-â   = inv-r-â {{of ð áµáµ}} (of f)
            ; inv-l-â   = inv-l-â {{of ð áµáµ}} (of f)
            }


  module _ {{Mp : isMonoid (â¨ ð â© since isSetoid:byCategory {{of ð áµáµ}})}} where
    isMonoid:byáµáµ :  isMonoid (â¨ ð â© since isSetoid:byCategory {{of ð}})
    isMonoid._â_ isMonoid:byáµáµ        = _â_ {{Mp}}
    isMonoid.â isMonoid:byáµáµ          = â {{Mp}}
    isMonoid.unit-l-â isMonoid:byáµáµ   = âáµáµâ»Â¹ unit-l-â
    isMonoid.unit-r-â isMonoid:byáµáµ   = âáµáµâ»Â¹ unit-r-â
    isMonoid.assoc-l-â isMonoid:byáµáµ  = âáµáµâ»Â¹ assoc-l-â
    isMonoid._âââ_ isMonoid:byáµáµ = {!!}





