
module Verification.Core.Category.Std.Category.Instance.FiniteProductCategory where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Construction.Id
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Construction.Product


module _ {๐ ๐ : ๐๐๐ญ ๐} where
  instance
    isProduct:ร-๐๐๐ญ : isProduct ๐ ๐ (๐ ร ๐)
    isProduct:ร-๐๐๐ญ = record
                        { ฯโ        = ฯโ-๐๐๐ญ
                        ; ฯโ        = ฯโ-๐๐๐ญ
                        ; โงผ_โงฝ       = ฮป (f , g) -> โงผ f , g โงฝ-๐๐๐ญ
                        ; isSetoidHom:โงผโงฝ = {!!}
                        ; reduce-ฯโ = ฮป {x} {f} {g} -> reduce-ฯโ-๐๐๐ญ {F = f} {G = g}
                        ; reduce-ฯโ = ฮป {x} {f} {g} -> reduce-ฯโ-๐๐๐ญ {F = f} {G = g}
                        ; expand-ฯโ,ฯโ  = expand-โ-๐๐๐ญ
                        }


instance
  isTerminal:๐ : isTerminal {๐ = ๐๐๐ญ ๐} โค-๐๐๐ญ
  isTerminal:๐ = record
                 { intro-โค   = intro-โค-๐๐๐ญ
                 ; expand-โค  = expand-โค-๐๐๐ญ
                 }

instance
  hasProducts:๐๐๐ญ : hasProducts (๐๐๐ญ ๐)
  hasProducts:๐๐๐ญ = record {_โ_ = _ร-๐๐๐ญ_}

instance
  hasTerminal:๐๐๐ญ : hasTerminal (๐๐๐ญ ๐)
  hasTerminal:๐๐๐ญ = record {โค = โค-๐๐๐ญ}

instance
  hasFiniteProducts:๐๐๐ญ : hasFiniteProducts (๐๐๐ญ ๐)
  hasFiniteProducts:๐๐๐ญ = hasFiniteProducts:default
  -- record { _โ_ = _ร-๐๐๐ญ_ ; โค = โค-๐๐๐ญ }

