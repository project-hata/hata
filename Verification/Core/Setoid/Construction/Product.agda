
module Verification.Core.Setoid.Construction.Product where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category

_×-𝐒𝐭𝐝_ : 𝐒𝐭𝐝 𝑖 -> 𝐒𝐭𝐝 𝑗 -> 𝐒𝐭𝐝 _
_×-𝐒𝐭𝐝_ A B = A × B


