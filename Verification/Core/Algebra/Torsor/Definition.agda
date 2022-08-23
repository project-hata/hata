
module Verification.Core.Algebra.Torsor.Definition where

open import Verification.Conventions
-- open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Algebra.MonoidAction.Instance.Category
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Op.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full2

-- record isTorsor (M : Monoid 𝑖) (T : Acted M 𝑗) : 𝒰 (𝑖 ､ 𝑗) where

module _ (M : Monoid 𝑖) where
  isTorsor : ∀{𝑗} -> Acted M 𝑗 -> _
  isTorsor = isFreeActed :, isTransitiveActed

  Torsor : ∀ 𝑗 -> _
  Torsor 𝑗 = _ :& isTorsor {𝑗}


-- _-𝐓𝐨𝐫𝐬 : (Monoid 𝑖 ×-𝒰 𝔏 ^ 2) -> 𝒰 _
-- _-𝐓𝐨𝐫𝐬 (M , 𝑗) = Torsor M 𝑗

module _ 𝑖 𝑗 where
  record 𝐓𝐨𝐫𝐬ᵘ : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
    constructor _,_
    field fst : Monoid 𝑖
    field snd : Torsor fst 𝑗

  macro 𝐓𝐨𝐫𝐬 = #structureOn 𝐓𝐨𝐫𝐬ᵘ


ιᵘ-𝐓𝐨𝐫𝐬 : 𝐓𝐨𝐫𝐬 𝑖 𝑗 -> 𝐀𝐜𝐭 _ _
ιᵘ-𝐓𝐨𝐫𝐬 (M , T) = M , ↳ T

module _ {𝑖 𝑗} where
  instance
    isCategory:𝐓𝐨𝐫𝐬 : isCategory (𝐓𝐨𝐫𝐬 𝑖 𝑗)
    isCategory:𝐓𝐨𝐫𝐬 = isCategory:FullSubcategory (ιᵘ-𝐓𝐨𝐫𝐬 {𝑖} {𝑗})

-- 𝐓𝐨𝐫𝐬ᵘ : ∀ 𝑖 𝑗 -> 𝒰 _
-- 𝐓𝐨𝐫𝐬ᵘ 𝑖 𝑗 = FullSubcategory (𝐀𝐜𝐭 _ _) (ιᵘ-𝐓𝐨𝐫𝐬 {𝑖} {𝑗})



