
module Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Indexed.Definition


module _ {I : 𝒰 𝑖} {𝒞 : Category 𝑗} {{_ : hasFiniteCoproducts 𝒞}} where

  _⊔-𝐈𝐱_ : (a b : 𝐈𝐱 I 𝒞) -> 𝐈𝐱 I 𝒞
  _⊔-𝐈𝐱_ a b = indexed (λ i → ix a i ⊔ ix b i)


  module _ {a b : 𝐈𝐱 I 𝒞} where
    instance
      isCoproduct:⊔-𝐈𝐱 : isCoproduct a b (a ⊔-𝐈𝐱 b)
      isCoproduct.ι₀ isCoproduct:⊔-𝐈𝐱             = λ i -> ι₀
      isCoproduct.ι₁ isCoproduct:⊔-𝐈𝐱             = λ i -> ι₁
      isCoproduct.⦗ isCoproduct:⊔-𝐈𝐱 ⦘            = λ (f , g) i → ⦗ f i , g i ⦘
      isCoproduct.isSetoidHom:⦗⦘ isCoproduct:⊔-𝐈𝐱 = {!!}
      isCoproduct.reduce-ι₀ isCoproduct:⊔-𝐈𝐱      = {!!}
      isCoproduct.reduce-ι₁ isCoproduct:⊔-𝐈𝐱      = {!!}
      isCoproduct.expand-ι₀,ι₁ isCoproduct:⊔-𝐈𝐱       = {!!}


  instance
    hasCoproducts:𝐈𝐱 : hasCoproducts (𝐈𝐱 I 𝒞)
    hasCoproducts._⊔_ hasCoproducts:𝐈𝐱            = _⊔-𝐈𝐱_
    hasCoproducts.isCoproduct:⊔ hasCoproducts:𝐈𝐱  = isCoproduct:⊔-𝐈𝐱

  ⊥-𝐈𝐱 : 𝐈𝐱 I 𝒞
  ⊥-𝐈𝐱 = indexed λ _ -> ⊥

  instance
    isInitial:⊥-𝐈𝐱 : isInitial ⊥-𝐈𝐱
    isInitial:⊥-𝐈𝐱 = {!!}

  instance
    hasInitial:𝐈𝐱 : hasInitial (𝐈𝐱 I 𝒞)
    hasInitial.⊥ hasInitial:𝐈𝐱 = ⊥-𝐈𝐱
    hasInitial.isInitial:⊥ hasInitial:𝐈𝐱 = {!!}

  instance
    hasFiniteCoproducts:𝐈𝐱 : hasFiniteCoproducts (𝐈𝐱 I 𝒞)
    hasFiniteCoproducts:𝐈𝐱 = hasFiniteCoproducts:default



