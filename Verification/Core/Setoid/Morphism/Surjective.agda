
module Verification.Core.Setoid.Morphism.Surjective where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isSetoid {𝑖₁} A}} {{_ : isSetoid {𝑗₁} B}} where
  record isSurjective (f : A -> B) {{_ : isSetoidHom ′ A ′ ′ B ′ f}} : 𝒰 (𝑖 ､ 𝑖₁ ､ 𝑗 ､ 𝑗₁) where
    constructor surjective
    field surj : B -> A
    field {{isSetoidHom:surj}} : isSetoidHom ′ B ′ ′ A ′ surj
    field inv-surj : ∀{b : B} -> f (surj b) ∼ b

  open isSurjective {{...}} public


