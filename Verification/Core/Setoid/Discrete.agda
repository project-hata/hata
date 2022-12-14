
module Verification.Core.Setoid.Discrete where

open import Verification.Conventions
-- open import Verification.Core.Data.Prop.Definition
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Setoid.Definition


isSetoid:byDiscrete : โ{A : ๐ฐ ๐} -> isSetoid {๐} A
isSetoid._โผ_ isSetoid:byDiscrete = _โก_
isSetoid.refl isSetoid:byDiscrete = refl-โก
isSetoid.sym isSetoid:byDiscrete = sym-Path
isSetoid._โ_ isSetoid:byDiscrete = _โ-โก_

module _ {A : ๐ฐ ๐}
         {B : ๐ฐ ๐} {{_ : isSetoid {๐} B}}
         where

  isSetoidHom:byDiscrete : {f : A -> B} -> isSetoidHom (A since isSetoid:byDiscrete) โฒ B โฒ f
  isSetoidHom:byDiscrete {f} = record { cong-โผ = ฮป p โ โกโโผ (cong f p) }





