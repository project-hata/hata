
module Verification.Core.Set.Discrete where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Everything


record isDiscrete-βΌ (A : π° π) {{_ : isSetoid {π} A}} : π° (π ο½€ π) where
  field _β-βΌ_ : (a b : A) -> Decision (a βΌ b)
open isDiscrete-βΌ {{...}} public

record isSet-Str (A : π° π) : π° π where
  field isset-Str : β{a b : A} -> (p q : a β‘-Str b) -> p β‘-Str q
open isSet-Str {{...}} public

record isDiscrete' (A : π° π) : π° (π) where
  field {{decidableEquality}} : β{a : A} -> isπ«-Dec (Ξ» b -> β£ a β‘-Str b β£)
open isDiscrete' {{...}} public

module _ {A : π° π} {B : π° π} where
  instance
    isDiscrete':+ : {{_ : isDiscrete' A}} {{_ : isDiscrete' B}} -> isDiscrete' (A +-π° B)
    isDiscrete'.decidableEquality isDiscrete':+ = {!!}

