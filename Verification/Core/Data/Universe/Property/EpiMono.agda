
module Verification.Core.Data.Universe.Property.EpiMono where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Set.Function.Injective

module _ {A B : ð° ð} where
  construct-isMono-ðð§ð¢ð¯ : â{f : A -> B} -> isInjective-ð° f -> isMono f
  isMono.cancel-mono (construct-isMono-ðð§ð¢ð¯ p) Î±fâ¼Î²f = Î» i a â cancel-injective-ð° (Î» j -> Î±fâ¼Î²f j a) i
    where instance _ = p

  destruct-isMono-ðð§ð¢ð¯ : â{f : A -> B} -> isMono f -> isInjective-ð° f
  isInjective-ð°.cancel-injective-ð° (destruct-isMono-ðð§ð¢ð¯ {f} p) {a} {b} faâ¼fb = Î» i -> Pâ i tt
    where
      instance _ = p

      Î± : â¤-ð° {ð} -> A
      Î± = const a

      Î² : â¤-ð° {ð} -> A
      Î² = const b

      Pâ : Î± â f â¡ Î² â f
      Pâ = Î» i _ â faâ¼fb i

      Pâ : Î± â¡ Î²
      Pâ = cancel-mono Pâ





