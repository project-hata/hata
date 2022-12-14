
module Verification.Core.Data.Universe.Instance.SeparatingFamily where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily
open import Verification.Core.Data.Universe.Instance.Category


private
  sep : β π -> β{π} -> β€-π° {π} -> π° π
  sep _ = const β€-π°

instance
  isSeparatingFamily:constβ€ : isSeparatingFamily (ππ§π’π― π) (sep π)
  isSeparatingFamily.separate isSeparatingFamily:constβ€ Ο Ο x = P
    where
      P : Ο βΌ Ο
      P = Ξ» i a β x {tt} (const a) i tt

module _ {π} {π} where
  instance
    hasSeparatingFamily:ππ§π’π― : hasSeparatingFamily π (ππ§π’π― π)
    hasSeparatingFamily:ππ§π’π― = record
                                { separator = sep π
                                ; isSeparatingFamily:seperators = it
                                }



