
module Verification.Core.Category.Std.Fibration.BaseChange.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category


record hasBaseChange ๐ (๐ : Category ๐) : ๐ฐ (๐ โบ ๏ฝค ๐) where
  constructor basechange
  field Change : Functor (๐ แตแต) (๐๐๐ญ ๐)

  _*! : โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> Functor (โจ Change โฉ b) (โจ Change โฉ a)
  _*! f = map {{of Change}} (f)

  field โ! : โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> Functor (โจ Change โฉ a) (โจ Change โฉ b)
  field โ! : โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> Functor (โจ Change โฉ a) (โจ Change โฉ b)

open hasBaseChange {{...}} public
  -- โ!  โ! *!







{-
record hasBaseChange (๐ : Category ๐) : ๐ฐ (๐ โบ) where
  constructor basechange
  field MyTarget : ๐ฐโ
  field myMap : โ{a b : โจ ๐ โฉ} -> (a โถ b) -> MyTarget -> MyTarget

open hasBaseChange {{...}} public

instance
  hasBaseChange:Set1 : hasBaseChange (๐๐ฒ๐ฉ๐ ๐)
  hasBaseChange:Set1 = basechange โ (const (const 1))

instance
  hasBaseChange:Set2 : hasBaseChange (๐๐ฒ๐ฉ๐ ๐)
  hasBaseChange:Set2 = basechange Bool (const (const false))


mycall : Bool
mycall = myMap {a = โ} {b = โ} (id) true

-}
