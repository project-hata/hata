
module Verification.Core.Category.Std.Groupoid.As.Setoid where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Groupoid.Definition

GroupoidAsSetoid : Groupoid ๐ -> Setoid _
GroupoidAsSetoid ๐ข = โจ ๐ข โฉ since isSetoid:byDef (ฮป a b -> a โถ b) id _โปยน-๐๐ซ๐ฉ๐ _โ_



