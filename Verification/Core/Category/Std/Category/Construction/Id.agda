
module Verification.Core.Category.Std.Category.Construction.Id where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso



private
  module _ {A : š° š} where
    lem-1 : ā{a b : A} {p : a ā£ b} -> p ā-ā£ refl-ā£ ā£ p
    lem-1 {p = refl-ā£} = refl-ā£

    lem-2 : ā{a b c d : A} {p : a ā£ b} {q : b ā£ c} {r : c ā£ d} -> (p ā-ā£ q) ā-ā£ r ā£ p ā-ā£ (q ā-ā£ r)
    lem-2 {p = refl-ā£} = refl-ā£

    lem-3 : ā{a b c : A} -> {pā pā : a ā£ b} {qā qā : b ā£ c} -> (pā ā£ pā) -> (qā ā£ qā) -> (pā ā-ā£ qā ā£ pā ā-ā£ qā)
    lem-3 refl-ā£ refl-ā£ = refl-ā£


module _ {A : š° š} where

  isCategory:byId : isCategory A
  isCategory.Hom isCategory:byId          = _ā£_
  isCategory.isSetoid:Hom isCategory:byId = isSetoid:byId
  isCategory.id isCategory:byId           = refl-ā£
  isCategory._ā_ isCategory:byId          = _ā-ā£_
  isCategory.unit-l-ā isCategory:byId     = refl-ā£
  isCategory.unit-r-ā isCategory:byId     = lem-1
  isCategory.unit-2-ā isCategory:byId     = refl-ā£
  isCategory.assoc-l-ā isCategory:byId {f = p} = lem-2 {p = p}
  isCategory.assoc-r-ā isCategory:byId {f = p} = sym-ā£ (lem-2 {p = p})
  isCategory._ā_ isCategory:byId          = lem-3



