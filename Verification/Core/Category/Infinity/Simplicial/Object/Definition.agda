
module Verification.Core.Category.Infinity.Simplicial.Object.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Set.Finite.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Set.Discrete
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Representable
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Infinity.Simplicial.Simplex.Definition

Simplicial : β π -> (π : Category π) -> π° _
Simplicial π π = Functor (βL π α΅α΅) π


βStd : β π π -> π° _
βStd π π = Simplicial π (Std π)


-- now we want to build examples
β[_] : β(n : β) -> βStd _ _
β[ n ] = β² [_, β² Fin n β² ]π β²

-- sss = β[ 0 ]

-- now, by yoneda, we have
lem-10 : β{X : βStd _ _} -> (β¨ X β© β² Fin n β²) βπ [ β[ n ] , X ]π
lem-10 = {!!}


