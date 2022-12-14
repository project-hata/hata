
module Verification.Core.Space.Topological.Specific.Discrete where

open import Verification.Conventions hiding (Discrete ; β ; Bool ; _and_)
open import Verification.Core.Setoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice

open import Verification.Core.Space.Topological.Definition



module _ {π : π} where
  data Bool : π° π where
    false true : Bool

  macro πΉ = #structureOn Bool

_and_ : β{π} -> πΉ {π} -> πΉ {π} -> πΉ {π}
false and b = false
true and b = b


--------------------------------------------------------------------------------
-- Discrete topology on a type

{-
record Discrete (A : π° π) : π° π where
  constructor incl
  field β¨_β© : A

open Discrete public

macro
  π£πππΌ : β(A : π° π) -> SomeStructure
  π£πππΌ A = #structureOn (Discrete A)

instance
  isTopologicalαΆ:DiscreteTopological : β{A : π° π} -> isTopologicalαΆ (π£πππΌ A)
  isTopologicalαΆ:DiscreteTopological {π} {A = A} = topological πͺ' Open' β₯ β€ (_β§_) (Ξ» F -> β β¨ F β©) refl refl refl refl
    where πͺ' = (A -> Prop π)
          Open' = Ξ» u a -> u β¨ a β©

-}

--------------------------------------------------------------------------------
-- Codiscrete topology on a type

record Codiscrete (A : π° π) : π° π where
  constructor incl
  field β¨_β© : A

open Codiscrete public

macro
  π’ππ£πππΌ : β(A : π° π) -> SomeStructure
  π’ππ£πππΌ A = #structureOn (Codiscrete A)


module _ {A : π° π} {B : π° π} where
  ββ : (A -> B -> Prop π) -> B -> Prop (π ο½€ π)
  ββ R b = β£ β (Ξ» a β β¨ R a b β©) β£



instance
  isTopologicalαΆ:CodiscreteTopological : β{A : π° π} -> isTopologicalαΆ (π’ππ£πππΌ A)
  isTopologicalαΆ:CodiscreteTopological {π} {A = A} = topological πΉ Open' lem-1 {!!}
    where Open' : πΉ -> _
          Open' (true) = β€
          Open' (false) = β₯

          lem-1 : ββ Open' βΌ β€
          lem-1 = antisym terminal-β€ (incl (Ξ» x β true , tt))

          lem-2 : β{a b : πΉ} -> Open' a β§ Open' b βΌ β (Ξ» (x : β¦ a β[ Open' ] b β¦) -> Open' β¨ x β©)
          lem-2 {false} {b} = β₯ β§ Open' b    β¨ absorb-l-β§ β©-βΌ
                              β₯              β¨ antisym initial-β₯ (incl (Ξ» ((x β’ xp) , y) β {!!})) β©-βΌ
                              β (Ξ» (x : β¦ false β[ Open' ] b β¦) -> Open' β¨ x β©) β
          lem-2 {true} {b} = {!!}




-- topological πͺ' Open' (false) (true) (_and_) union refl refl (Ξ» {u} {v} -> lem-1 {u} {v}) (Ξ» {B} {U} -> lem-2 {B} {U})
--     where πͺ' = Bool
--           Open' : πΉ -> _
--           Open' (true) = β€
--           Open' (false) = β₯

--           union : {B : π° π} β GoodFamily Open' B β πͺ'
--           union F with decideBase (of F)
--           ... | left x = false
--           ... | just x = true

--           lem-1 : {u v : πͺ'} β Open' (u and v) βΌ Open' u β§ Open' v
--           lem-1 {false} {v} = absorb-l-β§ β»ΒΉ
--           lem-1 {true} {v} = unit-l-β§ β»ΒΉ

--           lem-2 : {B : π° π} {U : GoodFamily Open' B} β
--                   Open' (union U) βΌ (β (Open' β β¨ U β©))
--           lem-2 {B} {U} with decideBase (of U)
--           ... | left x = empty-β x β»ΒΉ
--           ... | just b =
--                    β€                       β¨ absorb-r-β¨ β»ΒΉ β©-βΌ
--                    (β (Open' β β¨ U β©)) β¨ β€ β¨ duplicate-r-β b P β©-βΌ
--                    (β (Open' β β¨ U β©))      β
--                 where P : Open' (β¨ U β© b) βΌ β€
--                       P with  β¨ U β© b | noEmpties (of U) b
--                       ... | true | Y = refl

