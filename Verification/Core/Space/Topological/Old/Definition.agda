
module Verification.Core.Space.Topological.Definition where

open import Verification.Conventions hiding (Discrete ; â ; Bool ; _and_)
open import Verification.Core.Setoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice

module _ {A : ð° ð} {ðª : ð° ð} (Open : ðª -> (A -> Prop ð)) where
  record isGoodFamily (B : ð° ð) (F : B -> ðª) : ð° ð where
    constructor goodFamily
    field noEmpties : â(b : B) -> â Î» a -> â¨ Open (F b) a â©
    field decideBase : isDecidable B

  open isGoodFamily public

  GoodFamily : (B : ð° ð) -> _
  GoodFamily B = (B -> ðª) :& isGoodFamily B

record isTopologicalá¶ (A : ð° ð) : ð° (ð âº âº) where
  constructor topological
  field ðª : ð° (ð âº)
  field Open : ðª -> (A -> Prop ð)
  field â : ðª
  field â§ : ðª
  field _â©_ : ðª -> ðª -> ðª
  field â : â{B} -> (U : GoodFamily Open B) -> ðª
  field eval-â : Open â â¼ â¥
  field eval-â§ : Open â§ â¼ â¤
  field eval-â© : â{u v : ðª} -> Open (u â© v) â¼ Open u â§ Open v
  field eval-â : â{B} {U : GoodFamily Open B} -> Open (â U) â¼ â (Open â â¨ U â©)

  -- private
  --   None : â¥-ð° -> ðª
  --   None = Î» ()

  -- â : ðª
  -- â = â (None since goodFamily (Î» ()) (left (Î» ())))

  -- eval-â : Open â â¼ â¥
  -- eval-â = {!!} -- incl ({!!} , {!!})

open isTopologicalá¶ {{...}} public

Topologicalá¶ : â ð -> ð° _
Topologicalá¶ ð = ð° ð :& isTopologicalá¶

ðð¨ð©á¶ : â ð -> SomeStructure
ðð¨ð©á¶ ð = #structureOn (Topologicalá¶ ð)




