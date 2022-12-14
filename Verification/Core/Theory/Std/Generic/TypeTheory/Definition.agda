
module Verification.Core.Theory.Std.Generic.TypeTheory.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
-- open import Verification.Core.Data.Sum.Definition
-- open import Verification.Core.Data.Rational.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full2
open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Computation.Question.Construction.Product
open import Verification.Core.Theory.Std.Generic.Theory.Definition
open import Verification.Core.Computation.Question.Definition
open import Verification.Core.Computation.Question.Specific.Check
open import Verification.Core.Computation.Question.Specific.Small

open import Verification.Core.Data.Family.Definition
open import Verification.Core.Data.Family.Instance.Fibration
open import Verification.Core.Category.Std.Fibration.BaseChange.Definition
open import Verification.Core.Category.Std.Fibration.Definition
open import Verification.Core.Category.Std.Fibration.Instance.BaseChange

--------------------------------------------------------------------
-- The type theoretical perspective on a theory

record isTypeTheory (π : π ^ 3) (Type : π° π) : π°' (π βΊ ο½€ π) where
  constructor typeTheory

  field Termα΅ : π° (π β 0)
  field {{isSetoid:Term}} : isSetoid {π β 1} Termα΅

  field _βΆ_ : Termα΅ -> Type -> π° (π β 2)
  field preserveType : β {tβ tβ} -> (tβ βΌ tβ) -> β{Ο : Type} -> tβ βΆ Ο -> tβ βΆ Ο

  macro Term = #structureOn Termα΅

  TypedTermα΅ : Type -> π° _
  TypedTermα΅ Ο = (β Ξ» (t : Term) -> t βΆ Ο)

  instance
    isSetoid:TypedTerm : β{Ο : Type} -> isSetoid {π β 0} (TypedTermα΅ Ο)
    isSetoid:TypedTerm = {!!}


open isTypeTheory {{...}} public

TypeTheory : (π : π ^ 4) -> π° _
TypeTheory π = (π° (π β 0)) :& isTypeTheory (π β 1 β― 3)


private
  Forget : TypeTheory π -> Theory _
  Forget π£  = β¨ π£ β© since theory Ξ» Ο β TypedTermα΅ Ο

instance
  Register:ForgetTypeTheory = registerβ[ "" , π ] (Forget {π})

macro
  ππ : β(π) -> SomeStructure
  ππ (π) = #structureOn (TypeTheory π)

instance
  isCategory:ππ : isCategory (ππ π)
  isCategory:ππ = isCategory:FullSubcategory Forget

---------------------------------------------------------------
-- Solved Type theories are ones for which the type checking
-- problem is solved

private
  Q : ππ π -> ππ?ππ¬π­ _
  Q π£ = (Term Γ-π° β¨ π£ β©) since answerWith (Ξ» (t , Ο) -> isDecidable (t βΆ Ο))


ππFam : β(π) -> Family (ππ?ππ¬π­ _) _
ππFam π = TypeTheory π since family Q

private macro
  p = instance[ "" , π / 3 ] (πππ¦ (ππ?ππ¬π­ (π β 0 β― 1)) (π β 2) -> ππ²π©π _) β

ππFib : β π -> Fiber (p) (TypeTheory π)
ππFib π = ππFam π since record { isSectionFiber = refl-β£ }


instance
  hasBaseChange:ππ²π©π : β {π : π ^ 3} -> hasBaseChange _ (ππ²π©π _)
  hasBaseChange:ππ²π©π {π} = hasBaseChange:Fibration (p {π})


trivialF : β{π} -> β{A} -> Fiber (p {π}) A
trivialF {A = A} = (A since family (Ξ» _ -> TRIVIAL))
           since record { isSectionFiber = refl-β£ }

module _ {A : π° _} {B} (X : Fiber (p {π}) B) (Ο : A -> B) where
  Solution : π° _
  Solution = β¨ Ο *! β© X βΆ trivialF






{-
record SolvedTypeTheoryClass π : π° (π βΊ βΊ) where
  field Param : π° _
  field theory : Param -> TypeTheory π
  field solution : Solution (ππFam π) theory

open SolvedTypeTheoryClass public

checkClass : (π£ : SolvedTypeTheoryClass π) -> (p : Param π£) -> (t : Term {{of theory π£ p}}) -> (Ο : β¨ theory π£ p β©) -> isDecidable (_βΆ_ {{of theory π£ p}} t Ο)
checkClass π£ p t =
  let X = map-β  {{of β¨ β¨ β¨ solution π£ β© β© β©}}
  in {!!}
-}





-- ---------------------------------------------------------------
-- -- Parsable type theories

-- record isParsable (π£ : ππ π) : π° π where
--   field parseTerm : String -> Term


---------------------------------------------------------------
-- the categorical structure

--  -> Category _
-- macro
--   TT : β {π} -> SomeStructure
--   TT {π} = #structureOn (FullSubcategory (ForgetTT {π}))

-- instance
--   isCategory:Theory : isCategory (_ , π β 0) (TypeTheory π)
--   isCategory:Theory = category TypeTheoryHom {{{!!}}} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}






