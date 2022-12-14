
module Verification.Core.Theory.Computation.Question.Specific.Infer where

open import Verification.Core.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Theory.Computation.Question.Definition

record Infer (ð : ð ^ 4) : ð° (ð âº) where
  constructor infer
  field Input : ð° (ð â 0)
  field Info : Input -> Category (ð â 1 , ð â 2 , ð â 3)

  -- field forget : â¨ Info â© -> Input
  -- Sum : Input -> ð° _
  -- Sum i = â Î» (x : â¨ Info â©) -> forget x â£ i
  -- ÏSum : â i -> Sum i -> â¨ Info â©
  -- ÏSum i (x , _) = x

open Infer public

  -- field Answer : Input -> 
  -- field 
  -- field isCorrect : (i : Input) -> (a : Answer i) -> ð° (ð â 4)

-- open Check public

macro
  INFER : â ð -> SomeStructure
  INFER ð = #structureOn (Infer ð)

-- -- record CheckingSolution (Î  : CheckingQuestion ð) : ð° ð where
-- --   field decideSolution : â q a -> isDecidable (Î  .Correct q a)

record hasInitial (ð : Category ð) : ð° ð where
  field â¥ : â¨ ð â©
  field initial-â¥ : â{a} -> â¥ â¶ a

instance
  isQuestion:INFER : â {ð} -> isQuestion _ (INFER ð)
  isQuestion:INFER = answerWith Î» (inf) â â (i : Input inf) -> hasInitial (Info inf i)

  -- Î» q â â i a -> isDecidable (isCorrect q i a)

-- CheckFam : Check ð -> ðð®ðð¬ð­ _
-- CheckFam (check i a c) = (â a) since answerWith (Î» (i , a) â isDecidable (c i a))

-- instance
--   isReductive:CheckFam : isReductive (INFER ð) (ðð®ðð¬ð­ _) CheckFam
--   isReductive:CheckFam = reductive Î» x i a â x (i , a)
