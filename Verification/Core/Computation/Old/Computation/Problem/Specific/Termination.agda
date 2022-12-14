
module Verification.Core.Theory.Computation.Problem.Specific.Termination where

open import Verification.Core.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Core.Category.Std.Category.As.Monoid
-- open import Verification.Core.Algebra.MonoidWithZero.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Theory.Computation.Problem.Definition
-- open import Verification.Core.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat
-- open import Verification.Core.Theory.Computation.Problem.Paradigm.DivideAndConquer


record TerminationProblem (๐ : ๐) : ๐ฐ (๐ โบ) where
  field Base : ๐ฐ ๐
  field step : Base -> Base
  field isDone : Base -> Bool

open TerminationProblem {{...}} public

data IterationStep (T : TerminationProblem ๐) : Base {{T}} -> ๐ฐ ๐ where
  done : โ{a} -> isDone {{T}} a โฃ true -> IterationStep T a
  next : โ{a b} -> step {{T}} a โฃ b -> IterationStep T b -> IterationStep T a

TerminationSolution : (T : TerminationProblem ๐) -> ๐ฐ ๐
TerminationSolution T = โ a -> IterationStep T a

TERMINATION : โ ๐ -> SomeStructure
TERMINATION ๐ = structureOn (TerminationProblem ๐)

-- ็ทด :

-- TERMINATION : 

instance
  isProblem:TERMINATION : โ {๐} -> isProblem _ (TERMINATION ๐)
  isProblem:TERMINATION = problem TerminationSolution

-- ็ทด

-- record TerminationSolution (T : TerminationProblem ๐) : ๐ฐ ๐ where
--   field 



