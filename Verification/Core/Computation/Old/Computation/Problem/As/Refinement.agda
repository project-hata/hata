
module Verification.Core.Theory.Computation.Problem.As.Refinement where

open import Verification.Core.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Theory.Computation.Problem.Definition
open import Verification.Core.Theory.Computation.Refinement.Definition



refine : ๐๐ซ๐จ๐ ๐ -> ๐๐๐ ๐
refine ฮ  = {!!}

็ทด : โ {๐} -> SomeStructure
็ทด {๐} = structureOn (refine {๐})

instance
  isFunctor:็ทด : isFunctor (๐๐ซ๐จ๐ ๐) (๐๐๐ ๐) ็ทด
  isFunctor:็ทด = {!!}


