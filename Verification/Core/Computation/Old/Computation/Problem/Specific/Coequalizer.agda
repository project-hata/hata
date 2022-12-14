
module Verification.Core.Theory.Computation.Problem.Specific.Coequalizer where

open import Verification.Core.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Core.Category.Std.Category.As.Monoid
-- open import Verification.Core.Algebra.MonoidWithZero.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Theory.Computation.Problem.Definition
open import Verification.Core.Theory.Computation.Problem.Specific.Forall
-- open import Verification.Core.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat
-- open import Verification.Core.Theory.Computation.Refinement.Paradigm.DivideAndConquer

record UnificationProblem (π : π ^ 3) : π° (π βΊ) where
  constructor unifyP
  field π : Category π
  field {{isDiscrete:π}} : isDiscrete β¨ π β©
  field {{isSet-Str:π}} : isSet-Str β¨ π β©
  -- field a b : β¨ π β©
  -- field f g : a βΆ b

macro
  UNIFY : β π -> SomeStructure
  UNIFY π = #structureOn (UnificationProblem π)

-- UNIFY = UnificationProblem

module _ {π : Category π} where
  record Pair : π° π where
    constructor pair
    field {PairDomain} : β¨ π β©
    field {PairCodomain} : β¨ π β©
    field arrowβ arrowβ : PairDomain βΆ PairCodomain

  hasUnification : Pair -> π° _
  hasUnification (pair f g) = isDecidable (β isCoequalizer f g)

instance
  isProblem:UNIFY : β{π : π ^ 3} -> isProblem _ (UNIFY π)
  isProblem:UNIFY = problem (Ξ» P -> β (a : Pair {π = UnificationProblem.π P}) -> hasUnification a)




-- instance
--   isProblem:COEQ : isProblem (β¨ π) (COEQ π)
--   isProblem:COEQ = record
--     { Solution = Ξ» a β β (Ξ» (x : β¨ CoeqProblem.π a β©) -> isCoequalizer (CoeqProblem.f a) (CoeqProblem.g a) x)
--     }

{-
record EpiPrincipalProblem (π : π) : π° (π βΊ) where
  field M : Monoidβ (π , π)
  field Ideal : Ideal-r M

EPIPRI : β π -> SomeStructure
EPIPRI π = structureOn (EpiPrincipalProblem π)


instance
  isProblem:EPIPRI : isProblem (π , π) (EPIPRI π)
  isProblem:EPIPRI = record
    { Property = const β€-π°
    ; Solution = Ξ» P a _ -> isEpiPrincipal (EpiPrincipalProblem.Ideal a)
    }


reduceCoeq : COEQ π -> EPIPRI _
reduceCoeq Ο = record
  { M = π―πΊπππ¬ππ (CoeqProblem.π Ο)
  ; Ideal = β² CoeqSolutions (arrow (CoeqProblem.f Ο)) (arrow (CoeqProblem.g Ο)) β²
  }

instance
  isReduction:reduce-Coeq : isReduction (COEQ π) (EPIPRI _) reduceCoeq
  isReduction:reduce-Coeq = record { propMap = Ξ» P x β tt ; solutionMap = Ξ» P PX a pa β {!!} }


coeq-epipri : β π -> SomeStructure
coeq-epipri π = structureOn (reduceCoeq {π = π})


ff : COEQ (π , π , π) βΆ EPIPRI _
ff = incl (coeq-epipri _)

xxx : ε (EPIPRI π) βΆ EPIPRI π
xxx = Ξ΅-ε


-}
