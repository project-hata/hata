
module Verification.Core.Theory.Computation.Problem.Paradigm.DivideAndConquer where

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


---------------------------------------------------------------
-- Every problem can be turned into the problem of
-- finding a divide and conquer solution

record DivideAndConquer (Ξ  : Problem π) : π° (π β 0) where
  constructor dac
  field original : β¨ Ξ  β©
open DivideAndConquer {{...}} public

record DivideAndConquerProp (Ξ  : Problem π) (P : DivideAndConquer Ξ  -> π° (fst π)) : π° (fst π ο½€ (snd π) βΊ) where
  field Size : WFT (ββ , ββ)
  field size : (β P) -> β¨ Size β©
  -- field originalP : π± {{of Ξ }} (P β£ dac)
--   -- field β : β¨ Ξ  β© -> β Ξ» n -> Fin-R n -> β¨ Ξ  β©
--   -- field size-β : β p -> β i -> size (β p .snd i) βͺ size p

open DivideAndConquerProp {{...}} public

DAC : β (Ξ  : Problem π) -> SomeStructure
DAC Ξ  = structureOn (DivideAndConquer Ξ )

instance
  isProblem:DAC : β{Ξ  : Problem π} -> isProblem (π β 1) (DAC Ξ )
  isProblem:DAC {Ξ  = Ξ } = record
    { π± = DivideAndConquerProp Ξ 
    }

γΆγ : Problem π -> Problem π
γΆγ Ξ  = DAC Ξ 

ε : β {π} -> SomeStructure
ε {π} = structureOn (γΆγ {π})


private
  module _ {Ξ  : Problem π} where
    Ξ΅ : DAC Ξ  -> β¨ Ξ  β©
    Ξ΅ x = x .original

    -- Ξ· : β¨ Ξ  β© -> DAC Ξ 
    -- Ξ· x = dac x

    instance
      isReduction:Ξ· : isReduction (DAC Ξ ) Ξ  Ξ΅
      isReduction:Ξ· = record
        { valid = Ξ» P x β {!!}
        }
        -- { propMap = Ξ» P x β let y = originalP {{x}}
        --                     in {!!}
        -- ; solutionMap = {!!}
        -- }

-- Ξ·-ε : β{Ξ  : Problem π} -> ε Ξ  βΆ Ξ 
-- Ξ·-ε = incl β² Ξ· β²













































