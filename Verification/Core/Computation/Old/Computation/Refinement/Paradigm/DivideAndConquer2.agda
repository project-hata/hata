
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
  field original : β¨ Ξ  β©
open DivideAndConquer {{...}} public

record DivideAndConquerProp (Ξ  : Problem π) (P : DivideAndConquer Ξ  -> π° _) : π° (fst π ο½€ (fst (snd π)) βΊ) where
  field Size : WFT (ββ , ββ)
  field size : (β P) -> β¨ Size β©
  field originalP : Property {{of Ξ }} (Ξ» x -> (P (record {original = x})))
  -- field β : β¨ Ξ  β© -> β Ξ» n -> Fin-R n -> β¨ Ξ  β©
  -- field size-β : β p -> β i -> size (β p .snd i) βͺ size p

open DivideAndConquerProp {{...}} public

DAC : β (Ξ  : Problem π) -> SomeStructure
DAC Ξ  = structureOn (DivideAndConquer Ξ )

instance
  isProblem:DAC : β{Ξ  : Problem π} -> isProblem ((π β 1) , π β 2) (DAC Ξ )
  isProblem:DAC {Ξ  = Ξ } = record
    { Property = DivideAndConquerProp Ξ 
    ; Solution = {!!}
    }

γΆγ : Problem π -> Problem π
γΆγ Ξ  = DAC Ξ 

ε : β {π} -> SomeStructure
ε {π} = structureOn (γΆγ {π})

private
  module _ {Ξ  : Problem π} where
    Ξ΅ : DAC Ξ  -> β¨ Ξ  β©
    Ξ΅ x = x .original

    instance
      isReduction:Ξ΅ : isReduction (DAC Ξ ) Ξ  Ξ΅
      isReduction:Ξ΅ = record
        { propMap = Ξ» P x β let y = originalP {{x}}
                            in {!!}
        ; solutionMap = {!!}
        }

Ξ΅-ε : β{Ξ  : Problem π} -> ε Ξ  βΆ Ξ 
Ξ΅-ε = incl β² Ξ΅ β²


{-
-- record DivideAndConquerSolution {Ξ  : Problem π} (P : DivideAndConquer Ξ ) : π° π where
--   field β-solves : β (p : β¨ Ξ  β©) -> (β i -> SolutionSpace (β {{P}} p .snd i)) -> SolutionSpace p


module _ {Ξ  : Problem π} where
  instance
    isProblem:DAC : isProblem (π β 1) (DAC Ξ )
    isProblem:DAC = record
      { Property = DivideAndConquerProp Ξ 
      ; Solution = {!!}
      }
    -- record { SolutionSpace = DivideAndConquerSolution }

dac : Problem π -> Problem _
dac Ξ  = DAC Ξ 

fmap-dac : β{Ξ© Ξ  : Problem π} -> (f : Reduction Ξ© Ξ ) -> DAC Ξ© -> DAC Ξ 
fmap-dac f x = record { original = β¨ f β© (x .original) }

instance
  isReduction:fmap-dac : β{Ξ© Ξ  : Problem π} -> {f : Reduction Ξ© Ξ } -> isReduction (DAC Ξ©) (DAC Ξ ) (fmap-dac f)
  isReduction:fmap-dac {f = f} = record
    { propMap = Ξ» P x β record
                        { Size = x .Size
                        ; size = Ξ» (a , b , c) β let Q = x .size
                                                 in Q (_ , c .fst )
                        ; originalP = let Q = x .originalP
                                          xx = propMap {{of f}} _ Q
                                      in {!!}
                        }
    ; solutionMap = {!!}
                         -- { Size = x .Size
                         -- ; size = Ξ» y β let f = x .size
                         --                in f (_ , y .snd)
                         -- ; originalP = let Q = x .originalP
                         --                   xx = propMap {{of f}} _ Q
                         --               in xx
                         -- }
    }

module _ {Ξ  : Problem π} where
  -- Ξ·-DAC : β¨ Ξ  β© -> DAC Ξ 
  -- Ξ·-DAC x = record { original = x }

  Ξ·-DAC : DAC Ξ  -> β¨ Ξ  β©
  Ξ·-DAC x = x .original

  instance
    isReduction:Ξ·-DAC : isReduction (DAC Ξ ) Ξ  Ξ·-DAC
    isReduction:Ξ·-DAC = record
      { propMap = Ξ» P x β let y = originalP {{x}}
                          in {!!}
      ; solutionMap = {!!}
      }


-}
