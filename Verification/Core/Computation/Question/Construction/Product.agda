
module Verification.Core.Computation.Question.Construction.Product where

open import Verification.Core.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Computation.Question.Definition




macro
  _Γ_ : (π° π) [ π ]β (π° π) [ π ]β SomeStructure
  _Γ_ = Ξ»str A β¦ Ξ»str B β¦ #structureOn (A Γ-π° B)
  infixr 50 _Γ_

  -- (Ξ» X -> Ξ»str (Ξ» B -> {!!}))
  -- (Ξ»[] B , #structureOn (X Γ-π° B))

  -- _Γ'_ : WithStructureOnΟ (π° π) (WithStructureOn (π° π) SomeStructure)
  -- _Γ'_ = Ξ»strΟ (Ξ» X -> Ξ»str ?)
  -- Ξ»str (Ξ» X -> Ξ»str (Ξ» B -> #structureOn (X Γ-π° B)))

  -- u {{UU}} {{refl-StrId}} B = #structureOn (destructEl UU u Γ-π° B)
  -- _Γ'_ u {{UU}} {{refl-StrId}} B = #structureOn (destructEl UU u Γ-π° B)
  -- #structureOn (A Γ-π° B)

-- macro
--   _Γ_ : β(A : π° π) (B : π° π) -> SomeStructure
--   _Γ_ A B = #structureOn (A Γ-π° B)


module _ {π : π° _} {π : π° _} {{_ : Question π on π}} {{_ : Question π on π}} where
  instance
    isQuestion:Γ : isQuestion _ (π Γ π)
    isQuestion:Γ = answerWith (Ξ» (p , q) β p β½ + q β½)


module _ {π π : Question π} where
  private
    Οβ : (π Γ π) βΆ π
    Οβ = incl (fst since reductive left)

    Οβ : (π Γ π) βΆ π
    Οβ = incl (snd since reductive right)

    β¨_,_β© : β{β : Question π} -> (f : β βΆ π) -> (g : β βΆ π) -> β βΆ π Γ π
    β¨_,_β© f g = incl ((Ξ» x β (β¨ β¨ f β© β© x , β¨ β¨ g β© β© x)) since reductive (either (reduce) (reduce)))


-- product : A β¨― (B β¨Ώ C) βΌ (A β¨― B β¨Ώ A β¨― C)
-- coproduct: β¨Ώ


-- β
-- U+221x 	β
-- β¨ 	β¨
-- ββ¨Ώ 
-- β 	β 	
-- β¨― 

-- β β union

-- xβy
-- βba \sqcup b if your fonts don't include ββ¨Ώ\amalg

  -- private
  --   Οβ : 




