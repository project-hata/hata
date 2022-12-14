
module Verification.Core.Theory.FirstOrderTerm.Signature where

open import Verification.Conventions hiding (_â_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition


-- | Abstractly, first order terms are defined to
--   made up of free variables and function symbols.
--   Each function symbol has a finite number
--   of inputs and a single output. In the many sorted case
--   the inputs and outputs of a symbol carry a type (usually called a sort),
--   and only well-typed compositions are allowed.
--   The available sorts and function symbols for a particular
--   term system are succinctly given in a /signature/.

-- [Definition]
-- | A /signature for many sorted terms/,
--   which we call [..], is given by the following data.
record FOSignature (đ : đ) : đ° (đ âē) where

  -- | 1. A type of sorts [..].
  field Sort : đ° đ

  -- | 2. A parametrized type of function symbols, here called constructors, [...,]
  --      where |Con Îąs Î˛| contains function symbols
  --      with input sorts |Îąs| and output sort |Î˛|.
  field Con : List Sort -> Sort -> đ° đ

  -- | 3. Proofs that those sets are discrete,
  --      i.e., have decidable equality.
  field {{isDiscrete:Sort}} : isDiscrete Sort
  field {{isDiscrete:Con}} : â{Îąs Îą} -> isDiscrete (Con Îąs Îą)
  field {{isSet-Str:Sort}} : isSet-Str Sort

open FOSignature public

-- #Notation/Rewrite# FOSignature = Sig_{FO}
-- //

-- [Remark]
-- | The discreteness of the sort and constructor
--   types is required by unification, since the algorithm needs to
--   compare sorts and constructors when unifying terms. On the other hand,
--   no finiteness assumptions are neccessary.

-- //



-- [Hide]
module _ (đ : đ) where
  macro đÃ = #structureOn (FOSignature đ)
-- //

-- [Hide]
-- | We show that the type of sorts of a signature
--   is a set.
-- module _ {ÎŖ : FOSignature đ} where
--   instance
--     isSet-Str:Sort : isSet-Str (Sort ÎŖ)
--     isSet-Str:Sort = {!!}

-- //


