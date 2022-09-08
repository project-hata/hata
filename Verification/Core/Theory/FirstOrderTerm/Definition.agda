
module Verification.Core.Theory.FirstOrderTerm.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.FiniteIndexed.Definition
-- open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.FirstOrderTerm.Signature

-- | The informal intuition behind terms is as follows:
--   Every function symbol in |Con αs β| can be considered as
--   a function |(α₁ × ⋯ × αₙ) → β|. A term is formed by
--   composing these function symbols with each other,
--   thus it also has a natural interpretation as a function.
-- | Yet by adding variables, we create a distinction between
--   terms and "compositions of function symbols": Terms are also
--   allowed to discard their inputs, or use them multiple times.
-- | For example,
--   let |f : α × α × β → γ| and |g : α → β| be function symbols,
--   then we can form
--   the term $\(t₁ : α × α × α → γ\)$
--   by writing $\(t₁(a₁,a₂,a₃) = f(a₁,a₂,g(a₃)) \)$.
--   But as the notation suggests, we can also form terms which
--   use their inputs twice, or discard them, e.g.,
--   the term $\(t₂ : α × α → γ\)$, given by $\(t₂(a₁, a₂) = f(a₁,a₁,g(a₁))\)$.
-- | From the point of view of type theory, the list of input sorts
--   may also be considered as a context, a term $\(t : Γ → τ\)$
--   is then simply a well typed term $\(Γ ⊢ t : τ\)$.
-- | For the next definition this means that the type of terms is
--   similarly parametrized by a list of input sorts, and an output sort.
--   A small difference is that, due to compatibility with further definitions
--   of substitutions and coproducts, we use binary instead of unary lists here.

-- [Definition]
-- | Let [..] be a signature.
module _ (Σ : FOSignature 𝑖) where
  -- |> Then /many sorted terms over/ |Σ| are formalized by the type [..].
  data FOTerm : ⋆List (Sort Σ) -> Sort Σ -> 𝒰 𝑖 where
  -- |> It is defined inductively with two constructors,
  -- | - {} [..]
    var : ∀{α αs} -> αs ∍ α -> FOTerm αs α
  -- | - {} [..].
    con : ∀{γs βs α} -> (f : Con Σ βs α) -> ⋆List[ β ∈ ι βs ] (FOTerm γs β) -> FOTerm γs α

  -- |: Here, |var| is the base case, and creates a term containing only a single variable.
  --   Intuitively this can be seen as a projection function onto the component |α| of the
  --   list of inputs |αs|.
  -- | Larger terms are built with |con|, which requires a function symbol |f : βs → α|,
  --   and for each |β ∈ βs|, a term of that sort in a different context |γs|. Evidently,
  --   these terms can be prepended to |f|.

-- //



-- [Hide]
-- | We also define |term-FO| as a function |𝐅𝐢𝐧𝐈𝐱 ⟶ 𝐈𝐱|.

  open import Verification.Core.Data.Indexed.Definition
  open import Verification.Core.Data.FiniteIndexed.Definition

  termᵘ-FO : (𝐅𝐢𝐧𝐈𝐱 (Sort Σ)) -> (𝐈𝐱 (Sort Σ) (𝐔𝐧𝐢𝐯 𝑖))
  termᵘ-FO Γ = indexed (λ τ → FOTerm ⟨ Γ ⟩ τ)

  macro term-FO = #structureOn termᵘ-FO

-- //

