
module Verification.Core.Theory.Std.Generic.LogicalFramework.Definition where

open import Verification.Core.Conventions hiding (Structure ; Σ)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full2
-- open import Verification.Core.Category.Std.Graph.Definition
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Set.Discrete
-- open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category


-------------------------------------------------------------------
-- Theories and models
----------------------------------------------------
-- ====* Possible extensions of the current concept
-- | The usual adjunction postulating the syntactical category of, e.g. lambda calculus
--   is:
--
-- |> $ % https://q.uiver.app/?q=WzAsMixbMCwwLCJcXFNpZ21hIl0sWzIsMCwiXFxtYXRoc2Nye019Il0sWzAsMSwiXFx0ZXh0e0ZyZWV9IiwwLHsiY3VydmUiOi0yfV0sWzEsMCwiXFx0ZXh0e0ZvcmdldH0iLDAseyJjdXJ2ZSI6LTJ9XSxbMiwzLCIiLDAseyJsZXZlbCI6MSwic3R5bGUiOnsibmFtZSI6ImFkanVuY3Rpb24ifX1dXQ==
-- \[\begin{tikzcd}
--  \Sigma && {\mathscr{M}}
--  \arrow[""{name=0, anchor=center, inner sep=0}, "{\text{LFTerm}}", curve={height=-12pt}, from=1-1, to=1-3]
--  \arrow[""{name=1, anchor=center, inner sep=0}, "{\text{LFSig}}", curve={height=-12pt}, from=1-3, to=1-1]
--  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=0, to=1]
-- \end{tikzcd}\] $


-- | But in the case of actual constructions of free term models one should be able to extend
--   those to another adjunction with the category of sheaves on |Σ|.

-- |> $ % https://q.uiver.app/?q=WzAsMixbMCwwLCJcXHRleHR7U2h9KFxcU2lnbWEpIl0sWzIsMCwiXFxtYXRoc2Nye019Il0sWzAsMSwiXFx0ZXh0e1Rlcm19IiwwLHsiY3VydmUiOi0yfV0sWzEsMCwiXFx0ZXh0e2lzU3RydWN0dXJlfSIsMCx7ImN1cnZlIjotMn1dLFsyLDMsIiIsMCx7ImxldmVsIjoxLCJzdHlsZSI6eyJuYW1lIjoiYWRqdW5jdGlvbiJ9fV1d
-- \[\begin{tikzcd}
--  {\text{Sh}(\Sigma)} && {\mathscr{M}}
--  \arrow[""{name=0, anchor=center, inner sep=0}, "{\text{LFTerm}}", curve={height=-12pt}, from=1-1, to=1-3]
--  \arrow[""{name=1, anchor=center, inner sep=0}, "{\text{isStructure}}", curve={height=-12pt}, from=1-3, to=1-1]
--  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=0, to=1]
-- \end{tikzcd}\] $

-- |> Interestingly, nominal sets [fn:: \href{https://ncatlab.org/nlab/show/nominal+set}{See here.}]
--   are also a sheaf category where |Σ = Fin𝐒𝐞𝐭|. But we do not go into
--   this possible extension to sheaves.

----------------------------------------------------
-- ====* Current concept
-- | Instead we define what a /logical framework/ is using the same data
--   and language of adjunctions, but without actually requiring it
--   to be an adjunction. This is useful in our case since we also want
--   to speak about logical frameworks such as the |MetaLFTermCalculus|
--   which do generate cartesian categories but are not the initial
--   among their models.


-- [Definition]
-- | Let |ℳ| and |Σ| be categories. We say that |Σ| is a *logical framework* for |ℳ|,
--   i.e., we define the record type [...] as follows:
record isLogicalFramework (ℳ : Category 𝑖) (Σ : Category 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where

  -- | 1. We require two functions [..] and [..] between them.
  field LFTerm : ⟨ Σ ⟩ -> ⟨ ℳ ⟩
  field LFSig : ⟨ ℳ ⟩ -> ⟨ Σ ⟩

  -- | 2. There should be proofs [..] and [..] that they are actually functors between
  --      the corresponding categories.
  field {{isFunctor:LFTerm}} : LFTerm is (Functor Σ ℳ)
  field {{isFunctor:LFSig}} : LFSig is (Functor ℳ Σ)

  -- | 3. And finally we want a map which shows that every |σ| structure
  --      is a model of |LFTerm Σ|
  field interp : ∀{σ m} -> (Hom σ (LFSig m)) -> (Hom (LFTerm σ) m)

  -- |: We define a |σ| structure on an object |m| as:
  Structure : ⟨ Σ ⟩ -> ⟨ ℳ ⟩ -> 𝒰 _
  Structure σ m = Hom σ (LFSig m)

-- //
open isLogicalFramework {{...}} public





  -- -- - We define the structure 
  -- Structure : Σ -> 𝒰 _
  -- Structure σ = ∑ isStructure σ

  -- instance
  --   StructureCat : ∀ {σ} -> isCategory _ (Structure σ)
  --   StructureCat = isCategory:FullSubcategory (fst)

  -- field LFTerm : (σ : Σ) -> ⟨ ℳ ⟩
  -- field ⟦_⟧ : ∀{σ} -> {A : ⟨ ℳ ⟩} -> isStructure σ A -> (LFTerm σ) ⟶ A
  -- field makeStr : ∀{σ A} -> (LFTerm σ) ⟶ A -> isStructure σ A

  -- field isInitial:LFTerm : ∀{σ} -> isInitial (LFTerm σ)


