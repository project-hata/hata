
module Verification.Core.Theory.Std.Generic.ComputationalTheory.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Category.Std.Graph.Definition
open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
-- open import Verification.Core.Data.Sum.Definition
-- open import Verification.Core.Data.Rational.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Computation.Question.Construction.Product
open import Verification.Core.Theory.Std.Generic.Theory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full


--------------------------------------------------------------------

-- record Repr (A : Setoid π) (P : β¨ A β© -> π° π) (a : β¨ A β©) : π° (π ο½€ π) where
--   constructor mkrepr
--   field β¨_β© : β¨ A β©
--   field represents : a βΌ β¨_β©
--   field hasProperty : P β¨_β©
-- open Repr public

-- record hasRepr (A : Setoid π) (P : β¨ A β© -> π° π) : π° (π ο½€ π) where
--   field repr : β(a : β¨ A β©) -> Repr A P a
-- open hasRepr public

--------------------------------------------------------------------
-- theory with computational interpretation

-- private macro
--   U = instance[ "forget" , π ] (Category π -> π° _) β

{-
arg1-syntax : β{A : π° π} {B : A -> π° π} -> ((a : A) -> B a) -> {a : A} -> B a
arg1-syntax f {a} = f a

syntax arg1-syntax (Ξ» a -> f) = arg1 a βΆ f

    isGraph:CompTerm = arg1 c βΆ (of CompTermα΅ c)
  testttt = arg1 c βΆ (of CompTermα΅ c)
-}

  -- field CompTermα΅ : π -> π° (π β 0)
  -- field {{isGraph:CompTerm}} : β {c} -> isGraph {π β 1} (CompTermα΅ c)

record isComputational {π : π ^ 2} {π} (π : π° π) : π° (π βΊ ο½€ π βΊ) where
  constructor computational
  field CompTermα΅ : (c : π) -> π° (π β 0)
  field {{isGraph:CompTerm}} : β{c} -> isGraph {π β 1} (CompTermα΅ c)

  -------
  -- usual overloading of notation
  macro
    CompTerm : β(c) -> SomeStructure
    CompTerm (c) = #structureOn (CompTermα΅ c)

open isComputational {{...}} public

Computational : (π : π ^ 3) -> π° _
Computational π = π° (π β 0) :& isComputational {π β 1 , π β 2}


private macro
  πΊπ = instance[ "" , π ] (Graph π -> Setoid _) β

ComputationalβTheory : Computational π -> Theory _
ComputationalβTheory π = β¨ π β© since theory (Ξ» Ξ³ -> β¨ πΊπ (CompTerm Ξ³) β©)

instance
  Register:ComputationalβTheory = registerβ[ "" , π ] (ComputationalβTheory {π})

-- instance
--   Register:ForgetTypeTheory = registerΟ[ "" , π ] (ForgetTT {π})


-- {{Ξ» {c} -> of S β² CompTerm c β²}}


-- Computational : (π : π ^ 5) -> π° _
-- Computational π = Theory (π β 0 , π β 1 , π β 2) :& isComputational (π β 3 , π β 4)





{-
record isComputational (π : π ^ 2) (π£ : Theory π) : π° (π βΊ ο½€ π βΊ) where
  constructor computational
  field isNormal : β{Ο : β¨ π£ β©} -> β¨ Ο β  β© -> π° (π β 0)

  _β N : β¨ π£ β© -> π° _
  _β N Ο = β Ξ» (p : β¨ Ο β  β©) -> isNormal p

  field normalize : β (Ο : β¨ π£ β©) -> hasRepr (Ο β ) isNormal
  field isCanonical : β¨ π£ β© -> π° (π β 1)
  Canonical : π° _
  Canonical = β isCanonical
  field _β_ : Canonical -> Canonical -> β¨ π£ β©
  infix 100 _β_
  field run : β{a b : Canonical} -> β¨ (a β b) β  β© -> a .fst β N -> b .fst β N
  normalize' : β {Ο : β¨ π£ β©} -> β¨ Ο β  β© -> Ο β N
  normalize' = {!!}

  -- field can : Canonical -> β¨ π£ β©


-- maps between computational theories
record isComputationalHom (π : Computational π) (π : Computational π) (F : TheoryHom β² β¨ π β© β² β² β¨ π β© β²) : π° (π ο½€ π) where
  constructor computationalHom
  field isNormal-β N : β(Ο : β¨ π β©) -> (t : Ο β N) -> isNormal (β¨ map-β  {{of F}} Ο β© (t .fst))

  map-β N : β(Ο : β¨ π β©) -> Ο β N -> β¨ β¨ F β© Ο β  β©
  map-β N Ο t = (β¨ map-β  {{of F}} Ο β© (t .fst))
  -- , isNormal-β N _ t

  field canonical : β{Ο : β¨ π β©} -> isCanonical Ο -> isCanonical (β¨ F β© Ο) -> isIso-π° (map-β N Ο)



record Meta π : π° (π βΊ) where
  constructor meta
  field fst : π° π
  field snd : π° π

macro
  π π²ππ? : β π -> SomeStructure
  π π²ππ? π = #structureOn (Meta π)

-- π π²ππ?
-- β³β―ππΆ
-- πππ

instance
  isTheory:π π²ππ? : isTheory _ (π π²ππ? π)
  isTheory:π π²ππ? = theory Ξ» (meta a b) β (a βΆ b) since isSetoid:Hom


instance
  isComputational:π π²ππ? : isComputational _ (π π²ππ? π)
  isComputational:π π²ππ? = computational (const π-π°) R (const π-π°) (Ξ» (A , _) (B , _) β {!!}) {!!}
    where R = {!!}



-}


