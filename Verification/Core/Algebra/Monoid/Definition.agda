
module Verification.Core.Algebra.Monoid.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Prop.Definition


-- #Notation/Rewrite# โ = \Circle

-- [Definition]
-- | A setoid |A| is a /monoid/, that is, the type [..] is inhabited,
--   if the following data is given.
record isMonoid {๐ : ๐ ^ 2} (A : Setoid ๐) : ๐ฐ (๐) where

  -- | 1. A binary operation [..].
  field _โ_ : โจ A โฉ -> โจ A โฉ -> โจ A โฉ

  -- | 2. A specified element [..].
        โ : โจ A โฉ

  -- | 3. Proofs that |โ| is associative,
  --      and |โ| is a unit for it.
        unit-l-โ   : โ {a} -> โ โ a โผ a
        unit-r-โ   : โ {a} -> a โ โ โผ a
        assoc-l-โ  : โ {a b c} -> (a โ b) โ c โผ a โ (b โ c)

  -- | 4. Finally, a proof that the operation is compatible
  --      with the equivalence relation.
        _โโโ_ : โ{aโ aโ bโ bโ} -> aโ โผ aโ -> bโ โผ bโ -> aโ โ bโ โผ aโ โ bโ

  -- | We further write [] [..].
  assoc-r-โ : โ{a b c} -> a โ (b โ c) โผ (a โ b) โ c
  assoc-r-โ = assoc-l-โ โปยน

  infixl 50 _โ_ _โโโ_
open isMonoid {{...}} public

-- //

-- [Hide]

Monoid : (๐ : ๐ ^ 2) -> ๐ฐ _
Monoid ๐ = Setoid ๐ :& isMonoid

module _ {A : ๐ฐ _} {{Ap : A is Monoid ๐}} where
  macro
   โโจ : SomeStructure
   โโจ = #structureOn (ฮปโ {A = A} {B = A} {C = A} (_โ_))


record isCommutative {๐ : ๐ ^ 2} (A : Monoid ๐) : ๐ฐ ๐ where
  field comm-โ : โ{a b : โจ A โฉ} -> a โ b โผ b โ a

open isCommutative {{...}} public


record isSubmonoid {๐ : ๐ ^ 2} {A} {{_ : Monoid ๐ on A}} (P : ๐ซ A :& isSubsetoid) : ๐ฐ ๐ where
  field closed-โ : โ โ P
        closed-โ : โ{a b : A} -> a โ P -> b โ P -> (a โ b) โ P
        --โจ โจ P โฉ a โฉ -> โจ โจ P โฉ b โฉ -> โจ โจ P โฉ (a โ b) โฉ
open isSubmonoid {{...}} public


Submonoid : (M : Monoid ๐) -> ๐ฐ _
Submonoid M = _ :& isSubmonoid {A = โจ M โฉ}

module _ (A : Monoid ๐) (B : Monoid ๐) where
  record isMonoidHom (f : SetoidHom โฒ โจ A โฉ โฒ โฒ โจ B โฉ โฒ) : ๐ฐ (๐ ๏ฝค ๐) where
    field pres-โ : โจ f โฉ โ โผ โ
    field pres-โ : โ{a b : โจ A โฉ} -> โจ f โฉ (a โ b) โผ โจ f โฉ a โ โจ f โฉ b

  MonoidHom : ๐ฐ _
  MonoidHom = _ :& isMonoidHom

open isMonoidHom {{...}} public

module _ {A : Monoid ๐} {B : Monoid ๐} where

  instance
    isSetoid:MonoidHom : isSetoid (MonoidHom A B)
    isSetoid:MonoidHom = isSetoid:FullSubsetoid (_ since isSetoid:SetoidHom) (ฮป f -> โณ f)

-- //



