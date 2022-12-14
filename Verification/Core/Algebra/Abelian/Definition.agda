
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Core.Algebra.Abelian.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient


Abelian : (๐ : ๐ ^ 2) -> ๐ฐ _
Abelian ๐ = Monoid ๐ :& (isGroup :, isCommutative)

-- Subabelian : (A : Abelian ๐) -> ๐ฐ _
-- Subabelian A = Subgroup โฒ โจ A โฉ โฒ

-- record isSubabelian {A} {{_ : Abelian ๐ on A}} (P : ๐ซ-๐ฐ A :& isSubsetoid :& isSubmonoid :& isSubgroup) : ๐ฐ ๐ where
record isSubabelian {๐ : ๐ ^ 2} {A : Abelian ๐} (P : ๐ซ-๐ฐ โจ A โฉ :& isSubsetoid :& isSubmonoid :& isSubgroup) : ๐ฐ ๐ where
open isSubabelian {{...}} public


Subabelian : {๐ : ๐ ^ 2} (A : Abelian ๐) -> ๐ฐ _
Subabelian A = Subgroup โฒ โจ A โฉ โฒ :& isSubabelian {A = A}


-- module _ {A : Abelian ๐} where
--   RelSubabelian : Subabelian A -> โจ A โฉ -> โจ A โฉ -> ๐ฐ _
--   RelSubabelian B = RelSubgroup โฒ โจ B โฉ โฒ

-- RelSubabelian : {A : Abelian ๐} (B : Subabelian A) -> 

-- module _ {A : ๐ฐ _} {B : ๐ซ A} {{_ : Abelian ๐ on A}} {{_ : Subgroup โฒ A โฒ on B}} where

--   instance
--     isNormal:Subabelian : isNormal โฒ B โฒ
--     isNormal.normal isNormal:Subabelian a {b} bโB =
--       let Pโ = b             โฃโจ unit-r-โ โปยน โฉ
--                 b โ โ         โฃโจ refl โโโ inv-r-โ โปยน โฉ
--                 b โ (a โ โก a) โฃโจ assoc-r-โ โฉ
--                 b โ a โ โก a   โฃโจ comm-โ โโโ refl โฉ
--                 a โ b โ โก a   โ

--           Pโ : B (a โ b โ โก a)
--           Pโ = transp-โผ Pโ bโB
--       in Pโ

-- private
module _ {๐ : ๐ ^ 2} {A : Group ๐} {B : Subgroup A} {{_ : isCommutative โฒ โจ A โฉ โฒ}} where
  instance
    isNormal:Subabelian : isNormal โฒ โจ B โฉ โฒ
    isNormal.normal isNormal:Subabelian a {b} bโB =
      let Pโ = b             โฃโจ unit-r-โ โปยน โฉ
                b โ โ         โฃโจ refl โโโ inv-r-โ โปยน โฉ
                b โ (a โ โก a) โฃโจ assoc-r-โ โฉ
                b โ a โ โก a   โฃโจ comm-โ โโโ refl โฉ
                a โ b โ โก a   โ

          Pโ : โจ โจ B โฉ (a โ b โ โก a) โฉ
          Pโ = transp-โผ Pโ bโB
      in Pโ

-- module _ {A : Abelian ๐} {B : Subabelian A} where
-- module _ {A : ๐ฐ _} {B : ๐ซ A} {{_ : Abelian ๐ on A}} {{_ : Subabelian โฒ A โฒ on B}} where
-- module _ {A : Abelian ๐} {B : Subgroup โฒ โจ A โฉ โฒ} where
module _ {๐ : ๐ ^ 2} {A : Group ๐} {{_ : isCommutative โฒ โจ A โฉ โฒ}} {B : Subgroup A} where

  instance
    isCommutative:AbelianQuot : isCommutative (โฒ โจ โฒ โจ A โฉ โฒ /-Group โฒ โจ B โฉ โฒ โฉ โฒ)
    -- isCommutative:AbelianQuot = {!!}
    isCommutative.comm-โ isCommutative:AbelianQuot {a = [ a ]} {b = [ b ]} = cong-โผ comm-โ

  -- _/-Abelian_ : Abelian _
  -- _/-Abelian_ = โฒ โจ โฒ A โฒ /-Group โฒ B โฒ โฉ โฒ

-- RelSubabelian : {G : Abelian ๐} (H : Subabelian G) (a : โจ G โฉ) (b : โจ G โฉ) : ๐ฐ (๐ โ 0) where

_/-Abelian_ : {๐ : ๐ ^ 2} (A : Abelian ๐) -> (B : Subabelian A) -> Abelian _
-- _/-Abelian_ A B = โฒ โจ โฒ โจ A โฉ โฒ /-Group โฒ โจ B โฉ โฒ โฉ โฒ
_/-Abelian_ A B = โฒ โจ A โฉ /-๐ฐ RelSubgroup โฒ โจ B โฉ โฒ โฒ

  -- let XX : isCommutative โฒ โจ A โฉ โฒ
  --     XX = it
  --     YY = โจ A โฉ /-๐ฐ RelSubgroup โฒ โจ B โฉ โฒ
  --     -- YY1 : Monoid _ on YY
  --     -- YY1 = makeโi {_} {{isMonoid:GroupQuot {G = โฒ โจ A โฉ โฒ} {{isNormal:Subabelian {A = A}}}}}
  -- in โฒ YY โฒ

-- _/-Abelian_ A B = โฒ โจ A โฉ /-๐ฐ RelSubgroup โฒ โจ B โฉ โฒ โฒ


-- โฒ โจ โฒ โจ A โฉ โฒ /-Group B โฉ โฒ

{-
  -}
{-
  -- testaa : (a b : โจ โฒ โจ A โฉ โฒ /-Group B โฉ) -> ๐-๐ฐ
  -- testaa a b =
  --   let x = a โ b
  --   in {!!}

  -- instance
  --   open _:&_ (โฒ โจ A โฉ โฒ /-Group B)



-}

