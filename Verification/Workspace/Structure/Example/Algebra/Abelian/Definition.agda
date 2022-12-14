
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Workspace.Structure.Example.Algebra.Abelian.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Setoid.Definition
open import Verification.Workspace.Structure.Example.Algebra.Monoid.Definition
open import Verification.Workspace.Structure.Example.Algebra.Group.Definition
-- open import Verification.Core.Algebra.Group.Quotient

open import Verification.Workspace.Structure.Definition2


Abelian' : (๐ : ๐ ^ 2) -> ๐ฐ _
Abelian' ๐ = Monoid' ๐ :&' (isGroup :,' isCommutative)

{-

-- record isSubabelian {๐ : ๐ ^ 2} {A : Abelian ๐} (P : ๐ซ-๐ฐ โจ A โฉ :& isSubsetoid :& isSubmonoid :& isSubgroup) : ๐ฐ ๐ where
-- open isSubabelian {{...}} public


-- Subabelian : {๐ : ๐ ^ 2} (A : Abelian ๐) -> ๐ฐ _
-- Subabelian A = Subgroup โฒ โจ A โฉ โฒ :& isSubabelian {A = A}


-- module _ {๐ : ๐ ^ 2} {A : Group ๐} {B : Subgroup A} {{_ : isCommutative โฒ โจ A โฉ โฒ}} where
--   instance
--     isNormal:Subabelian : isNormal โฒ โจ B โฉ โฒ
--     isNormal.normal isNormal:Subabelian a {b} bโB =
--       let Pโ = b             โฃโจ unit-r-โ โปยน โฉ
--                 b โ โ         โฃโจ refl โโโ inv-r-โ โปยน โฉ
--                 b โ (a โ โก a) โฃโจ assoc-r-โ โฉ
--                 b โ a โ โก a   โฃโจ comm-โ โโโ refl โฉ
--                 a โ b โ โก a   โ

--           Pโ : โจ โจ B โฉ (a โ b โ โก a) โฉ
--           Pโ = transp-โผ Pโ bโB
--       in Pโ

{-
module _ {๐ : ๐ ^ 2} {A : Group ๐} {{_ : isCommutative โฒ โจ A โฉ โฒ}} {B : Subgroup A} where

  instance
    isCommutative:AbelianQuot : isCommutative (โฒ โจ โฒ โจ A โฉ โฒ /-Group โฒ โจ B โฉ โฒ โฉ โฒ)
    isCommutative.comm-โ isCommutative:AbelianQuot {a = [ a ]} {b = [ b ]} = cong-โผ comm-โ


_/-Abelian_ : {๐ : ๐ ^ 2} (A : Abelian ๐) -> (B : Subabelian A) -> Abelian _
_/-Abelian_ A B = โฒ โจ A โฉ /-๐ฐ RelSubgroup โฒ โจ B โฉ โฒ โฒ

-}
-}
