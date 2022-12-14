
module Verification.Core.Data.Prop.Definition where

open import Verification.Core.Conventions

record Prop (๐ : ๐) : ๐ฐ (๐ โบ) where
  -- no-eta-equality
  constructor โฃ_โฃ-Prop
  field โจ_โฉ : ๐ฐ ๐
open Prop public

instance
  Notation-Absolute:Prop : Notation-Absolute (๐ฐ ๐) (Prop ๐)
  Notation-Absolute.โฃ_โฃ Notation-Absolute:Prop = โฃ_โฃ-Prop


๐ซ-๐ฐ : ๐ฐ ๐ -> ๐ฐ (๐ โบ)
๐ซ-๐ฐ {๐} A = A -> Prop ๐

-------------------------
-- notation for ๐ซ


record hasPower (A : ๐ฐ ๐) (B : ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
  field ๐ซแต : A -> B

open hasPower {{...}} public

instance
  hasPower:๐ฐ : hasPower (๐ฐ ๐) (๐ฐ (๐ โบ))
  hasPower:๐ฐ = record { ๐ซแต = ๐ซ-๐ฐ }

module _ {A : ๐ฐ ๐} {B : ๐ฐ ๐} {{_ : hasPower A B}} (a : A) where
  macro
    ๐ซ = #structureOn (๐ซแต a)



---------------------------------------------------------------
-- finitary Operators

infix 40 _โ_ _โ_

_โ_ : {A : ๐ฐ ๐} -> (a : A) -> {U : ๐ฐ ๐} -> (u : U) -> {{UU : hasU U (๐ โบ โ ๐) ๐}} -> {{_ : getU UU โก-Str (A -> Prop ๐)}} -> ๐ฐ ๐
_โ_ a u {{UU}} {{p}} with destructEl UU u | p
... | f | refl-StrId = โจ f a โฉ

_โ_ : {A : ๐ฐ ๐} ->
      {U : ๐ฐ ๐โ} -> (u : U) -> {{UU : hasU U (๐โ โบ โ ๐) ๐}} -> {{_ : getU UU โก-Str (A -> Prop ๐โ)}}
      {V : ๐ฐ ๐โ} -> (v : V) -> {{VV : hasU V (๐โ โบ โ ๐) ๐}} -> {{_ : getU VV โก-Str (A -> Prop ๐โ)}}
      -> ๐ฐ (๐โ ๏ฝค ๐โ ๏ฝค ๐)
_โ_ {A = A} u {{UU}} {{p}} v {{VV}} {{q}} with destructEl UU u | p | destructEl VV v | q
... | f | refl-StrId | g | refl-StrId = โ{a : A} -> โจ f a โฉ -> โจ g a โฉ


module _ {A : ๐ฐ ๐}
      {U : ๐ฐ ๐โ}  (u : U)  {{UU : hasU U (๐โ โบ โ ๐) ๐}}  {{_ : getU UU โก-Str (A -> Prop ๐โ)}}
      {V : ๐ฐ ๐โ}  (v : V)  {{VV : hasU V (๐โ โบ โ ๐) ๐}}  {{_ : getU VV โก-Str (A -> Prop ๐โ)}}
      where

  infixr 60 _โฉ_ _โช_ _โฉแต_ _โชแต_

  _โชแต_ : A -> Prop (๐โ ๏ฝค ๐โ)
  _โชแต_ a = โฃ a โ u +-๐ฐ a โ v โฃ

  _โฉแต_ : A -> Prop (๐โ ๏ฝค ๐โ)
  _โฉแต_ a = โฃ a โ u ร-๐ฐ a โ v โฃ

  macro _โช_ = #structureOn _โชแต_
  macro _โฉ_ = #structureOn _โฉแต_

module _ {A : ๐ฐ ๐} where
  module _ {๐} where
    โแต : A -> Prop ๐
    โแต a = โฃ โฅ-๐ฐ โฃ

    โงแต : A -> Prop ๐
    โงแต a = โฃ โค-๐ฐ โฃ

    macro โ = #structureOn โแต
    macro โง = #structureOn โงแต

---------------------------------------------------------------
-- indexed Operators

module _ {A : ๐ฐ ๐} {I : ๐ฐ ๐โ}
      {U : ๐ฐ ๐โ}  {{UU : hasU U (๐โ โบ โ ๐) ๐}}  {{_ : getU UU โก-Str (A -> Prop ๐โ)}} (uแตข : I -> U)
      where

  โแต : A -> Prop _
  โแต a = โฃ (โ (i : I) -> a โ uแตข i) โฃ

  โแต : A -> Prop _
  โแต a = โฃ โ (ฮป (i : I) -> a โ uแตข i) โฃ

  macro โ = #structureOn โแต
  macro โ = #structureOn โแต



---------------------------------------------------------------
-- Existence

record โฆ_โฆ {U : ๐ฐ ๐} (P : U -> Prop ๐) : ๐ฐ (๐ โ ๐) where
  constructor _โข_
  field โจ_โฉ : U
  field Proof : Prop.โจ_โฉ (P โจ_โฉ)
open โฆ_โฆ public

infix 60 _โข_


infix 1 exists

exists : โ{A : ๐ฐ โ} -> (B : A -> ๐ฐ โ') -> Prop (โ โ โ')
exists B = โฃ โ B โฃ

syntax exists (ฮป x -> F) = โ x , F

-- module _  where
existsIn : {A : ๐ฐ ๐} {U : ๐ฐ ๐} -> (u : U) -> {{UU : hasU U (๐ โบ โ ๐) ๐}} {{_ : getU UU โก-Str (A -> Prop ๐)}} -> (C : A -> ๐ฐ ๐โ) -> Prop (๐ ๏ฝค ๐ ๏ฝค ๐โ)
existsIn u C = โฃ โ (ฮป a -> (a โ u) ร-๐ฐ C a) โฃ

syntax existsIn U (ฮป x -> F) = โ x โ U , F


