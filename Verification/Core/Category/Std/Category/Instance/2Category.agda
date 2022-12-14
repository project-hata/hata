
module Verification.Core.Category.Std.Category.Instance.2Category where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Instance.CategoryLike
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Notation.Associativity





module _ {๐ : Category ๐} {๐ : Category ๐} {โฐ : Category ๐} where

  Comp-๐๐๐ญแต : (Functor ๐ ๐ ร Functor ๐ โฐ) -> Functor ๐ โฐ
  Comp-๐๐๐ญแต = ฮปโ _โ-๐๐๐ญ_

  macro Comp-๐๐๐ญ = #structureOn Comp-๐๐๐ญแต

  map-Comp-๐๐๐ญ : โ{a b} -> (a โถ b) -> Comp-๐๐๐ญ a โถ Comp-๐๐๐ญ b
  map-Comp-๐๐๐ญ {fโ , gโ} {fโ , gโ} (ฮฑ , ฮฒ) = ฮณ since isNatural:ฮณ
    where
      ฮณ : โ(x : โจ ๐ โฉ) -> โจ (fโ โ-๐๐๐ญ gโ) โฉ x โถ โจ (fโ โ-๐๐๐ญ gโ) โฉ x
      ฮณ x = โจ ฮฒ โฉ _ โ map (โจ ฮฑ โฉ _)

      isNatural:ฮณ : isNatural (fโ โ-๐๐๐ญ gโ) (fโ โ-๐๐๐ญ gโ) ฮณ
      isNatural:ฮณ = {!!}

  instance
    isFunctor:Comp-๐๐๐ญ : isFunctor (๐๐ฎ๐ง๐ ๐ ๐ ร-๐๐๐ญ ๐๐ฎ๐ง๐ ๐ โฐ) (๐๐ฎ๐ง๐ ๐ โฐ) Comp-๐๐๐ญ
    isFunctor.map isFunctor:Comp-๐๐๐ญ = map-Comp-๐๐๐ญ
    isFunctor.isSetoidHom:map isFunctor:Comp-๐๐๐ญ = {!!}
    isFunctor.functoriality-id isFunctor:Comp-๐๐๐ญ = {!!}
    isFunctor.functoriality-โ isFunctor:Comp-๐๐๐ญ = {!!}
  infixl 50 _โโโ_
  _โโโ_ : โ{fโ fโ : Functor ๐ ๐} {gโ gโ : Functor ๐ โฐ}
        -> (ฮฑ : Natural fโ fโ) -> (ฮฒ : Natural gโ gโ)
        -> (Natural (fโ โ-๐๐๐ญ gโ) (fโ โ-๐๐๐ญ gโ))
  _โโโ_ ฮฑ ฮฒ = map-Comp-๐๐๐ญ (ฮฑ , ฮฒ)

  -----------------------------------------
  -- properties of โโโ
  --
  -- interchange
  module _ {fโ fโ fโ : Functor ๐ ๐} {gโ gโ gโ : Functor ๐ โฐ}
           (ฮฑ : Natural fโ fโ) (ฮฑ' : Natural fโ fโ)
           (ฮฒ : Natural gโ gโ) (ฮฒ' : Natural gโ gโ) where

    interchange-โโโ : ((ฮฑ โ-๐๐ฎ๐ง๐ ฮฑ') โโโ (ฮฒ โ-๐๐ฎ๐ง๐ ฮฒ')) โผ ((ฮฑ โโโ ฮฒ) โ-๐๐ฎ๐ง๐ (ฮฑ' โโโ ฮฒ'))
    interchange-โโโ = componentwise $ ฮป x ->
                        โจ ฮฒ โ-๐๐ฎ๐ง๐ ฮฒ' โฉ _ โ map (โจ ฮฑ โ-๐๐ฎ๐ง๐ ฮฑ' โฉ _)               โจ refl โฉ-โผ
                        (โจ ฮฒ โฉ _ โ โจ ฮฒ' โฉ _) โ map (โจ ฮฑ โฉ _ โ โจ ฮฑ' โฉ _)           โจ refl โ functoriality-โ โฉ-โผ
                        (โจ ฮฒ โฉ _ โ โจ ฮฒ' โฉ _) โ (map (โจ ฮฑ โฉ _) โ (map (โจ ฮฑ' โฉ _))) โจ assoc-[ab][cd]โผa[bc]d-โ โฉ-โผ
                        โจ ฮฒ โฉ _ โ (โจ ฮฒ' โฉ _ โ map (โจ ฮฑ โฉ _)) โ (map (โจ ฮฑ' โฉ _))   โจ refl โ naturality (โจ ฮฑ โฉ _) โ refl โฉ-โผ
                        โจ ฮฒ โฉ _ โ (map (โจ ฮฑ โฉ _) โ โจ ฮฒ' โฉ _) โ (map (โจ ฮฑ' โฉ _))   โจ assoc-[ab][cd]โผa[bc]d-โ โปยน โฉ-โผ
                        (โจ ฮฒ โฉ _ โ map (โจ ฮฑ โฉ _)) โ (โจ ฮฒ' โฉ _ โ (map (โจ ฮฑ' โฉ _))) โ



  --
  -- setoid compatability
  --
  module _ {fโ fโ : Functor ๐ ๐} {gโ gโ : Functor ๐ โฐ}
           {ฮฑโ ฮฑโ : Natural fโ fโ} {ฮฒโ ฮฒโ : Natural gโ gโ}
         where

    infixl 50 _โโโโโ_
    _โโโโโ_ : ฮฑโ โผ ฮฑโ -> ฮฒโ โผ ฮฒโ -> (ฮฑโ โโโ ฮฒโ โผ ฮฑโ โโโ ฮฒโ)
    _โโโโโ_ p q = componentwise $ ฮป x โ
                โจ ฮฒโ โฉ _ โ (map (โจ ฮฑโ โฉ x))  โจ โจ q โฉ _ โ cong-โผ (โจ p โฉ _) โฉ-โผ
                โจ ฮฒโ โฉ _ โ (map (โจ ฮฑโ โฉ x))  โ

  --
  -- categorical laws
  --
  module _ {fโ : Functor ๐ ๐} {gโ : Functor ๐ โฐ} where
    unit-โโโ : id-๐๐ฎ๐ง๐ {F = fโ} โโโ id-๐๐ฎ๐ง๐ {F = gโ} โผ idOn (fโ โ-๐๐๐ญ gโ)
    unit-โโโ = componentwise $ ฮป x โ
                 let lem-1 : (โจ id-๐๐ฎ๐ง๐ {F = fโ} โโโ id-๐๐ฎ๐ง๐ {F = gโ} โฉ x)
                             โผ
                             (โจ idOn (fโ โ-๐๐๐ญ gโ) โฉ x)
                     lem-1 = unit-l-โ โ functoriality-id
                 in lem-1
  -----------------------------------------
  -- for isos
module _ {๐ : Category ๐} {๐ : Category ๐} {โฐ : Category ๐} where
  module _ {fโ fโ : Functor ๐ ๐} {gโ gโ : Functor ๐ โฐ} where
    _โโโ-๐๐๐ญ_ : (ฮฑ : fโ โผ fโ) -> (ฮฒ : gโ โผ gโ)
              -> ((fโ โ-๐๐๐ญ gโ) โผ (fโ โ-๐๐๐ญ gโ))
    _โโโ-๐๐๐ญ_ ฮฑ ฮฒ = (โจ ฮฑ โฉ โโโ โจ ฮฒ โฉ) since P
      where
        ฮฑฮฒโปยน : (fโ โ-๐๐๐ญ gโ) โถ (fโ โ-๐๐๐ญ gโ)
        ฮฑฮฒโปยน = โจ ฮฑ โฉโปยน โโโ โจ ฮฒ โฉโปยน

        lem-1 : (โจ ฮฑ โฉ โโโ โจ ฮฒ โฉ) โ (โจ ฮฑ โฉโปยน โโโ โจ ฮฒ โฉโปยน) โผ id
        lem-1 = (โจ ฮฑ โฉ โโโ โจ ฮฒ โฉ) โ (โจ ฮฑ โฉโปยน โโโ โจ ฮฒ โฉโปยน)             โจ interchange-โโโ โจ ฮฑ โฉ โจ ฮฑ โฉโปยน โจ ฮฒ โฉ โจ ฮฒ โฉโปยน โปยน โฉ-โผ
                (โจ ฮฑ โฉ โ-๐๐ฎ๐ง๐ โจ ฮฑ โฉโปยน) โโโ (โจ ฮฒ โฉ โ-๐๐ฎ๐ง๐ โจ ฮฒ โฉโปยน)     โจ _โโโโโ_ (inv-r-โ (of ฮฑ)) (inv-r-โ (of ฮฒ)) โฉ-โผ
                id-๐๐ฎ๐ง๐ {F = fโ} โโโ id-๐๐ฎ๐ง๐ {F = gโ}                 โจ unit-โโโ {fโ = fโ} {gโ = gโ} โฉ-โผ
                id-๐๐ฎ๐ง๐ {F = fโ โ-๐๐๐ญ gโ}                             โ

        lem-2 : (โจ ฮฑ โฉโปยน โโโ โจ ฮฒ โฉโปยน) โ (โจ ฮฑ โฉ โโโ โจ ฮฒ โฉ) โผ id
        lem-2 = (โจ ฮฑ โฉโปยน โโโ โจ ฮฒ โฉโปยน) โ (โจ ฮฑ โฉ โโโ โจ ฮฒ โฉ)                โจ interchange-โโโ โจ ฮฑ โฉโปยน โจ ฮฑ โฉ โจ ฮฒ โฉโปยน โจ ฮฒ โฉ โปยน โฉ-โผ
                (โจ ฮฑ โฉโปยน โ-๐๐ฎ๐ง๐ โจ ฮฑ โฉ) โโโ (โจ ฮฒ โฉโปยน โ-๐๐ฎ๐ง๐ โจ ฮฒ โฉ)        โจ _โโโโโ_ (inv-l-โ (of ฮฑ)) (inv-l-โ (of ฮฒ)) โฉ-โผ
                id-๐๐ฎ๐ง๐ {F = fโ} โโโ id-๐๐ฎ๐ง๐ {F = gโ}                 โจ unit-โโโ {fโ = fโ} {gโ = gโ} โฉ-โผ
                id-๐๐ฎ๐ง๐ {F = fโ โ-๐๐๐ญ gโ}                             โ

        P = record { inverse-โ = ฮฑฮฒโปยน ; inv-r-โ = lem-1 ; inv-l-โ = lem-2 }




