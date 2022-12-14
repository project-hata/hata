
module Verification.Core.Category.Std.Limit.Specific.Coequalizer.Definition where

open import Verification.Conventions
open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono

-- [Hide]
module _ {π : π° π} {{_ : isCategory {π} π}} where
  LiftU : (π -> π° π) -> (Obj β² π β² -> π° π)
  LiftU P o = P β¨ o β©

-- //

-- [Definition]
-- | Let [..] [] be a category.
module _ {π : π° π} {{_ : isCategory {π} π}} where
  private variable a b : π

  -- | A coequalizer |Οβ| of a pair of parallel arrows in |π|,
  --   is defined by the following type:
  record isCoequalizer (f g : a βΆ b) (x : π) : π° (π ο½€ π) where
    -- | It is given by the following data:
    -- | - A map [..].
    field Οβ : b βΆ x
    -- | - Such that |f| and |g| become equal when
    --    post composed with |Οβ|.
          equate-Οβ : f β Οβ βΌ g β Οβ
    -- | - Furthermore, any other arrow which has the same property has to factor through |Οβ|.
          compute-Coeq : β{c : π} -> (h : b βΆ c) -> (p : f β h βΌ g β h) -> β Ξ» (ΞΎ : x βΆ c) -> Οβ β ΞΎ βΌ h
    -- | - Finally, |Οβ| needs to be an epimorphism.
          {{isEpi:Οβ}} : isEpi Οβ

  -- //

  -- [Hide]


    β¦_β¦β : β{c : π} -> (β Ξ» (h : b βΆ c) -> (f β h βΌ g β h)) -> x βΆ c
    β¦_β¦β (h , p) = fst (compute-Coeq h p)
    reduce-Οβ : β{c : π} -> {h : b βΆ c} -> {p : f β h βΌ g β h} -> Οβ β β¦ h , p β¦β βΌ h
    reduce-Οβ {h = h} {p} = snd (compute-Coeq h p)

  open isCoequalizer {{...}} public

  hasCoequalizer : {a b : π} (f g : a βΆ b) -> π° _
  hasCoequalizer f g = _ :& LiftU (isCoequalizer f g)


  ----------------------------------------------------------
  -- Coequalizer without uniqueness
  record isCoequalizerCandidate {a b : π} (f g : a βΆ b) (x : π) : π° (π ο½€ π) where
    field Οβ? : b βΆ x
          equate-Οβ? : f β Οβ? βΌ g β Οβ?

  open isCoequalizerCandidate {{...}} public

  hasCoequalizerCandidate : {a b : π} (f : HomPair a b) -> π° _
  hasCoequalizerCandidate (f , g) = _ :& LiftU (isCoequalizerCandidate f g)


record hasCoequalizers (π : Category π) : π° π where
  field Coeq : β{a b : β¨ π β©} (f g : a βΆ b) -> β¨ π β©
  field {{isCoequalizer:Coeq}} : β{a b : β¨ π β©} {f g : a βΆ b} -> isCoequalizer f g (Coeq f g)

open hasCoequalizers {{...}} public
-- //
