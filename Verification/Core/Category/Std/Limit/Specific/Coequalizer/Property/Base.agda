
module Verification.Core.Category.Std.Limit.Specific.Coequalizer.Property.Base where

open import Verification.Conventions hiding (_โ_)
open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition

open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor




module _ {๐ : Category ๐} {{_ : hasInitial ๐}} where
  module _ {b : โจ ๐ โฉ} {f g : โฅ โถ b} where

    hasCoequalizer:byInitial : hasCoequalizer f g
    hasCoequalizer:byInitial = b since P
      where
        P : isCoequalizer f g b
        isCoequalizer.ฯโ P    = id
        isCoequalizer.equate-ฯโ P = expand-โฅ โ expand-โฅ โปยน
        isCoequalizer.compute-Coeq P = ฮป h p โ h , unit-l-โ
        isCoequalizer.isEpi:ฯโ P = isEpi:id

module _ {๐ : Category ๐} where
  module _ {a b : โจ ๐ โฉ} {f : a โถ b} where
    hasCoequalizer:byId : hasCoequalizer f f
    hasCoequalizer:byId = b since P
      where
        P : isCoequalizer f f b
        isCoequalizer.ฯโ P    = id
        isCoequalizer.equate-ฯโ P = refl
        isCoequalizer.compute-Coeq P = ฮป h p โ h , unit-l-โ
        isCoequalizer.isEpi:ฯโ P = isEpi:id


  module _ {a b : โจ ๐ โฉ} {f g : a โถ b} where
    hasCoequalizer:bySym : hasCoequalizer f g -> hasCoequalizer g f
    hasCoequalizer:bySym (x since P) = x since Q
      where
        Q : isCoequalizer g f x
        isCoequalizer.ฯโ Q = ฯโ
        isCoequalizer.equate-ฯโ Q = equate-ฯโ โปยน
        isCoequalizer.compute-Coeq Q = ฮป h p โ compute-Coeq h (p โปยน)
        isCoequalizer.isEpi:ฯโ Q = isEpi:ฯโ

  module _ {a b : โจ ๐ โฉ} {f g : a โถ b} where
    hasCoequalizerCandidate:bySym : hasCoequalizerCandidate (f , g) -> hasCoequalizerCandidate (g , f)
    hasCoequalizerCandidate:bySym (x since P) = x since Q
      where
        Q : isCoequalizerCandidate g f x
        isCoequalizerCandidate.ฯโ? Q = ฯโ?
        isCoequalizerCandidate.equate-ฯโ? Q = equate-ฯโ? โปยน

module _ {๐ : Category ๐} where
  module _ {aโ aโ bโ bโ xโ xโ : โจ ๐ โฉ}
           {fโ gโ : aโ โถ bโ} {fโ gโ : aโ โถ bโ}
           {{_ : isCoequalizer fโ gโ xโ}}
           {{_ : isCoequalizer fโ gโ xโ}}
           {{_ : hasCoproducts ๐}}
           where

    private
      fโโ = map-โ (fโ , fโ)
      gโโ = map-โ (gโ , gโ)

    ฯโ-โ : bโ โ bโ โถ xโ โ xโ
    ฯโ-โ = map-โ (ฯโ , ฯโ)

    equate-ฯโ-โ : fโโ โ ฯโ-โ โผ gโโ โ ฯโ-โ
    equate-ฯโ-โ = map-โ (fโ , fโ) โ map-โ (ฯโ , ฯโ)   โจ functoriality-โ {{isFunctor:โ}} โปยน โฉ-โผ
                  map-โ (fโ โ ฯโ , fโ โ ฯโ)           โจ equate-ฯโ โโโโโ equate-ฯโ โฉ-โผ
                  map-โ (gโ โ ฯโ , gโ โ ฯโ)           โจ functoriality-โ {{isFunctor:โ}} โฉ-โผ
                  gโโ โ ฯโ-โ                          โ

    compute-Coeq-โ : โ{y : โจ ๐ โฉ} -> (h : bโ โ bโ โถ y) -> (p : fโโ โ h โผ gโโ โ h) -> โ ฮป (ฮพ : xโ โ xโ โถ y) -> ฯโ-โ โ ฮพ โผ h
    compute-Coeq-โ {y} h p =
      let hโ : bโ โถ y
          hโ = ฮนโ โ h

          hโ : bโ โถ y
          hโ = ฮนโ โ h

          pโ : fโ โ hโ โผ gโ โ hโ
          pโ = p
               >> (fโโ โ h โผ gโโ โ h) <<
               โช (refl โ_) โซ
               >> ฮนโ โ (fโโ โ h) โผ ฮนโ โ (gโโ โ h) <<
               โช assoc-r-โ โโผโ assoc-r-โ โซ
               >> (ฮนโ โ fโโ) โ h โผ (ฮนโ โ gโโ) โ h <<
               โช reduce-ฮนโ โ refl โโผโ reduce-ฮนโ โ refl โซ
               >> (fโ โ ฮนโ) โ h โผ (gโ โ ฮนโ) โ h <<
               โช assoc-l-โ โโผโ assoc-l-โ โซ
               >> fโ โ (ฮนโ โ h) โผ gโ โ (ฮนโ โ h) <<

          pโ : fโ โ hโ โผ gโ โ hโ
          pโ = p
               >> (fโโ โ h โผ gโโ โ h) <<
               โช (refl โ_) โซ
               >> ฮนโ โ (fโโ โ h) โผ ฮนโ โ (gโโ โ h) <<
               โช assoc-r-โ โโผโ assoc-r-โ โซ
               >> (ฮนโ โ fโโ) โ h โผ (ฮนโ โ gโโ) โ h <<
               โช reduce-ฮนโ โ refl โโผโ reduce-ฮนโ โ refl โซ
               >> (fโ โ ฮนโ) โ h โผ (gโ โ ฮนโ) โ h <<
               โช assoc-l-โ โโผโ assoc-l-โ โซ
               >> fโ โ (ฮนโ โ h) โผ gโ โ (ฮนโ โ h) <<

          ฮพ = โฆ โฆ hโ , pโ โฆโ , โฆ hโ , pโ โฆโ โฆ

          lem-1 : ฮนโ โ (ฯโ-โ โ ฮพ) โผ ฮนโ โ h
          lem-1 = ฮนโ โ (ฯโ-โ โ ฮพ)   โจ assoc-r-โ โฉ-โผ
                  ฮนโ โ ฯโ-โ โ ฮพ     โจ reduce-ฮนโ โ refl โฉ-โผ
                  (ฯโ โ ฮนโ) โ ฮพ     โจ assoc-l-โ โฉ-โผ
                  ฯโ โ (ฮนโ โ ฮพ)     โจ refl โ reduce-ฮนโ โฉ-โผ
                  ฯโ โ โฆ hโ , pโ โฆโ โจ reduce-ฯโ โฉ-โผ
                  hโ                โ

          lem-2 : ฮนโ โ (ฯโ-โ โ ฮพ) โผ ฮนโ โ h
          lem-2 = ฮนโ โ (ฯโ-โ โ ฮพ)   โจ assoc-r-โ โฉ-โผ
                  ฮนโ โ ฯโ-โ โ ฮพ     โจ reduce-ฮนโ โ refl โฉ-โผ
                  (ฯโ โ ฮนโ) โ ฮพ     โจ assoc-l-โ โฉ-โผ
                  ฯโ โ (ฮนโ โ ฮพ)     โจ refl โ reduce-ฮนโ โฉ-โผ
                  ฯโ โ โฆ hโ , pโ โฆโ โจ reduce-ฯโ โฉ-โผ
                  hโ                โ

          lem-3 : ฯโ-โ โ ฮพ โผ h
          lem-3 = (lem-1 , lem-2)
                  โช cong-โผ {{isSetoidHom:โฆโฆ}} โซ
                  >> โฆ ฮนโ โ (ฯโ-โ โ ฮพ) , ฮนโ โ (ฯโ-โ โ ฮพ) โฆ โผ โฆ ฮนโ โ h , ฮนโ โ h โฆ <<
                  โช expand-ฮนโ,ฮนโ โปยน โโผโ expand-ฮนโ,ฮนโ โปยน โซ

      in ฮพ , lem-3

    isEpi:ฯโ-โ : isEpi ฯโ-โ
    isEpi:ฯโ-โ = isEpi:map-โ

    isCoequalizer:โ : isCoequalizer (map-โ (fโ , fโ)) (map-โ (gโ , gโ)) (xโ โ xโ)
    isCoequalizer.ฯโ isCoequalizer:โ = ฯโ-โ
    isCoequalizer.equate-ฯโ isCoequalizer:โ = equate-ฯโ-โ
    isCoequalizer.compute-Coeq isCoequalizer:โ = compute-Coeq-โ
    isCoequalizer.isEpi:ฯโ isCoequalizer:โ = isEpi:ฯโ-โ

