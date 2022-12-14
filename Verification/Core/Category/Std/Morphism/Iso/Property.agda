
module Verification.Core.Category.Std.Morphism.Iso.Property where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Setoid.Morphism

open import Verification.Core.Category.Std.Morphism.Iso.Definition

module _ {๐ : Category ๐} {๐ : Category ๐} where

  module _ {F : โจ ๐ โฉ -> โจ ๐ โฉ} {{_ : isFunctor ๐ ๐ F}} where


    cong-โ : โ{a b : โจ ๐ โฉ} -> (a โ b) -> F a โ F b
    cong-โ p = qโ since P
      where
        qโ = map โจ p โฉ
        qโ = map (inverse-โ (of p))

        Pโ : qโ โ qโ โผ id
        Pโ = map โจ p โฉ โ map (inverse-โ (of p))   โจ functoriality-โ โปยน โฉ-โผ
             map (โจ p โฉ โ inverse-โ (of p))       โจ cong-โผ (inv-r-โ (of p)) โฉ-โผ
             map id                               โจ  functoriality-id โฉ-โผ
             id {{of ๐}}                         โ

        Pโ : qโ โ qโ โผ id
        Pโ = map (inverse-โ (of p)) โ map โจ p โฉ   โจ functoriality-โ โปยน โฉ-โผ
             map (inverse-โ (of p) โ โจ p โฉ)       โจ cong-โผ (inv-l-โ (of p)) โฉ-โผ
             map id                               โจ  functoriality-id โฉ-โผ
             id {{of ๐}}                         โ

        P : isIso (hom qโ)
        P = record
            { inverse-โ  = qโ
            ; inv-r-โ    = Pโ
            ; inv-l-โ    = Pโ
            }

    module _ where
      private
        instance
          _ : isSetoid โจ ๐ โฉ
          _ = isSetoid:byCategory

          _ : isSetoid โจ ๐ โฉ
          _ = isSetoid:byCategory

      isSetoidHom:byFunctor : isSetoidHom โฒ โจ ๐ โฉ โฒ โฒ โจ ๐ โฉ โฒ F
      isSetoidHom:byFunctor = record { cong-โผ = cong-โ }

    module _ {{_ : isFull โฒ F โฒ}} {{_ : isFaithful โฒ F โฒ}} where
      congโปยน-โ : โ{a b : โจ ๐ โฉ} -> F a โ F b -> (a โ b)
      congโปยน-โ {a} {b} f = f' since Q
        where
          f' : a โถ b
          f' = surj โจ f โฉ

          g' : b โถ a
          g' = surj (inverse-โ (of f))

          lem-1 : f' โ g' โผ id
          lem-1 = inv-r-โ (of f)
                  >> โจ f โฉ โ inverse-โ (of f) โผ id <<
                  โช (inv-surj โปยน โ inv-surj โปยน) โโผโ refl โซ
                  >> map f' โ map g' โผ id <<
                  โช (functoriality-โ โปยน) โโผโ (functoriality-id โปยน) โซ
                  >> map (f' โ g') โผ map id <<
                  โช cancel-injective โซ


          lem-2 : g' โ f' โผ id
          lem-2 = inv-l-โ (of f)
                  >> inverse-โ (of f) โ โจ f โฉ โผ id <<
                  โช (inv-surj โปยน โ inv-surj โปยน) โโผโ refl โซ
                  >> map g' โ map f' โผ id <<
                  โช (functoriality-โ โปยน) โโผโ (functoriality-id โปยน) โซ
                  >> map (g' โ f') โผ map id <<
                  โช cancel-injective โซ

          Q = record
              { inverse-โ = g'
              ; inv-r-โ   = lem-1
              ; inv-l-โ   = lem-2
              }
  module _ (F : Functor ๐ ๐) where
    congOf-โ : โ{a b : โจ ๐ โฉ} -> (a โ b) -> โจ F โฉ a โ โจ F โฉ b
    congOf-โ = cong-โ


module _ {๐ : Category ๐} where
  switch-โ-r : โ{a b c : โจ ๐ โฉ} -> {f : a โถ b} -> {ฯ : b โ c} -> {g : a โถ c}
                -> (f โ โจ ฯ โฉ โผ g)
                -> f โผ g โ โจ ฯ โฉโปยน
  switch-โ-r {f = f} {ฯ} {g} p =
    f                      โจ unit-r-โ โปยน โฉ-โผ
    f โ id                 โจ refl โ (inv-r-โ (of ฯ)) โปยน โฉ-โผ
    f โ (โจ ฯ โฉ โ โจ ฯ โฉโปยน)  โจ assoc-r-โ โฉ-โผ
    (f โ โจ ฯ โฉ) โ โจ ฯ โฉโปยน  โจ p โ refl โฉ-โผ
    g โ โจ ฯ โฉโปยน            โ

