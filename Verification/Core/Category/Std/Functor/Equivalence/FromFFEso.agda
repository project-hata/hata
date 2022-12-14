
module Verification.Core.Category.Std.Functor.Equivalence.FromFFEso where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Setoid.Morphism
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Equivalence.Definition

module _ {๐ : Category ๐} {๐ : Category ๐} where
  module _ {F : Functor ๐ ๐} {{_ : isFull F}} {{_ : isFaithful F}} {{EsoP : isEssentiallySurjective F}} where
    private
      map-eso : โ{a b : โจ ๐ โฉ} -> a โถ b -> eso a โถ eso b
      map-eso {a} {b} f =
        let f' : โจ F โฉ (eso a) โถ โจ F โฉ (eso b)
            f' = โจ inv-eso โฉ โ f โ โจ inv-eso โฉโปยน
        in surj f'

      lem-0 : โ{a b : โจ ๐ โฉ} -> {f g : a โถ b} -> (f โผ g) -> map-eso f โผ map-eso g
      lem-0 p = cong-โผ {{isSetoidHom:surj}} ((refl โ p โ refl))

      lem-1 : โ{a b : โจ ๐ โฉ} -> isSetoidHom (a โถ b) (eso a โถ eso b) map-eso
      lem-1 {a} {b} = record { cong-โผ = lem-0 }

      lem-2 : โ{a : โจ ๐ โฉ} -> map-eso (id {a = a}) โผ id
      lem-2 = cancel-injective lem-2a
        where
          lem-2a : โ{a : โจ ๐ โฉ} -> mapOf F (map-eso (id {a = a})) โผ mapOf F id
          lem-2a {a} =
            mapOf F (surj (โจ inv-eso โฉ โ (id {a = a}) โ โจ inv-eso โฉโปยน))
            โจ inv-surj โฉ-โผ
            โจ inv-eso โฉ โ (id {a = a}) โ โจ inv-eso โฉโปยน
            โจ unit-r-โ โ refl โฉ-โผ
            โจ inv-eso โฉ โ โจ inv-eso โฉโปยน
            โจ inv-r-โ (of inv-eso) โฉ-โผ
            id {a = โจ F โฉ (eso a)}
            โจ functoriality-id โปยน โฉ-โผ
            mapOf F id
            โ

      lem-3 : โ{a b c : โจ ๐ โฉ} -> {f : a โถ b} {g : b โถ c} -> map-eso (f โ g) โผ map-eso f โ map-eso g
      lem-3 {a} {b} {c} {f} {g} = cancel-injective lem-3a
        where
          lem-3a : mapOf F (map-eso (f โ g)) โผ mapOf F (map-eso f โ map-eso g)
          lem-3a = map (surj (โจ inv-eso โฉ โ (f โ g) โ โจ inv-eso โฉโปยน))

                      โจ inv-surj โฉ-โผ

                    (โจ inv-eso โฉ โ (f โ g) โ โจ inv-eso โฉโปยน)

                      โจ assoc-[ab][cd]โผa[bc]d-โ โปยน โฉ-โผ

                    โจ inv-eso โฉ โ f โ (g โ โจ inv-eso โฉโปยน)

                      โจ refl โ refl โ unit-l-โ โปยน โฉ-โผ

                    โจ inv-eso โฉ โ f โ (id โ (g โ โจ inv-eso โฉโปยน))

                      โจ refl โ refl โ (inv-l-โ (of inv-eso) โปยน  โ refl) โฉ-โผ

                    โจ inv-eso โฉ โ f โ ((โจ inv-eso โฉโปยน โ โจ inv-eso โฉ) โ (g โ โจ inv-eso โฉโปยน))

                      โจ refl โ refl โ (assoc-l-โ) โฉ-โผ

                    โจ inv-eso โฉ โ f โ (โจ inv-eso โฉโปยน โ (โจ inv-eso โฉ โ (g โ โจ inv-eso โฉโปยน)))

                      โจ refl โ refl โ (refl โ (assoc-r-โ)) โฉ-โผ

                    โจ inv-eso โฉ โ f โ (โจ inv-eso โฉโปยน โ (โจ inv-eso โฉ โ g โ โจ inv-eso โฉโปยน))

                      โจ assoc-r-โ โฉ-โผ

                    (โจ inv-eso โฉ โ f โ โจ inv-eso โฉโปยน) โ (โจ inv-eso โฉ โ g โ โจ inv-eso โฉโปยน)

                      โจ inv-surj โปยน โ inv-surj โปยน โฉ-โผ

                    map (surj (โจ inv-eso โฉ โ f โ โจ inv-eso โฉโปยน)) โ map (surj (โจ inv-eso โฉ โ g โ โจ inv-eso โฉโปยน))

                      โจ functoriality-โ โปยน โฉ-โผ

                    map ((surj (โจ inv-eso โฉ โ f โ โจ inv-eso โฉโปยน)) โ surj (โจ inv-eso โฉ โ g โ โจ inv-eso โฉโปยน))

                      โ


      instance
        lem-5 : isFunctor ๐ ๐ eso
        isFunctor.map lem-5 = map-eso
        isFunctor.isSetoidHom:map lem-5 = lem-1
        isFunctor.functoriality-id lem-5 = lem-2
        isFunctor.functoriality-โ lem-5 = lem-3

      lem-6 : F โ-๐๐๐ญ โฒ eso โฒ โผ id
      lem-6 = ฮฑ since Proof
        where

          ฯ : โ{x} -> โจ F โฉ (eso (โจ F โฉ x)) โ โจ F โฉ x
          ฯ = inv-eso

          ฯ : โ{x} -> eso (โจ F โฉ x) โ x
          ฯ = congโปยน-โ ฯ

          ฮฑ : Natural (F โ-๐๐๐ญ โฒ eso โฒ) id
          ฮฑ = (ฮป x -> โจ ฯ โฉ) since natural ฮป f -> cancel-injective (P f)
            where
              P : โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> map (โจ ฯ โฉ โ f) โผ map (mapOf (F โ-๐๐๐ญ โฒ eso โฒ) f โ โจ ฯ โฉ)
              P f = map (โจ ฯ โฉ โ f)

                    โจ functoriality-โ โฉ-โผ

                  map โจ ฯ โฉ โ map f

                    โจ inv-surj โ refl โฉ-โผ

                  โจ ฯ โฉ โ map f

                    โจ unit-r-โ โปยน โฉ-โผ

                  โจ ฯ โฉ โ map f โ id

                    โจ refl โ inv-l-โ (of ฯ) โปยน โฉ-โผ

                  โจ ฯ โฉ โ map f โ (โจ ฯ โฉโปยน โ โจ ฯ โฉ)

                    โจ assoc-r-โ โฉ-โผ

                  (โจ ฯ โฉ โ map f โ โจ ฯ โฉโปยน) โ โจ ฯ โฉ

                    โจ inv-surj โปยน โ refl โฉ-โผ

                  map (mapOf (F โ-๐๐๐ญ โฒ eso โฒ) f) โ โจ ฯ โฉ

                    โจ refl โ inv-surj โปยน โฉ-โผ

                  map (mapOf (F โ-๐๐๐ญ โฒ eso โฒ) f) โ map โจ ฯ โฉ

                    โจ functoriality-โ โปยน โฉ-โผ

                  map (mapOf (F โ-๐๐๐ญ โฒ eso โฒ) f โ โจ ฯ โฉ)

                    โ

          ฮฒ : Natural id (F โ-๐๐๐ญ โฒ eso โฒ)
          ฮฒ = (ฮป x -> โจ ฯ โฉโปยน) since natural ฮป f -> cancel-injective (P f)
            where
              P : โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> map (โจ ฯ โฉโปยน โ mapOf (F โ-๐๐๐ญ โฒ eso โฒ) f) โผ map (f โ โจ ฯ โฉโปยน)
              P f = map (โจ ฯ โฉโปยน โ mapOf (F โ-๐๐๐ญ โฒ eso โฒ) f)

                    โจ functoriality-โ โฉ-โผ

                    map โจ ฯ โฉโปยน โ map (mapOf (F โ-๐๐๐ญ โฒ eso โฒ) f)

                    โจ inv-surj โ refl โฉ-โผ

                    โจ ฯ โฉโปยน โ map (mapOf (F โ-๐๐๐ญ โฒ eso โฒ) f)

                    โจ refl โ inv-surj โฉ-โผ

                    โจ ฯ โฉโปยน โ (โจ ฯ โฉ โ map f โ โจ ฯ โฉโปยน)

                    โจ (refl โ assoc-l-โ) โ assoc-r-โ โฉ-โผ

                    (โจ ฯ โฉโปยน โ โจ ฯ โฉ) โ (map f โ โจ ฯ โฉโปยน)

                    โจ inv-l-โ (of ฯ) โ refl โฉ-โผ

                    id โ (map f โ โจ ฯ โฉโปยน)

                    โจ unit-l-โ โฉ-โผ

                    (map f โ โจ ฯ โฉโปยน)

                    โจ refl โ inv-surj โปยน โฉ-โผ

                    (map f โ map โจ ฯ โฉโปยน)

                    โจ functoriality-โ โปยน โฉ-โผ

                    (map (f โ โจ ฯ โฉโปยน))

                    โ

          Proof : isIso (hom ฮฑ)
          Proof = record
            { inverse-โ = ฮฒ
            ; inv-r-โ = componentwise (ฮป x โ inv-r-โ (of ฯ))
            ; inv-l-โ = componentwise (ฮป x โ inv-l-โ (of ฯ))
            }


      lem-7 : โฒ eso โฒ โ-๐๐๐ญ F โผ id
      lem-7 = ฮฑ since Proof
        where
          ฯ = inv-eso

          --
          -- Note: the naturality proof is almost the same as above
          --
          ฮฑ : Natural (โฒ eso โฒ โ-๐๐๐ญ F) id
          ฮฑ = (ฮป x โ โจ inv-eso โฉ) since natural (ฮป f โ P f)
            where
              P : โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> (โจ ฯ โฉ โ f) โผ (mapOf (โฒ eso โฒ โ-๐๐๐ญ F) f โ โจ ฯ โฉ)
              P f = โจ ฯ โฉ โ f

                    โจ unit-r-โ โปยน โฉ-โผ

                  โจ ฯ โฉ โ f โ id

                    โจ refl โ inv-l-โ (of ฯ) โปยน โฉ-โผ

                  โจ ฯ โฉ โ f โ (โจ ฯ โฉโปยน โ โจ ฯ โฉ)

                    โจ assoc-r-โ โฉ-โผ

                  (โจ ฯ โฉ โ f โ โจ ฯ โฉโปยน) โ โจ ฯ โฉ

                    โจ inv-surj โปยน โ refl โฉ-โผ

                  (mapOf (โฒ eso โฒ โ-๐๐๐ญ F) f) โ โจ ฯ โฉ

                    โ

          ฮฒ : Natural id (โฒ eso โฒ โ-๐๐๐ญ F)
          ฮฒ = (ฮป x โ โจ inv-eso โฉโปยน) since natural ฮป f โ P f
            where
              P : โ{a b : โจ ๐ โฉ} -> (f : a โถ b) -> (โจ ฯ โฉโปยน โ mapOf (โฒ eso โฒ โ-๐๐๐ญ F) f) โผ (f โ โจ ฯ โฉโปยน)
              P f = โจ ฯ โฉโปยน โ mapOf (โฒ eso โฒ โ-๐๐๐ญ F) f

                    โจ refl โ inv-surj โฉ-โผ

                    โจ ฯ โฉโปยน โ (โจ ฯ โฉ โ f โ โจ ฯ โฉโปยน)

                    โจ (refl โ assoc-l-โ) โ assoc-r-โ โฉ-โผ

                    (โจ ฯ โฉโปยน โ โจ ฯ โฉ) โ (f โ โจ ฯ โฉโปยน)

                    โจ inv-l-โ (of ฯ) โ refl โฉ-โผ

                    id โ (f โ โจ ฯ โฉโปยน)

                    โจ unit-l-โ โฉ-โผ

                    f โ โจ ฯ โฉโปยน

                    โ

          Proof : isIso (hom ฮฑ)
          Proof = record
            { inverse-โ = ฮฒ
            ; inv-r-โ = componentwise (ฮป x โ inv-r-โ (of inv-eso))
            ; inv-l-โ = componentwise (ฮป x โ inv-l-โ (of inv-eso))
            }

    isIso-๐๐๐ญ:byFFEso : isIso-๐๐๐ญ F
    isIso-๐๐๐ญ:byFFEso = Proof
      where
        Proof = record
          { inverse-โ-๐๐๐ญ = eso since lem-5
          ; inv-r-โ-๐๐๐ญ = lem-6
          ; inv-l-โ-๐๐๐ญ = lem-7
          }
