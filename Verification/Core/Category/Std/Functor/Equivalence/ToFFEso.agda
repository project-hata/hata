
module Verification.Core.Category.Std.Functor.Equivalence.ToFFEso where

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
  module _ {F : Functor ๐ ๐} {{ofF : isIso-๐๐๐ญ F}} where
    private
      G : Functor ๐ ๐
      G = inverse-โ-๐๐๐ญ ofF

      ฯ : โ{a : โจ ๐ โฉ} -> โจ G โฉ (โจ F โฉ a) โ a
      ฯ = โจ โจ inv-r-โ-๐๐๐ญ (ofF) โฉ โฉ _ since record
        { inverse-โ = โจ โจ inv-r-โ-๐๐๐ญ ofF โฉโปยน โฉ _
        ; inv-r-โ = โจ inv-r-โ (of inv-r-โ-๐๐๐ญ ofF) โฉ _
        ; inv-l-โ = โจ inv-l-โ (of inv-r-โ-๐๐๐ญ ofF) โฉ _
        }

      ฯ : โ{a : โจ ๐ โฉ} -> โจ F โฉ (โจ G โฉ a) โ a
      ฯ = โจ โจ inv-l-โ-๐๐๐ญ (ofF) โฉ โฉ _ since record
        { inverse-โ = โจ โจ inv-l-โ-๐๐๐ญ ofF โฉโปยน โฉ _
        ; inv-r-โ = โจ inv-r-โ (of inv-l-โ-๐๐๐ญ ofF) โฉ _
        ; inv-l-โ = โจ inv-l-โ (of inv-l-โ-๐๐๐ญ ofF) โฉ _
        }

      --
      -- First, we show that both F and G are faithful
      --
      module _ {a b : โจ ๐ โฉ} where
        cancel-injective-F : {f g : a โถ b} -> map f โผ map g -> f โผ g
        cancel-injective-F {f} {g} p =

          f

          โจ unit-l-โ โปยน โฉ-โผ

          id โ f

          โจ inv-l-โ (of ฯ) โปยน โ refl โฉ-โผ

          โจ ฯ โฉโปยน โ โจ ฯ โฉ โ f

          โจ assoc-l-โ โฉ-โผ

          โจ ฯ โฉโปยน โ (โจ ฯ โฉ โ f)

          โจ refl โ naturality f โฉ-โผ

          โจ ฯ โฉโปยน โ (mapOf (F โ-๐๐๐ญ G) f โ โจ ฯ โฉ)

          โจ refl โ (cong-โผ p โ refl) โฉ-โผ

          โจ ฯ โฉโปยน โ (mapOf (F โ-๐๐๐ญ G) g โ โจ ฯ โฉ)

          โจ refl โ naturality g โปยน โฉ-โผ

          โจ ฯ โฉโปยน โ (โจ ฯ โฉ โ g)

          โจ assoc-r-โ โฉ-โผ

          โจ ฯ โฉโปยน โ โจ ฯ โฉ โ g

          โจ inv-l-โ (of ฯ) โ refl โฉ-โผ

          id โ g

          โจ unit-l-โ โฉ-โผ

          g

          โ

      instance
        isFaithful:F : isFaithful F
        isFaithful.isInjective:map isFaithful:F = record { cancel-injective = cancel-injective-F }

      module _ {a b : โจ ๐ โฉ} where
        cancel-injective-G : {f g : a โถ b} -> map f โผ map g -> f โผ g
        cancel-injective-G {f} {g} p =

          f

          โจ unit-l-โ โปยน โฉ-โผ

          id โ f

          โจ inv-l-โ (of ฯ) โปยน โ refl โฉ-โผ

          โจ ฯ โฉโปยน โ โจ ฯ โฉ โ f

          โจ assoc-l-โ โฉ-โผ

          โจ ฯ โฉโปยน โ (โจ ฯ โฉ โ f)

          โจ refl โ naturality f โฉ-โผ

          โจ ฯ โฉโปยน โ (mapOf (G โ-๐๐๐ญ F) f โ โจ ฯ โฉ)

          โจ refl โ (cong-โผ p โ refl) โฉ-โผ

          โจ ฯ โฉโปยน โ (mapOf (G โ-๐๐๐ญ F) g โ โจ ฯ โฉ)

          โจ refl โ naturality g โปยน โฉ-โผ

          โจ ฯ โฉโปยน โ (โจ ฯ โฉ โ g)

          โจ assoc-r-โ โฉ-โผ

          โจ ฯ โฉโปยน โ โจ ฯ โฉ โ g

          โจ inv-l-โ (of ฯ) โ refl โฉ-โผ

          id โ g

          โจ unit-l-โ โฉ-โผ

          g

          โ

      instance
        isFaithful:G : isFaithful G
        isFaithful.isInjective:map isFaithful:G = record { cancel-injective = cancel-injective-G }

      --
      -- Next, we need to show that we have for the isomorphisms:
      -- |ฯ @ (FG X) โผ FG (ฯ @ X)|
      --
      -- For that, we look at the following commuting square, given by naturality.
      -- $
      -- % https://q.uiver.app/?q=WzAsNCxbMCwwLCJYIl0sWzEsMCwiRkdYIl0sWzAsMSwiRkdYIl0sWzEsMSwiRkdGR1giXSxbMCwxLCJcXHBoaV57LTF9X1giXSxbMCwyLCJcXHBoaV57LTF9X1giLDJdLFsyLDMsIkZHXFxwaGleey0xfV9YIiwyXSxbMSwzLCJcXHBoaV57LTF9X3tGR1h9Il1d
      -- \[\begin{tikzcd}
      -- 	X & FGX \\
      -- 	FGX & FGFGX
      -- 	\arrow["{\phi^{-1}_X}", from=1-1, to=1-2]
      -- 	\arrow["{\phi^{-1}_X}"', from=1-1, to=2-1]
      -- 	\arrow["{FG\phi^{-1}_X}"', from=2-1, to=2-2]
      -- 	\arrow["{\phi^{-1}_{FGX}}", from=1-2, to=2-2]
      -- \end{tikzcd}\]
      -- $
      --
      -- It gives us the equation:
      prop-1 : โ{x} -> โจ ฯ {โจ G โฉ (โจ F โฉ x)} โฉโปยน โผ mapOf (F โ-๐๐๐ญ G) (โจ ฯ {x} โฉโปยน)
      prop-1 {x} = โจ ฯ {โจ G โฉ (โจ F โฉ x)} โฉโปยน

               โจ unit-l-โ โปยน โฉ-โผ

               id โ โจ ฯ {โจ G โฉ (โจ F โฉ x)} โฉโปยน

               โจ inv-r-โ (of ฯ) โปยน โ refl โฉ-โผ

               โจ ฯ โฉ โ โจ ฯ โฉโปยน โ โจ ฯ {โจ G โฉ (โจ F โฉ x)} โฉโปยน

               โจ assoc-l-โ โฉ-โผ

               โจ ฯ โฉ โ (โจ ฯ โฉโปยน โ โจ ฯ {โจ G โฉ (โจ F โฉ x)} โฉโปยน)

               โจ refl โ sym (naturality โจ ฯ โฉโปยน) โฉ-โผ

               โจ ฯ โฉ โ (โจ ฯ โฉโปยน โ mapOf (F โ-๐๐๐ญ G) (โจ ฯ {x} โฉโปยน))

               โจ assoc-r-โ โฉ-โผ

               (โจ ฯ โฉ โ โจ ฯ โฉโปยน) โ mapOf (F โ-๐๐๐ญ G) (โจ ฯ {x} โฉโปยน)

               โจ inv-r-โ (of ฯ) โ refl โฉ-โผ

               id โ mapOf (F โ-๐๐๐ญ G) (โจ ฯ {x} โฉโปยน)

               โจ unit-l-โ โฉ-โผ

               mapOf (F โ-๐๐๐ญ G) (โจ ฯ {x} โฉโปยน)

               โ



      module _ {a b : โจ ๐ โฉ} where
        surj-F : โจ F โฉ a โถ โจ F โฉ b -> a โถ b
        surj-F f = โจ ฯ โฉโปยน โ map f โ โจ ฯ โฉ

        instance
          isSetoidHom:surj-F : isSetoidHom (โจ F โฉ a โถ โจ F โฉ b) (a โถ b) surj-F
          isSetoidHom:surj-F = record { cong-โผ = ฮป x โ refl โ cong-โผ x โ refl }

        lem-1 : โ{f} -> map (surj-F f) โผ f
        lem-1 {f} = cancel-injective-G P
          where
            FG = F โ-๐๐๐ญ G
            P : mapOf (F โ-๐๐๐ญ G) (โจ ฯ โฉโปยน โ map f โ โจ ฯ โฉ) โผ mapOf G f
            P = mapOf (F โ-๐๐๐ญ G) (โจ ฯ โฉโปยน โ map f โ โจ ฯ โฉ)

                โจ functoriality-โ {{of F โ-๐๐๐ญ G}} โฉ-โผ

                mapOf FG (โจ ฯ โฉโปยน โ map f) โ mapOf FG โจ ฯ โฉ

                โจ functoriality-โ {{of F โ-๐๐๐ญ G}} โ refl โฉ-โผ

                mapOf FG โจ ฯ โฉโปยน โ mapOf FG (map f) โ mapOf FG โจ ฯ โฉ

                โจ prop-1 โปยน โ refl โ refl โฉ-โผ

                โจ ฯ โฉโปยน โ mapOf FG (map f) โ mapOf FG โจ ฯ โฉ

                โจ naturality (map f) โ refl โฉ-โผ

                map f โ โจ ฯ โฉโปยน โ mapOf FG โจ ฯ โฉ

                โจ refl โ prop-1 โ refl โฉ-โผ

                map f โ mapOf FG โจ ฯ โฉโปยน โ mapOf FG โจ ฯ โฉ

                โจ assoc-l-โ โฉ-โผ

                map f โ (mapOf FG โจ ฯ โฉโปยน โ mapOf FG โจ ฯ โฉ)

                โจ refl โ functoriality-โ {{of FG}} โปยน โฉ-โผ

                map f โ (mapOf FG (โจ ฯ โฉโปยน โ โจ ฯ โฉ))

                โจ refl โ cong-โผ (cong-โผ (inv-l-โ (of ฯ))) โฉ-โผ

                map f โ (mapOf FG id)

                โจ refl โ functoriality-id {{of FG}} โฉ-โผ

                map f โ id

                โจ unit-r-โ โฉ-โผ

                map f

                โ

        instance
          isSurjective:mapOfF : isSurjective (mapOf F {a = a} {b = b})
          isSurjective.surj isSurjective:mapOfF = surj-F
          isSurjective.isSetoidHom:surj isSurjective:mapOfF = it
          isSurjective.inv-surj isSurjective:mapOfF = lem-1

    isFull:byIsIso-๐๐๐ญ : isFull F
    isFull.isSurjective:map isFull:byIsIso-๐๐๐ญ = isSurjective:mapOfF

    isEssentiallySurjective:byIsIso-๐๐๐ญ : isEssentiallySurjective F
    isEssentiallySurjective.eso isEssentiallySurjective:byIsIso-๐๐๐ญ = โจ G โฉ
    isEssentiallySurjective.inv-eso isEssentiallySurjective:byIsIso-๐๐๐ญ = ฯ


