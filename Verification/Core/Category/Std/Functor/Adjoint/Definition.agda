
module Verification.Core.Category.Std.Functor.Adjoint.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Morphism
open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity


module _ {๐ : Category ๐} {๐ : Category ๐} where
  record isAdjoint (F : Functor ๐ ๐) (G : Functor ๐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
    field adj    : โ(a : โจ ๐ โฉ) -> โจ F โฉ (โจ G โฉ a) โถ a
    field coadj  : โ(a : โจ ๐ โฉ) -> a โถ โจ G โฉ (โจ F โฉ a)
    field {{isNatural:adj}} : isNatural (G โ-๐๐๐ญ F) id adj
    field {{isNatural:coadj}} : isNatural id (F โ-๐๐๐ญ G) coadj
    field reduce-coadj : โ{b : โจ ๐ โฉ}  -> coadj _ โ map (adj _) โผ id {a = โจ G โฉ b}
    field reduce-adj : โ{a : โจ ๐ โฉ}    -> map (coadj _) โ (adj _) โผ id {a = โจ F โฉ a}

  open isAdjoint {{...}} public

  _โฃ_ = isAdjoint


  module _ {F : Functor ๐ ๐} {G : Functor ๐ ๐} {{_ : isAdjoint F G}} where

    -- |> For any two objects [..] and [..],
    module _ {a : โจ ๐ โฉ} {b : โจ ๐ โฉ} where

      -- |> we have an isomorphism between hom-types as follows:
      free : (a โถ โจ G โฉ b) -> (โจ F โฉ a โถ b)
      free f = map f โ adj _

      -- | The inverse direction is given by:
      cofree : (โจ F โฉ a โถ b) -> (a โถ โจ G โฉ b)
      cofree f = coadj _ โ map f

      inv-free : โ{f} -> free (cofree f) โผ f
      inv-free {f} =
        map ((coadj _) โ (map f)) โ adj _      โจ functoriality-โ โ refl โฉ-โผ
        map (coadj _) โ map (map f) โ adj _    โจ assoc-l-โ โฉ-โผ
        map (coadj _) โ (map (map f) โ adj _)  โจ refl โ naturality f โปยน โฉ-โผ
        map (coadj _) โ (adj _ โ f)            โจ assoc-r-โ โฉ-โผ
        (map (coadj _) โ adj _) โ f            โจ reduce-adj โ refl โฉ-โผ
        id โ f                           โจ unit-l-โ โฉ-โผ
        f                                โ

      inv-cofree : โ{f} -> cofree (free f) โผ f
      inv-cofree {f} = {!!}

      cong-โผ-free : โ{f g} -> f โผ g -> free f โผ free g
      cong-โผ-free p = p
        โช cong-โผ โซ
        โช (_โ refl) โซ

      cong-โผ-cofree : โ{f g} -> f โผ g -> cofree f โผ cofree g
      cong-โผ-cofree p = p
        โช cong-โผ โซ
        โช (refl โ_) โซ

      cancel-injective-free : โ{f g} -> free f โผ free g -> f โผ g
      cancel-injective-free p = p
        โช cong-โผ-cofree โซ
        โช inv-cofree โโผโ inv-cofree โซ

      cancel-injective-cofree : โ{f g} -> cofree f โผ cofree g -> f โผ g
      cancel-injective-cofree p = p
        โช cong-โผ-free โซ
        โช inv-free โโผโ inv-free โซ

      -- isSetoidHom:free : isSetoidHom โฒ(a โถ โจ G โฉ b)โฒ โฒ(โจ F โฉ a โถ b)โฒ free
      -- isSetoidHom:free = record { cong-โผ = {!!} }

      -- isSetoidHom:cofree : isSetoidHom โฒ(โจ F โฉ a โถ b)โฒ โฒ(a โถ โจ G โฉ b)โฒ cofree
      -- isSetoidHom:cofree = record { cong-โผ = {!!} }

      -- isInjective:free : isInjective free
      -- isInjective:free = record { cancel-injective = {!!} }

      -- isInjective:cofree : isInjective cofree
      -- isInjective:cofree = record { cancel-injective = {!!} }

