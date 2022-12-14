
module Verification.Core.Category.Std.Morphism.Epi.Definition where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Morphism
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition


-- [Definition]

-- | Let [..] [] be a category.
module _ {๐ : ๐ฐ ๐} {{_ : isCategory {๐} ๐}} where

  -- |> An arrow |f : a โถ b| in |๐| is called an /epimorphism/ if
  -- the following condition holds:
  record isEpi {a b : ๐} (f : a โถ b) : ๐ฐ (๐ ๏ฝค ๐) where
    constructor epi
    -- | If two parallel arrows |ฮฑ| and |ฮฒ| are equal after
    --   post-composition with |f|, then they are really equal, ie.:
    field cancel-epi : โ{x : ๐} -> โ{ฮฑ ฮฒ : b โถ x} -> f โ ฮฑ โผ f โ ฮฒ -> ฮฑ โผ ฮฒ

  open isEpi {{...}} public

  -- //

  -- | In classical mathematics, surjective functions are exactly the epimorphisms
  --   in the category of sets. In our setting this is not quite so, since the notion
  --   of surjectivity is stronger. Nevertheless, it is useful to think of epimorphisms
  --   that way.


  -- [Hide]
  isEpi:id : โ{a : ๐} -> isEpi (id {a = a})
  isEpi:id = epi (ฮป p โ unit-l-โ โปยน โ p โ unit-l-โ)

  isEpi:โ : โ{a b c : ๐} -> {f : a โถ b} -> {g : b โถ c} -> isEpi f -> isEpi g -> isEpi (f โ g)
  isEpi:โ p q = epi (ฮป gfฮฑโผgfฮฒ โ cancel-epi (cancel-epi (assoc-r-โ โ gfฮฑโผgfฮฒ โ assoc-l-โ)) )
    where
      instance
        _ = p
        _ = q


module _ {๐ : Category ๐} {๐ : Category ๐} where

  --------------------------------------------------------------
  -- reflection

  record isEpiReflecting (F : Functor ๐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
    field reflect-isEpi : โ{a b : โจ ๐ โฉ} -> โ{f : a โถ b} -> isEpi (map {{of F}} f) -> isEpi f

  open isEpiReflecting {{...}} public

  --------------------------------------------------------------
  -- preservation
  record isEpiPreserving (F : Functor ๐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
    field preserve-isEpi : โ{a b : โจ ๐ โฉ} -> โ{f : a โถ b} -> isEpi f -> isEpi (map {{of F}} f)

  open isEpiPreserving {{...}} public

-- //
