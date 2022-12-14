
module Verification.Research.StateCalculus.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Category.Std.Category.Construction.Coproduct
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Data.List.Variant.Unary.Definition

module _ (ð : Category ð) where
  HomOf : â¨ ð â© -> â¨ ð â© -> ð° _
  HomOf a b = a â¶ b

module _ (ð : Category ð) (x : â¨ ð â©) where
  over : Category ð
  over = {!!}

-- module _ (ð : Category ð) {{_ : hasInitial}}

module Version1 (ð : Category ð) (L : Category ð) (d : â¨ ð â©) (X : ð° ð) (Lâ : ð°â) (loc : Lâ -> â¨ L â©)
  {{_ : hasFiniteCoproducts L}} {{_ : hasFiniteProducts ð}} {{_ : hasFiniteProducts L}}
  where

  StateObject = â¨ ð â© Ã-ð° â¨ L â©

  data StateHom : StateObject -> StateObject -> ð° (ð ï½¤ ð ï½¤ ð) where
    pure : â{a b} -> a â¶ b -> â{m n} -> m â n -> StateHom (a , m) (b , n)
    write : (i : Lâ) -> StateHom (d , â¥) ((â¤ , loc i))
    read : (i : Lâ) -> StateHom (â¤ , loc i) (d , loc i)
    -- par : {aâ aâ bâ bâ m n} -> (m Ã n â â¥) -> StateHom (aâ , m)

module Version2
  (ð : Category ð) (L : Functor ð (ððð­ ð))
  {{_ : hasFiniteProducts ð}}
  -- {{_ : hasFiniteCoproducts L}} {{_ : hasFiniteProducts ð}} {{_ : hasFiniteProducts L}}
  (d : â¨ ð â©)
  (l0 : â¨ ð â©)
  (loc : â{a} -> (a â¶ l0) -> â¨ (â¨ L â© a) â©)
  where

  -- LExt : ð° ?
  -- LExt =
  -- StateObject = â¨ ð â© Ã-ð° â¨ L â©

  data StateHom : (a b : â¨ ð â©) {m n : â¨ â¨ L â© a â©} (f : HomOf (â¨ L â© a) m n) -> ð° (ð ï½¤ ð) where
    -- pure : â{a b} -> a â¶ b -> â{m n : â¨ L â©} -> (Ï : m â n) -> StateHom a b â¨ Ï â©
    write : StateHom (d â l0) â¤ {loc Ïâ} {loc Ïâ} {!!}

  --   write : (i : Lâ) -> StateHom (d , â¥) ((â¤ , loc i))
  --   read : (i : Lâ) -> StateHom (â¤ , loc i) (d , loc i)
    -- par : {aâ aâ bâ bâ m n} -> (m Ã n â â¥) -> StateHom (aâ , m)




