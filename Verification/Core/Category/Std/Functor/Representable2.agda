
module Verification.Core.Category.Std.Functor.Representable2 where

--
-- NOTE:
--   This is a rewriting of Verification.Core.Category.Std.Functor.Representable,
--   to be merged when more complete.
--

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Instance.Category
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid


instance
  hasU:â' : â{A : ð° ð} {B : A -> ð° ð} -> hasU (â(a) -> B a) _ _
  getU (hasU:â' {A = A} {B}) = â(a) -> B a
  getP (hasU:â' {ð} {ð} {A = A} {B}) u = isAnything {A = â(a) -> B a} u (ââ)
  reconstruct (hasU:â' {A = A} {B}) (x , _) = x
  destructEl (hasU:â' {A = A} {B}) f = f
  destructP (hasU:â' {A = A} {B}) _ = record {}


-- We need isomorphisms across universe levels of presheaves
record isIso-ðð­ð {a : Setoid ð} {b : Setoid ð} (f : SetoidHom a b) : ð° (ð ï½¤ ð) where
  field inverse-ðð­ð : SetoidHom b a
        inv-r-â-ðð­ð : (f â-ðð­ð inverse-ðð­ð) â¼ id-ðð­ð
        inv-l-â-ðð­ð : (inverse-ðð­ð â-ðð­ð f) â¼ id-ðð­ð
open isIso-ðð­ð {{...}} public

_â-ðð­ð_ : (A : Setoid ð) (B : Setoid ð) -> ð° (ð ï½¤ ð)
A â-ðð­ð B = (SetoidHom A B) :& isIso-ðð­ð


Coððð¡ : (ð : Category ð) -> â ð -> ð° _
Coððð¡ ð ð = ðð®ð§ð ð (ðð­ð ð)

module _ {ð : Category ð} where
  module _ (A : Coððð¡ ð ð) (B : Coððð¡ ð ð) where
    record isPresheafMap (f : â(c : â¨ ð â©) -> SetoidHom (â¨ A â© c) (â¨ B â© c)) : ð° (ð ï½¤ ð ï½¤ ð) where
      -- field naturality : â{c d : â¨ ð â©} -> 

    PresheafMap = _ :& isPresheafMap

  record isIso-Coððð¡ {A : Coððð¡ ð ð} {B : Coððð¡ ð ð} (f : PresheafMap A B) : ð° (ð ï½¤ ð ï½¤ ð) where
    field inverse-â-Coððð¡ : PresheafMap B A

  open isIso-Coððð¡ public

  _â-Coððð¡_ : (A : Coððð¡ ð ð) (B : Coððð¡ ð ð) -> ð° (ð ï½¤ ð ï½¤ ð)
  _â-Coððð¡_ A B = PresheafMap A B :& isIso-Coððð¡


--
-- the hom functors
--
module _ {C : ð° ð} {{_ : isCategory {ðâ} C}} where
  private
    ð : Category _
    ð = â² C â²

  --
  -- first the contravariant hom
  --

  module _ (b : C) where
    âððáµ : C -> ðð­ð _
    âððáµ a = a â¶ b

    -- macro âðð = #structureOn âððáµ


  module _ {a : C} where
    instance
      isFunctor:âðð : isFunctor (ð áµáµ) (ðð­ð _) (âððáµ a)
      isFunctor.map isFunctor:âðð = {!!}
      isFunctor.isSetoidHom:map isFunctor:âðð = {!!}
      isFunctor.functoriality-id isFunctor:âðð = {!!}
      isFunctor.functoriality-â isFunctor:âðð = {!!}

  module _ (a : C) where
    --
    -- It seems that resolution cannot distinguish
    -- between âðð and âððáµáµ functor instances,
    -- so we cannot use this as macro, but need
    -- to specialize to Functor.
    --
    -- macro âððáµáµ = #structureOn âððáµáµáµ
    --

    âðð : Functor (ð áµáµ) (ðð­ð _)
    âðð = â² âððáµ a â²

  --
  -- now the covariant hom
  --
  module _ (a : C) where
    âððáµáµáµ : C -> ðð­ð _
    âððáµáµáµ b = a â¶ b


  module _ {a : C} where

    map-âððáµáµ : â{x y : C} -> x â¶ y -> âððáµáµáµ a x â¶ âððáµáµáµ a y
    map-âððáµáµ f = (Î» g -> g â f) since record { cong-â¼ = Î» p â p â refl }

    instance
      isFunctor:âððáµáµ : isFunctor ð (ðð­ð _) (âððáµáµáµ a)
      isFunctor.map isFunctor:âððáµáµ = map-âððáµáµ
      isFunctor.isSetoidHom:map isFunctor:âððáµáµ = {!!}
      isFunctor.functoriality-id isFunctor:âððáµáµ = {!!}
      isFunctor.functoriality-â isFunctor:âððáµáµ = {!!}


  module _ (a : C) where
    --
    -- It seems that resolution cannot distinguish
    -- between âðð and âððáµáµ functor instances,
    -- so we cannot use this as macro, but need
    -- to specialize to Functor.
    --
    -- macro âððáµáµ = #structureOn âððáµáµáµ
    --

    âððáµáµ : Functor ð (ðð­ð _)
    âððáµáµ = â² âððáµáµáµ a â²


module _ {ð : Category ð} where
  record isCorepresented (F : Coððð¡ ð ð) (x : â¨ ð â©) : ð° (ð ï½¤ ð) where
    field corep : F â-Coððð¡ âððáµáµ x

  open isCorepresented public

  record isRepresented (F : Coððð¡ (ð áµáµ) ð) (x : â¨ ð â©) : ð° (ð ï½¤ ð) where
    field rep : F â-Coððð¡ âðð x

  open isRepresented public
  -- Corep : (Functor ð (ðð­ð _)) -> ð° _
  -- Corep F = Structure (isCorep F)
