
module Verification.Core.Data.List.Variant.Binary.Element.As.Indexed where

open import Verification.Core.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.Monoid.By.Coproduct


module _ {A : π° π} where

  el : π₯ππΎπΎ-ππ¨π§ A -> ππ± A (ππ§π’π― π)
  el a = indexed (Ξ» i β a β i)

  macro
    ππ = #structureOn el

  private
    lem-1 : β{a : π₯ππΎπΎ-ππ¨π§ A} -> el (β β a) β el a
    lem-1 {a} = f since P
      where
        f : el (β β a) βΆ el a
        f _ (right-β x) = x

        P = record
            { inverse-β = Ξ» _ x -> right-β x
            ; inv-r-β   = Ξ» {i _ (right-β x) β right-β x}
            ; inv-l-β   = Ξ» _ -> refl
            }

    lem-2 : β{a : π₯ππΎπΎ-ππ¨π§ A} -> el (a β β) β el a
    lem-2 {a} = f since P
      where
        f : el (a β β) βΆ el a
        f _ (left-β x) = x

        P = record
            { inverse-β = Ξ» _ x -> left-β x
            ; inv-r-β   = Ξ» {i _ (left-β x) β left-β x}
            ; inv-l-β   = Ξ» _ -> refl
            }

    lem-3 : β{a b c : π₯ππΎπΎ-ππ¨π§ A} -> el (a β b β c) β el (a β (b β c))
    lem-3 {a} {b} {c} = f since P
      where
        f : el (a β b β c) βΆ el (a β (b β c))
        f _ (left-β (left-β x)) = left-β x
        f _ (left-β (right-β x)) = right-β (left-β x)
        f _ (right-β x) = right-β (right-β x)

        g : el (a β (b β c)) βΆ el (a β b β c)
        g _ (left-β x) = left-β (left-β x)
        g _ (right-β (left-β x)) = left-β (right-β x)
        g _ (right-β (right-β x)) = right-β x

        Pβ : β{a : A} -> (x : (_ β a)) -> g _ (f _ x) β‘ x
        Pβ {a} (left-β (left-β x)) = refl-β‘
        Pβ {a} (left-β (right-β x)) = refl-β‘
        Pβ {a} (right-β x) = refl-β‘

        Pβ : β{a : A} -> (x : (_ β a)) -> f _ (g _ x) β‘ x
        Pβ {a} (left-β x) = refl-β‘
        Pβ {a} (right-β (left-β x)) = refl-β‘
        Pβ {a} (right-β (right-β x)) = refl-β‘

        P = record
            { inverse-β = g
            ; inv-r-β = Ξ» _ -> funExt Pβ
            ; inv-l-β = Ξ» _ -> funExt Pβ
            }

    lem-4 : β{a b c : π₯ππΎπΎ-ππ¨π§ A} -> (el a β el b) -> el (a β c) β el (b β c)
    lem-4 {a} {b} {c} f = g since P
      where
        g : el (a β c) βΆ el (b β c)
        g _ (left-β x) = left-β (β¨ f β© _ x)
        g _ (right-β x) = right-β x

        h : el (b β c) βΆ el (a β c)
        h _ (left-β x) = left-β (inverse-β (of f) _ x)
        h _ (right-β x) = right-β x

        Pβ : β{a : A} -> (x : (_ β a)) -> h _ (g _ x) β‘ x
        Pβ (left-β x) = cong left-β (Ξ» i -> inv-r-β (of f) _ i x)
        Pβ (right-β x) = refl-β‘

        Pβ : β{a : A} -> (x : (_ β a)) -> g _ (h _ x) β‘ x
        Pβ (left-β x) = cong left-β (Ξ» i -> inv-l-β (of f) _ i x)
        Pβ (right-β x) = refl-β‘

        P = record
            { inverse-β = h
            ; inv-r-β   = Ξ» _ -> funExt Pβ
            ; inv-l-β   = Ξ» _ -> funExt Pβ
            }

    lem-5 : β{a b c : π₯ππΎπΎ-ππ¨π§ A} -> (el a β el b) -> el (c β a) β el (c β b)
    lem-5 {a}{b}{c} f = g since P
      where
        g : el (c β a) βΆ el (c β b)
        g _ (right-β x) = right-β (β¨ f β© _ x)
        g _ (left-β x) = left-β x

        h : el (c β b) βΆ el (c β a)
        h _ (right-β x) = right-β (inverse-β (of f) _ x)
        h _ (left-β x) = left-β x

        Pβ : β{a : A} -> (x : (_ β a)) -> h _ (g _ x) β‘ x
        Pβ (left-β x) = refl-β‘
        Pβ (right-β x) = cong right-β (Ξ» i -> inv-r-β (of f) _ i x)

        Pβ : β{a : A} -> (x : (_ β a)) -> g _ (h _ x) β‘ x
        Pβ (left-β x) = refl-β‘
        Pβ (right-β x) = cong right-β (Ξ» i -> inv-l-β (of f) _ i x)

        P = record
            { inverse-β = h
            ; inv-r-β   = Ξ» _ -> funExt Pβ
            ; inv-l-β   = Ξ» _ -> funExt Pβ
            }

    lem-6 : el β β β
    lem-6 = f since P
      where
        f : el β βΆ β
        f _ ()

        g : β βΆ el β
        g _ ()

        P = record
            { inverse-β = g
            ; inv-r-β   = Ξ» {_ i ()}
            ; inv-l-β   = Ξ» {_ i ()}
            }

    lem-7 : β{a b : π₯ππΎπΎ-ππ¨π§ A} -> el (a β b) β el a β el b
    lem-7 {a} {b} = f since P
      where
        f : el (a β b) βΆ el a β el b
        f _ (left-β x) = left x
        f _ (right-β x) = right x

        g : el a β el b βΆ el (a β b)
        g _ (left x) = left-β x
        g _ (just x) = right-β x

        Pβ : β{a : A} -> (x : (_ β a)) -> g _ (f _ x) β‘ x
        Pβ (left-β x)  = refl-β‘
        Pβ (right-β x) = refl-β‘

        Pβ : β{a : A} -> (x : (_ β a) + (_ β a)) -> f _ (g _ x) β‘ x
        Pβ (left x)  = refl-β‘
        Pβ (right x) = refl-β‘

        P = record
            { inverse-β = g
            ; inv-r-β   = Ξ» _ -> funExt Pβ
            ; inv-l-β   = Ξ» _ -> funExt Pβ
            }


  instance
    isSetoidHom:el : isSetoidHom (π₯ππΎπΎ-ππ¨π§ A) (ππ± A (ππ§π’π― π)) el
    isSetoidHom:el = record { cong-βΌ = rec-RST f}
      where
        f : β{a b : π₯ππΎπΎ-ππ¨π§ A} -> (a βΌ-βList b) -> _
        f unit-l-β-β§ = lem-1
        f unit-r-β-β§ = lem-2
        f assoc-l-β-β§ = lem-3
        f (cong-l-β-β§ p) = lem-4 (f p)
        f (cong-r-β-β§ p) = lem-5 (f p)

  instance
    isMonoidHom:el : isMonoidHom (π₯ππΎπΎ-ππ¨π§ A) (ππ± A (ππ§π’π― π)) ππ
    isMonoidHom:el = record
                     { pres-β = lem-6
                     ; pres-β = lem-7
                     }


  -- -- setoid hom to ππ’π§ππ±
  -- open import Verification.Core.Category.Std.Category.Subcategory.Full
  -- private
  --   instance
  --     _ : isSetoid (ππ?π₯π₯ (ππ± A (ππ§π’π― π)) ππ)
  --     _ = isSetoid:byCategory

  -- isSetoidHom:incl-π₯ππΎπΎ : isSetoidHom (π₯ππΎπΎ-ππ¨π§ A) (ππ?π₯π₯ (ππ± A (ππ§π’π― π)) ππ) incl
  -- isSetoidHom:incl-π₯ππΎπΎ = record { cong-βΌ = Ξ» p β {!!} }

  identify-β : β{a b : A} -> incl a β b -> a β£ b
  identify-β incl = refl-β£



