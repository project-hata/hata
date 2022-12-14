
module Verification.Core.Category.Std.Category.Construction.Product where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.CategoryLike
open import Verification.Core.Category.Std.Category.Construction.Id
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso


--------------------------------------------------------------
-- Showing that _Ć_ on universes lifts to categories

module _ {š : š° š} {š : š° š} {{_ : isCategory {šā} š}} {{_ : isCategory {šā} š}} where

  instance
    isCategory:Ć : isCategory (š Ć š)
    isCategory.Hom isCategory:Ć = Ī» (a , b) (c , d) -> (a ā¶ c) Ć (b ā¶ d)
    isCategory.isSetoid:Hom isCategory:Ć = isSetoid:Ć
    isCategory.id isCategory:Ć         = id , id
    isCategory._ā_ isCategory:Ć        = Ī» (fā , gā) (fā , gā) -> (fā ā fā , gā ā gā)
    isCategory.unit-l-ā isCategory:Ć   = unit-l-ā , unit-l-ā
    isCategory.unit-r-ā isCategory:Ć   = unit-r-ā , unit-r-ā
    isCategory.unit-2-ā isCategory:Ć   = unit-2-ā , unit-2-ā
    isCategory.assoc-l-ā isCategory:Ć  = assoc-l-ā , assoc-l-ā
    isCategory.assoc-r-ā isCategory:Ć  = assoc-r-ā , assoc-r-ā
    isCategory._ā_ isCategory:Ć        = Ī» (pā , qā) (pā , qā) -> (pā ā pā , qā ā qā)


  -- currently special treatment for isomorphisms
  into-Ć-ā : ā{a b : š} {c d : š} -> (p : a ā b) (q : c ā d) -> (a , c) ā (b , d)
  into-Ć-ā p q = (āØ p ā© , āØ q ā©) since P
    where
      P = record
          { inverse-ā  = (inverse-ā (of p) , inverse-ā (of q))
          ; inv-r-ā    = inv-r-ā (of p) , inv-r-ā (of q)
          ; inv-l-ā    = inv-l-ā (of p) , inv-l-ā (of q)
          }

_Ć-ššš­_ :(š : Category š) (š : Category š) -> Category _
_Ć-ššš­_ š š = š Ć š

module _ {š : Category š} {š : Category š} where
  Ļā-ššš­ : Functor (š Ć š) š
  Ļā-ššš­ = fst since P
    where
      P : isFunctor _ _ fst
      isFunctor.map P              = fst
      isFunctor.isSetoidHom:map P  = record { cong-ā¼ = fst }
      isFunctor.functoriality-id P = refl
      isFunctor.functoriality-ā P  = refl

  Ļā-ššš­ : Functor (š Ć š) š
  Ļā-ššš­ = snd since P
    where
      P : isFunctor _ _ snd
      isFunctor.map P              = snd
      isFunctor.isSetoidHom:map P  = record { cong-ā¼ = snd }
      isFunctor.functoriality-id P = refl
      isFunctor.functoriality-ā P  = refl

module _ {š³ : Category š} {š : Category š} {š : Category š} where
  ā§¼_ā§½-ššš­ : (Functor š³ š) Ć (Functor š³ š) -> Functor š³ (š Ć š)
  ā§¼_ā§½-ššš­ (F , G) = h since P
    where
      h : āØ š³ ā© -> š Ć š
      h x = āØ F ā© x , āØ G ā© x

      P : isFunctor _ _ h
      isFunctor.map P              = Ī» Ļ -> map Ļ , map Ļ
      isFunctor.isSetoidHom:map P  = record { cong-ā¼ = Ī» p -> cong-ā¼ p , cong-ā¼ p }
      isFunctor.functoriality-id P = functoriality-id , functoriality-id
      isFunctor.functoriality-ā P  = functoriality-ā , functoriality-ā

  module _ {F : Functor š³ š} {G : Functor š³ š} where
    reduce-Ļā-ššš­ : (ā§¼ F , G ā§½-ššš­ ā-ššš­ Ļā-ššš­) ā F
    reduce-Ļā-ššš­ = Ī± since P
      where
        Ī± : Natural (ā§¼ F , G ā§½-ššš­ ā-ššš­ Ļā-ššš­) F
        Ī± = (Ī» _ -> id) since natural (naturality {{of id-šš®š§š {F = F}}})

        Ī² : Natural F (ā§¼ F , G ā§½-ššš­ ā-ššš­ Ļā-ššš­)
        Ī² = (Ī» _ -> id) since natural (naturality {{of id-šš®š§š {F = F}}})

        P : isIso (hom Ī±)
        P = record
            { inverse-ā  = Ī²
            ; inv-r-ā    = componentwise $ Ī» _ -> unit-2-ā
            ; inv-l-ā    = componentwise $ Ī» _ -> unit-2-ā
            }

    reduce-Ļā-ššš­ : (ā§¼ F , G ā§½-ššš­ ā-ššš­ Ļā-ššš­) ā G
    reduce-Ļā-ššš­ = Ī± since P
      where
        Ī± : Natural (ā§¼ F , G ā§½-ššš­ ā-ššš­ Ļā-ššš­) G
        Ī± = (Ī» _ -> id) since natural (naturality {{of id-šš®š§š {F = G}}})

        Ī² : Natural G (ā§¼ F , G ā§½-ššš­ ā-ššš­ Ļā-ššš­)
        Ī² = (Ī» _ -> id) since natural (naturality {{of id-šš®š§š {F = G}}})

        P : isIso (hom Ī±)
        P = record
            { inverse-ā  = Ī²
            ; inv-r-ā    = componentwise $ Ī» _ -> unit-2-ā
            ; inv-l-ā    = componentwise $ Ī» _ -> unit-2-ā
            }

  module _ {F : Functor š³ (š Ć š)} where
    expand-ā-ššš­ : F ā ā§¼ F ā-ššš­ Ļā-ššš­ , F ā-ššš­ Ļā-ššš­ ā§½-ššš­
    expand-ā-ššš­ = Ī± since P
      where
        Ī± : Natural F ā§¼ F ā-ššš­ Ļā-ššš­ , F ā-ššš­ Ļā-ššš­ ā§½-ššš­
        Ī± = (Ī» _ -> id , id) since natural (Ī» f ā unit-l-ā ā unit-r-ā ā»Ā¹ , unit-l-ā ā unit-r-ā ā»Ā¹)

        Ī² : Natural ā§¼ F ā-ššš­ Ļā-ššš­ , F ā-ššš­ Ļā-ššš­ ā§½-ššš­ F
        Ī² = (Ī» _ -> id , id) since natural (Ī» f ā unit-l-ā ā unit-r-ā ā»Ā¹ , unit-l-ā ā unit-r-ā ā»Ā¹)

        P : isIso (hom Ī±)
        P = record
            { inverse-ā  = Ī²
            ; inv-r-ā    = componentwise $ Ī» _ -> unit-2-ā , unit-2-ā
            ; inv-l-ā    = componentwise $ Ī» _ -> unit-2-ā , unit-2-ā
            }


--------------------------------------------------------------
-- The 0-ary product, š

instance
  isCategory:š : isCategory (ā¤-š° {š})
  isCategory:š = isCategory:byId

ā¤-ššš­ : Category š
ā¤-ššš­ = ā²(Lift-Cat (š {āā}))ā²

intro-ā¤-ššš­ : ā{š : ššš­ š} -> Functor š (ā¤-ššš­ {š})
intro-ā¤-ššš­ = const (lift tt) since isFunctor:const

expand-ā¤-ššš­ : ā{š : ššš­ š} -> {F : Functor š (ā¤-ššš­ {š})} -> F ā intro-ā¤-ššš­
expand-ā¤-ššš­ {F = F} = Ī± since P
  where
    Ī± : Natural F intro-ā¤-ššš­
    Ī± = (Ī» _ -> incl isProp:ā¤-š°) since natural (Ī» _ ā ā„ isSet:ā¤-š°)

    Ī² : Natural intro-ā¤-ššš­ F
    Ī² = (Ī» _ -> incl isProp:ā¤-š°) since natural (Ī» _ ā ā„ isSet:ā¤-š°)

    P : isIso (hom Ī±)
    P = record
        { inverse-ā = Ī²
        ; inv-r-ā   = componentwise $ Ī» _ -> ā„ isSet:ā¤-š°
        ; inv-l-ā   = componentwise $ Ī» _ -> ā„ isSet:ā¤-š°
        }







