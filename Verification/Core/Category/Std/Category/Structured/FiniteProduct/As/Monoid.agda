
module Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.Monoid where

open import Verification.Conventions
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition


module _ {š : š° _} {{_ : š is FiniteProductCategory š}} where

  private instance
    _ : isSetoid š
    _ = isSetoid:byCategory

    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:ā§¼ā§½

  private
    lem-1 : ā{a b : š} -> a ā b ā¼ b ā a
    lem-1 {a} {b} = f since P
      where
        f : a ā b ā¶ b ā a
        f = ā§¼ Ļā , Ļā ā§½

        g : b ā a ā¶ a ā b
        g = ā§¼ Ļā , Ļā ā§½

        Pā : f ā g ā¼ id
        Pā = f ā g                             āØ expand-Ļā,Ļā ā©-ā¼
             ā§¼ (f ā g) ā Ļā , (f ā g) ā Ļā ā§½   āØ cong-ā¼ (assoc-l-ā , assoc-l-ā) ā©-ā¼
             ā§¼ f ā (g ā Ļā) , f ā (g ā Ļā) ā§½   āØ cong-ā¼ (refl ā reduce-Ļā , refl ā reduce-Ļā) ā©-ā¼
             ā§¼ f ā Ļā , f ā Ļā ā§½               āØ cong-ā¼ (reduce-Ļā ā unit-l-ā ā»Ā¹ , reduce-Ļā ā unit-l-ā ā»Ā¹) ā©-ā¼
             ā§¼ id ā Ļā , id ā Ļā ā§½             āØ expand-Ļā,Ļā ā»Ā¹ ā©-ā¼
             id                                ā

        Pā : g ā f ā¼ id
        Pā = g ā f                             āØ expand-Ļā,Ļā ā©-ā¼
             ā§¼ (g ā f) ā Ļā , (g ā f) ā Ļā ā§½   āØ cong-ā¼ (assoc-l-ā , assoc-l-ā) ā©-ā¼
             ā§¼ g ā (f ā Ļā) , g ā (f ā Ļā) ā§½   āØ cong-ā¼ (refl ā reduce-Ļā , refl ā reduce-Ļā) ā©-ā¼
             ā§¼ g ā Ļā , g ā Ļā ā§½               āØ cong-ā¼ (reduce-Ļā ā unit-l-ā ā»Ā¹ , reduce-Ļā ā unit-l-ā ā»Ā¹) ā©-ā¼
             ā§¼ id ā Ļā , id ā Ļā ā§½             āØ expand-Ļā,Ļā ā»Ā¹ ā©-ā¼
             id                                ā

        P : isIso (hom f)
        P = record
            { inverse-ā = g
            ; inv-r-ā   = Pā
            ; inv-l-ā   = Pā
            }

    lem-2 : ā{a : š} -> ā¤ ā a ā¼ a
    lem-2 {a} = Ļā since P
      where
        g : a ā¶ ā¤ ā a
        g = ā§¼ intro-ā¤ , id ā§½

        Pā : Ļā ā g ā¼ id
        Pā = Ļā ā g                             āØ expand-Ļā,Ļā ā©-ā¼
             ā§¼ (Ļā ā g) ā Ļā , (Ļā ā g) ā Ļā ā§½  āØ cong-ā¼ (assoc-l-ā , assoc-l-ā) ā©-ā¼
             ā§¼ Ļā ā (g ā Ļā) , Ļā ā (g ā Ļā) ā§½  āØ cong-ā¼ (refl ā reduce-Ļā , refl ā reduce-Ļā ) ā©-ā¼
             ā§¼ Ļā ā intro-ā¤ , Ļā ā id ā§½         āØ cong-ā¼ (expand-ā¤ ā expand-ā¤ ā»Ā¹ ā unit-l-ā ā»Ā¹ , unit-r-ā ā unit-l-ā ā»Ā¹) ā©-ā¼
             ā§¼ id ā Ļā , id ā Ļā ā§½              āØ expand-Ļā,Ļā ā»Ā¹ ā©-ā¼
             id                                 ā

        P : isIso (hom Ļā)
        P = record
            { inverse-ā = g
            ; inv-r-ā   = Pā
            ; inv-l-ā   = reduce-Ļā
            }

    lem-3 : ā{a b c : š} -> (a ā b) ā c ā¼ a ā (b ā c)
    lem-3 {a} {b} {c} = f since P
      where
        f : (a ā b) ā c ā¶ a ā (b ā c)
        f = ā§¼ Ļā ā Ļā , ā§¼ Ļā ā Ļā , Ļā ā§½ ā§½

        g : a ā (b ā c) ā¶ (a ā b) ā c
        g = ā§¼ ā§¼ Ļā , Ļā ā Ļā ā§½ , Ļā ā Ļā ā§½


        P = record
            { inverse-ā = g
            ; inv-r-ā   = {!!}
            ; inv-l-ā   = {!!}
            }




  isMonoid:byHasFiniteProducts : isMonoid ā² š ā²
  isMonoid:byHasFiniteProducts = record
    { _ā_        = _ā_
    ; ā          = ā¤
    ; unit-l-ā   = lem-2
    ; unit-r-ā   = lem-1 ā lem-2
    ; assoc-l-ā  = lem-3
    ; _āāā_ = {!!}
    }



