
module Verification.Core.Category.Std.Functor.Representable where

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


record isIso-๐๐ญ๐ {a : Setoid ๐} {b : Setoid ๐} (f : SetoidHom a b) : ๐ฐ (๐ ๏ฝค ๐) where
  field inverse-๐๐ญ๐ : SetoidHom b a
        inv-r-โ-๐๐ญ๐ : (f โ-๐๐ญ๐ inverse-๐๐ญ๐) โผ id-๐๐ญ๐
        inv-l-โ-๐๐ญ๐ : (inverse-๐๐ญ๐ โ-๐๐ญ๐ f) โผ id-๐๐ญ๐
open isIso-๐๐ญ๐ {{...}} public

_โ-๐๐ญ๐_ : (A : Setoid ๐) (B : Setoid ๐) -> ๐ฐ (๐ ๏ฝค ๐)
A โ-๐๐ญ๐ B = (SetoidHom A B) :& isIso-๐๐ญ๐


-- module _ {๐ : ๐ฐ _} {{_ : Category ๐ on ๐}} where
-- module _ {๐ : Category ๐} where
module _ {๐ : ๐ฐ ๐} {{_ : isCategory ๐ ๐}} where

  [_,_]-๐๐ญ๐ : ๐ -> ๐ -> โจ ๐๐ญ๐ _ โฉ
  [ x , y ]-๐๐ญ๐ = โฒ x โถ y โฒ

  [_,_]๐ = [_,_]-๐๐ญ๐

[_,_]๐ = _โถ_
_โ๐_ = _โ-๐๐ญ๐_


-- module _ {๐ : Category ๐} where
module _ {๐ : ๐ฐ ๐} {{_ : isCategory ๐ ๐}} where
  instance
    isSetoidHom:map[,] : โ{a b c : ๐} -> {f : b โถ c} -> isSetoidHom [ a , b ]๐ [ a , c ]๐ (_โ f)
    isSetoidHom:map[,] {f = f} =
      record {
        preserves-โผ = ฮป p -> p โ refl
      }

  instance
    isFunctor:Homแตแต : โ{x : ๐} -> isFunctor (โฒ ๐ โฒ) (๐๐ญ๐ _) [ x ,_]-๐๐ญ๐
    isFunctor.map isFunctor:Homแตแต (f) = incl (โฒ (ฮป g -> g โ f) โฒ)
      -- where P : isSetoidHom _ _ (ฮป g -> g โ f)
      --       isSetoidHom.preserves-โผ P p = p โ refl
    isSetoidHom.preserves-โผ (isFunctor.isSetoidHom:map isFunctor:Homแตแต) p = incl (incl (refl โ p))
    isFunctor.functoriality-id isFunctor:Homแตแต = incl (incl (unit-r-โ))
    isFunctor.functoriality-โ isFunctor:Homแตแต = incl (incl assoc-r-โ)

  instance
    isSetoidHom:compose : โ{a b c : ๐} -> {f : a โถ b} -> isSetoidHom [ b , c ]๐ [ a , c ]๐ (f โ_)
    isSetoidHom:compose {f = f} = record { preserves-โผ = refl โ_ }

  instance
    isFunctor:Hom : โ{y : ๐} -> isFunctor (โฒ ๐ โฒ แตแต) (๐๐ญ๐ _) [_, y ]-๐๐ญ๐
    isFunctor.map isFunctor:Hom (incl f) = incl โฒ(incl f โ_)โฒ
    isSetoidHom.preserves-โผ (isFunctor.isSetoidHom:map isFunctor:Hom) (incl p) = incl (incl (incl p โ refl))
    isFunctor.functoriality-id isFunctor:Hom = incl (incl (unit-l-โ))
    isFunctor.functoriality-โ isFunctor:Hom = incl (incl assoc-l-โ)

module _ {๐ : Category ๐} where
  record isCorep (F : Functor ๐ (๐๐ญ๐ _)) (x : โจ ๐ โฉ) : ๐ฐ (๐ โบ) where
    field corep : F โ โฒ [ x ,_]๐ โฒ

  open isCorep {{...}} public
  Corep : (Functor ๐ (๐๐ญ๐ _)) -> ๐ฐ _
  Corep F = Structure (isCorep F)

module _ {๐ : Category ๐} where
  module _ {F : Functor (๐) (๐๐ญ๐ _)} {x : โจ ๐ โฉ} where

    ใแตแต : [ โฒ [ x ,_]๐ โฒ , F ]๐ โ๐ (โจ F โฉ x)
    ใแตแต = โฒ f โฒ {{Pโ}}
      where f : (โฒ [ x ,_]-๐๐ญ๐ โฒ) โถ F -> โจ (โจ F โฉ x) โฉ
            f ฮฑ = let ฮฑ' = โจ โจ โจ โจ ฮฑ โฉ โฉ {x} โฉ โฉ
                  in ฮฑ' id

            g : โจ โจ F โฉ x โฉ  ->  [ โฒ [ x ,_]๐ โฒ , F ]๐
            g a = let ฮฑ : โ{y} -> [ x , y ]๐  -> โจ โจ F โฉ y โฉ
                      ฮฑ f = โจ โจ map f โฉ โฉ a

                      instance
                        Pโ : โ{y} -> isSetoidHom [ x , y ]๐ (โจ F โฉ y) (ฮฑ {y})
                        Pโ {y} = record {
                          preserves-โผ = ฮป {f} {g} fโผg ->
                            let Pโ : map {{of F}} f โผ map {{of F}} g
                                Pโ = preserves-โผ fโผg
                            in โจ โจ Pโ โฉ โฉ {a}
                          }

                        Pโ : isNatural โฒ [ x ,_]๐ โฒ F (incl โฒ ฮฑ โฒ)
                        Pโ = record {
                          naturality = ฮป f -> incl (incl (ฮป {g} ->
                            let instance
                                  Pโ : โ{y} -> isSetoid _ โจ โจ F โฉ y โฉ
                                  Pโ {y} = of (โจ F โฉ y)
                                Pโ : โจ โจ map {{of F}} f โฉ โฉ (โจ โจ map {{of F}} g โฉ โฉ a) โผ โจ โจ map {{of F}} (g โ f) โฉ โฉ a
                                Pโ = โจ โจ functoriality-โ {{of F}} โปยน โฉ โฉ
                            in Pโ
                            ))
                          }
                  in incl โฒ (incl โฒ ฮฑ โฒ) โฒ

            instance
              Pโ : isSetoidHom (โฒ (โฒ [ x ,_]-๐๐ญ๐ โฒ) โถ F โฒ) (โจ F โฉ x) f
              isSetoidHom.preserves-โผ Pโ {a = a} {b} (incl p) = โจ โจ p {x} โฉ โฉ {id}

              Pโ : isSetoidHom _ _ g
              isSetoidHom.preserves-โผ Pโ (p) = incl (incl (incl (ฮป {f} -> preserves-โผ {{of โจ map {{of F}} f โฉ}} p)))
            Pโ : isIso-๐๐ญ๐ โฒ f โฒ
            isIso-๐๐ญ๐.inverse-๐๐ญ๐ Pโ = โฒ g โฒ
            isIso-๐๐ญ๐.inv-r-โ-๐๐ญ๐ Pโ = incl (ฮป {ฮฑ} -> incl (ฮป {x} -> incl (incl (ฮป {f} ->
                let Pโ : โจ โจ ฮฑ โฉ โฉ โ map {{of F}} f โผ incl โฒ(_โ f)โฒ โ โจ โจ ฮฑ โฉ โฉ
                    Pโ = naturality {{of โจ ฮฑ โฉ}} f
                    Pโ = โจ โจ Pโ โฉ โฉ {id}

                    instance
                      Pโ : isSetoid _ โจ โจ F โฉ x โฉ
                      Pโ = of (โจ F โฉ x)

                    instance
                      Pโ = isEquivRel:โผ {{Pโ}}

                    Pโ : โจ โจ โจ โจ ฮฑ โฉ โฉ โฉ โฉ (id โ f) โผ โจ โจ โจ โจ ฮฑ โฉ โฉ โฉ โฉ f
                    Pโ = preserves-โผ {{of โจ โจ โจ ฮฑ โฉ โฉ โฉ}} unit-l-โ

                in Pโ โ Pโ
              )) ))
            isIso-๐๐ญ๐.inv-l-โ-๐๐ญ๐ Pโ = incl (ฮป {a} -> โจ โจ functoriality-id โฉ โฉ)



-- {{isSetoidHom:map[,] {๐ = โจ ๐ โฉ}}}
{-
--   instance
--     isFunctor:Hom : โ{y : โจ ๐ โฉ} -> isFunctor (๐ แตแต) (๐๐ญ๐ _) [_, y ]-๐๐ญ๐
--     isFunctor.map isFunctor:Hom (incl f) = incl (โฒ (ฮป g -> incl f โ g) โฒ {{P}})
--       where P : isSetoidHom (ฮป g -> incl f โ g)
--             isSetoidHom.preserves-โผ P p = incl โจ refl {{isEquivRel:โผ {{isSetoid:Hom {{of ๐}}}}}} โฉ โ p
--             -- incl โจ (refl) {{of ๐ แตแต}} โฉ โ p
--     isSetoidHom.preserves-โผ (isFunctor.isSetoidHom:map isFunctor:Hom) (incl p) = incl (incl (ฮป {aโ} -> incl (sym p) โ ?))
--     isFunctor.functoriality-id isFunctor:Hom = {!!}
--     isFunctor.functoriality-โ isFunctor:Hom = {!!}

--   record isRepresentable (F : Functor (๐ แตแต) (๐๐ญ๐ _)) : ๐ฐ (๐ โบ) where
--     field Repr : โจ ๐ โฉ
--     field repr : F โ โฒ [_, Repr ]-๐๐ญ๐ โฒ

-- module _ {๐ : Category ๐} where
--   module _ {F : Functor (๐ แตแต) (๐๐ญ๐ _)} {x : โจ ๐ โฉ} where
--     X : Functor (๐ แตแต) (๐๐ญ๐ _)
--     X = โฒ [_, x ]-๐๐ญ๐ โฒ {{isFunctor:Hom {๐ = ๐} {y = x}}}

    -- ใ : โฒ (โฒ [_, x ]-๐๐ญ๐ โฒ {{isFunctor:Hom}}) โถ F โฒ โ-๐๐ญ๐ (โจ F โฉ x)
    -- ใ = {!!}



-}


