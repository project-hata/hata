
module Verification.Core.Category.Std.Fibration.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Pullback

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category

--
-- The definition of (Grothendieck) fibrations
-- (following the definition at https://ncatlab.org/nlab/show/Grothendieck+fibration)
--

-- congβ-Str : β{A : π° π} {B : π° π} {C : π° π} -> (f : A -> B -> C) -> {a1 a2 : A} -> {b1 b2 : B} -> (p : a1 β£ a2) -> (q : b1 β£ b2) -> f a1 b1 β£ f a2 b2
-- congβ-Str f refl-StrId refl-StrId = refl-StrId

-- private variable
  -- β¬ : Category π
  -- β° : Category π
  -- e eβ eβ eβ : β¨ β° β©


-- module _  where
-- record FullSubsetoid (X : Setoid π) (Ο : β¨ X β© -> π° π) : π° π where
--   field 


-- β (a b : A) -> a βΌ b



module _ (β° : Category π) (β¬ : Category π) where
  module _ (p : Functor β° β¬) where

    module _ {eβ eβ eβ} (Ο : eβ βΆ eβ) (Ο : eβ βΆ eβ) (g : β¨ p β© eβ βΆ β¨ p β© eβ) (p : g β map Ο βΌ map Ο) where

      record isCartesianLift (Ο : Hom' {π = β°} eβ eβ) : π° (π ο½€ π) where
        field cartesianLiftFills : (β¨ Ο β© β Ο) βΌ Ο
        field cartesianLiftSection : map β¨ Ο β© βΌ g

      CartesianLift = _ :& isCartesianLift

    module _ {eβ eβ eβ} {Ο : eβ βΆ eβ} {Ο : eβ βΆ eβ} {g : β¨ p β© eβ βΆ β¨ p β© eβ} {p : g β map Ο βΌ map Ο} where
      instance
        isSetoid:CartesianLift : isSetoid (CartesianLift Ο Ο g p)
        isSetoid:CartesianLift = isSetoid:FullSubsetoid β²(eβ βΆ eβ)β² β¨_β©

    record isCartesian {eβ eβ : β¨ β° β©} (Ο : Hom' {π = β°} eβ eβ) : π° (π ο½€ π) where
      field uniqueCartesianLift : β{eβ} (Ο : eβ βΆ eβ) (g : β¨ p β© eβ βΆ β¨ p β© eβ) (p : g β map β¨ Ο β© βΌ map Ο) -> isContr-Std (CartesianLift β¨ Ο β© Ο g p)

    Cartesian : β(eβ eβ : β¨ β° β©) -> π° _
    Cartesian eβ eβ = _ :& isCartesian {eβ} {eβ}

  record isFibrationalLift (p : Functor β° β¬) {e b} (f : b βΆ β¨ p β© e) {e'} (Ο : Cartesian p e' e) : π° π where
    field fibrationalLiftObjectSection : β¨ p β© e' β‘ b
    field fibrationalLiftHomSection : transport (Ξ» i -> fibrationalLiftObjectSection i βΆ β¨ p β© e) (map β¨ Ο β©) βΌ f

  record isFibration (p : Functor β° β¬) : π° (π ο½€ π) where
    field liftCartesian : β{e : β¨ β° β©} {b : β¨ β¬ β©} (f : b βΆ β¨ p β© e) -> β Ξ» e' -> β Ξ» (Ο : Cartesian p e' e) -> isFibrationalLift p f Ο

  Fibration = _ :& isFibration

module _ {π : π° π} {{_ : isCategory {π} π}} where
  pid : {a b : π} -> (a β£ b) -> a β b
  pid refl-StrId = refl {{isSetoid:byCategory}}
  -- β¨ refl {{isEquivRel:β}} β©


module _ {β° : Category π} {β¬ : Category π} where

  module _ (p : Fibration β° β¬) (b : β¨ β¬ β©) where
    record isFiber (e : Obj β°) : π° (π ο½€ π) where
      constructor isfiber
      field isSectionFiber : β¨ p β© β¨ e β© β£ b

    open isFiber public

    Fiber = _ :& isFiber

  instance
    isFiber:Refl : β{p : Fibration β° β¬} {e : β¨ β° β©} -> isFiber p (β¨ p β© e) (obj e)
    isFiber:Refl = isfiber refl-β£

  module _ {p : Fibration β° β¬} {b : β¨ β¬ β©} where

    private
      p' : Functor β° β¬
      p' = β² β¨ p β© β²

      record isFiberHom (eβ eβ : Fiber p b) (Ο : Hom' {π = β°} β¨ eβ β© β¨ eβ β©) : π° (π ο½€ π) where
        constructor isfiberhom
        field isSectionFiberHom : β¨ sym-β (pid (isSectionFiber (of eβ))) β© β (map {{of p'}} β¨ Ο β©) β β¨ pid (isSectionFiber (of eβ)) β© βΌ id

      open isFiberHom {{...}} public

      FiberHom : β(eβ eβ : Fiber p b) -> π° _
      FiberHom eβ eβ = _ :& isFiberHom eβ eβ

      -- FiberHom : β(eβ eβ : Fiber p b) -> π° _
      -- FiberHom eβ eβ = β Ξ» (Ο : β¨ eβ β© βΆ β¨ eβ β©) -> β¨ iso-inv (pid (isSectionFiber (of eβ))) β© β (map {{of p'}} Ο) β β¨ pid (isSectionFiber (of eβ)) β© βΌ id

      -- FiberHom : β(eβ eβ : Fiber p b) -> π° _
      -- FiberHom eβ eβ = β Ξ» (Ο : β¨ eβ β© βΆ β¨ eβ β©) -> β¨ iso-inv (pid (isSectionFiber (of eβ))) β© β (map {{of p'}} Ο) β β¨ pid (isSectionFiber (of eβ)) β© βΌ id

      -- transport-Str (congβ-Str (_βΆ_) (isSectionFiber (of eβ)) (isSectionFiber (of eβ))) (map {{of p'}} Ο) βΌ id

      -- (Ξ» i -> isSectionFiber (of eβ) i βΆ isSectionFiber (of eβ) i) (map {{of p'}} Ο) βΌ id
      -- FiberHom eβ eβ = β Ξ» (Ο : β¨ eβ β© βΆ β¨ eβ β©) -> transport (Ξ» i -> isSectionFiber (of eβ) i βΆ isSectionFiber (of eβ) i) (map {{of p'}} Ο) βΌ id

      instance
        isSetoid:FiberHom : β{eβ eβ} -> isSetoid (FiberHom eβ eβ)
        isSetoid:FiberHom {eβ} {eβ} = isSetoid:FullSubsetoid (β² β¨ eβ β© βΆ β¨ eβ β© β²) β¨_β©



        -- isSetoid:Hom-Base {{isSetoid:FullSubsetoid (β² β¨ eβ β© βΆ β¨ eβ β© β²) β¨_β©}}

      id-Fiber : β{e : Fiber p b} -> FiberHom e e
      id-Fiber {e} = id since isfiberhom {!!} -- P
        -- where P : _ β map id β _ βΌ id
        --       P = _ β map id β _     β¨ refl β functoriality-id β refl β©-βΌ
        --           _ β id β _         β¨ unit-r-β β refl β©-βΌ
        --           _ β _              β¨ inv-l-β (of (pid (isSectionFiber (of e)))) β©-βΌ
        --           id {{of β°}}                 β

      comp-Fiber : β{e f g : Fiber p b} -> FiberHom e f -> FiberHom f g -> FiberHom e g
      comp-Fiber {β² e β²} {f} {β² g β²} (Ο') (Ο') = Ο β Ο since isfiberhom {!!} -- P
        where Ξ² = pid (isSectionFiber (of f))
              Ο = β¨ Ο' β©
              Ο = β¨ Ο' β©

              -- P : (_ β map (Ο β Ο) β _) βΌ id
              -- P = _ β map (Ο β Ο) β _                 β¨ refl β functoriality-β β refl β©-βΌ
              --     _ β (map Ο β map Ο) β _             β¨ refl β (unit-r-β β»ΒΉ β refl) β refl  β©-βΌ
              --     _ β (map Ο β id β map Ο) β _        β¨ refl β (refl β inv-r-β (of Ξ²) β»ΒΉ β refl) β refl β©-βΌ
              --     _ β (map Ο β (_ β _) β map Ο) β _   β¨ refl β (assoc-r-β β refl) β refl β©-βΌ
              --     _ β ((map Ο β _) β _ β map Ο) β _   β¨ refl β (assoc-l-β) β refl β©-βΌ
              --     _ β ((map Ο β _) β (_ β map Ο)) β _ β¨ assoc-r-β β refl β©-βΌ
              --     (_ β (map Ο β _)) β (_ β map Ο) β _ β¨ (assoc-r-β β isSectionFiberHom {{of Ο'}}) β refl β refl β©-βΌ
              --     id β (_ β map Ο) β _                β¨ unit-l-β β refl β©-βΌ
              --     (_ β map Ο) β _                     β¨ isSectionFiberHom {{of Ο'}} β©-βΌ
              --     id                      β

    instance
      isCategory:Fiber : isCategory (Fiber p b)
      isCategory.Hom isCategory:Fiber = FiberHom
      isCategory.isSetoid:Hom isCategory:Fiber = it
      isCategory.id isCategory:Fiber {e}    = (id-Fiber {e})
      isCategory._β_ isCategory:Fiber Ο Ο   = (comp-Fiber Ο Ο)
      isCategory.unit-l-β isCategory:Fiber  = incl unit-l-β
      isCategory.unit-r-β isCategory:Fiber  = incl unit-r-β
      isCategory.unit-2-β isCategory:Fiber  = incl unit-2-β
      isCategory.assoc-l-β isCategory:Fiber = incl assoc-l-β
      isCategory.assoc-r-β isCategory:Fiber = incl assoc-r-β
      isCategory._β_ isCategory:Fiber = {!!}

  FiberF : (p : Fibration β° β¬) -> Functor (β¬ α΅α΅) (πππ­ _)
  FiberF p = F since it
    where
      F : β¨ β¬ β© -> Category _
      F b = β² Fiber p b β²

      Ff : β{a b : β¨ β¬ β©} (f : a βΆ b) -> Fiber p b -> Fiber p a
      Ff f e = {!!}

      instance
        isFunctor:F : isFunctor (β¬ α΅α΅) (πππ­ _) F
        isFunctor.map isFunctor:F = Ξ» x β {!!}
        isFunctor.isSetoidHom:map isFunctor:F = {!!}
        isFunctor.functoriality-id isFunctor:F = {!!}
        isFunctor.functoriality-β isFunctor:F = {!!}

{-

-}
