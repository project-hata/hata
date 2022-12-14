
module Verification.Core.Category.Std.Functor.Constant where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid

--------------------------------------------------------------
-- constant functor
module _ {๐ : Category ๐} {๐ : Category ๐} where
  isFunctor:const : {x : โจ ๐ โฉ} -> isFunctor ๐ ๐ (const x)
  isFunctor.map (isFunctor:const {x})              = const id
  isFunctor.isSetoidHom:map (isFunctor:const {x})  = record { cong-โผ = const refl }
  isFunctor.functoriality-id (isFunctor:const {x}) = refl
  isFunctor.functoriality-โ (isFunctor:const {x})  = unit-2-โ โปยน

  Const : (x : โจ ๐ โฉ) -> Functor ๐ ๐
  Const x = const x since isFunctor:const

module _ {C : ๐ฐ ๐} {{_ : isCategory {๐โ} C}} {D : ๐ฐ ๐} {{_ : isCategory {๐โ} D}} where
  private
    ๐ : Category _
    ๐ = โฒ C โฒ

    ๐ : Category _
    ๐ = โฒ D โฒ

  map-Const : โ{a b : D} -> a โถ b -> Const {๐ = ๐} {๐ = ๐} a โถ Const b
  map-Const f = (ฮป _ โ f) since natural (ฮป _ -> unit-r-โ โ unit-l-โ โปยน)

  instance
    isFunctor:Const : isFunctor ๐ (๐๐ฎ๐ง๐ ๐ ๐) (Const)
    isFunctor.map isFunctor:Const = map-Const
    isFunctor.isSetoidHom:map isFunctor:Const = {!!}
    isFunctor.functoriality-id isFunctor:Const = {!!}
    isFunctor.functoriality-โ isFunctor:Const = {!!}





--------------------------------------------------------------
-- definition via structureOn

-- this probably doesn't work because then the instance resolution
-- gets confused with other functors (since `const` is to un-unique as function)
{-
module _ {A : ๐ฐ ๐} {B : ๐ฐ ๐} where
  module _ (b : B) where
    ๐๐๐๐?๐กแต : A -> B
    ๐๐๐๐?๐กแต _ = b

    macro ๐๐๐๐?๐ก = #structureOn ๐๐๐๐?๐กแต

  module _ {{_ : isCategory {๐โ} A}} {{_ : isCategory {๐โ} B}} {b : B} where
    instance
      isFunctor:๐๐๐๐?๐ก : isFunctor โฒ A โฒ โฒ B โฒ (๐๐๐๐?๐ก b)
      isFunctor:๐๐๐๐?๐ก = isFunctor:const
-}







