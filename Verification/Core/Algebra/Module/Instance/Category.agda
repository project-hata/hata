
module Verification.Core.Algebra.Module.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Abelian.Instance.Category
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Module.Definition
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Category.Opposite



_-𝐌𝐨𝐝ᵘ : ∀{𝑖} -> (_ : Ring 𝑖 ×-𝒰 𝔏 ^ 2) -> 𝒰 _
_-𝐌𝐨𝐝ᵘ (R , 𝑗) = Module R 𝑗

macro
  _-𝐌𝐨𝐝 : ∀{𝑖} -> (_ : Ring 𝑖 ×-𝒰 𝔏 ^ 2) -> _
  _-𝐌𝐨𝐝 (R , 𝑗) = #structureOn ((R , 𝑗)-𝐌𝐨𝐝ᵘ)


module _ {R : Ring 𝑖} where
  record isModuleHom (A B : (R , 𝑗)-𝐌𝐨𝐝) (f : AbelianHom (↳ A) (↳ B) ) : 𝒰 (𝑖 ､ 𝑗) where
    field preserve-↷ : ∀{m : ⟨ R ⟩} {a : ⟨ A ⟩} -> ⟨ f ⟩ (m ↷ a) ∼ m ↷ ⟨ f ⟩ a

  module _ (A B : (R , 𝑗)-𝐌𝐨𝐝) where
    ModuleHom = _ :& isModuleHom A B

  module _ {A B : (R , 𝑗)-𝐌𝐨𝐝} where
    record _∼-ModuleHom_ (f g : ModuleHom A B) : 𝒰 (𝑖 ､ 𝑗) where
      constructor incl
      field ⟨_⟩ : ⟨ f ⟩ ∼ ⟨ g ⟩

    instance
      isSetoid:ModuleHom : isSetoid (ModuleHom A B)
      isSetoid:ModuleHom = isSetoid:byDef _∼-ModuleHom_ (incl refl) {!!} {!!}

  instance
    isCategory:-𝐌𝐨𝐝 : isCategory ((R , 𝑗)-𝐌𝐨𝐝)
    isCategory.Hom isCategory:-𝐌𝐨𝐝 = ModuleHom
    isCategory.isSetoid:Hom isCategory:-𝐌𝐨𝐝 = it
    isCategory.id isCategory:-𝐌𝐨𝐝 = {!!}
    isCategory._◆_ isCategory:-𝐌𝐨𝐝 = {!!}
    isCategory.unit-l-◆ isCategory:-𝐌𝐨𝐝 = {!!}
    isCategory.unit-r-◆ isCategory:-𝐌𝐨𝐝 = {!!}
    isCategory.unit-2-◆ isCategory:-𝐌𝐨𝐝 = {!!}
    isCategory.assoc-l-◆ isCategory:-𝐌𝐨𝐝 = {!!}
    isCategory.assoc-r-◆ isCategory:-𝐌𝐨𝐝 = {!!}
    isCategory._◈_ isCategory:-𝐌𝐨𝐝 = {!!}


