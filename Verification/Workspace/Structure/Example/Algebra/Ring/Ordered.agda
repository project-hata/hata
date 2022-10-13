
module Verification.Workspace.Structure.Example.Algebra.Ring.Ordered where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Workspace.Structure.Example.Algebra.Monoid.Definition
open import Verification.Workspace.Structure.Example.Algebra.Group.Definition
open import Verification.Workspace.Structure.Example.Algebra.Abelian.Definition
open import Verification.Workspace.Structure.Example.Algebra.Ring.Definition
-- open import Verification.Core.Algebra.Ring.Domain
open import Verification.Core.Order.Linearorder

open import Verification.Workspace.Structure.Definition2

module _ {𝑖 : 𝔏 ^ 2} where
  record isOrderedRing (𝑗 : 𝔏) (R : Ring' 𝑖)  : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where

    private instance
      _ : isRing _
      _ = (isnd R)

      _ : isCommutative _
      _ = Proof2, (isnd (ifst R))

      _ : isMonoid _
      _ = isnd (ifst (ifst R))

      _ : isSetoid _
      _ = isnd (ifst (ifst (ifst R)))

    field {{OProof}} : isLinearorder 𝑗 (′ El R ′)
    field stronglyMonotone-l-⋆ : ∀{a b : El R} -> a < b -> ∀ {c} -> a ⋆ c < b ⋆ c
          preservesPositivity-⋅ : ∀{a b : El R} -> ◌ < a -> ◌ < b -> ◌ < a ⋅ b

  open isOrderedRing {{...}} public

module _ (𝑖 : 𝔏 ^ 3) where
  OrderedRing' = Ring' (𝑖 ⌄ 0 ⋯ 1) :&' isOrderedRing (𝑖 ⌄ 2)

record isOrderedRing# {𝑗 : 𝔏 ^ 3} (This : 𝒰 (𝑗 ⌄ 0)) : 𝒰 (𝑗 ⁺) where
  instance constructor makeIsOrderedRing#
  field {{isSetoid:This}} : isSetoid {𝑗 ⌄ 1} This
  field {{isMonoid:This}} : isMonoid (make:&' This isSetoid:This)
  field {{isGroup:This}}  : isGroup (make:&' (make:&' This isSetoid:This) isMonoid:This)
  field {{isCommutative:This}}  : isCommutative ((make:&' (make:&' This isSetoid:This) isMonoid:This))
  field {{isRing:This}}    : isRing (make:&' ((make:&' (make:&' This isSetoid:This) isMonoid:This)) (make, isGroup:This isCommutative:This))
  field {{isOrderedRing:This}}    : isOrderedRing (𝑗 ⌄ 2) (make:&' (make:&' ((make:&' (make:&' This isSetoid:This) isMonoid:This)) (make, isGroup:This isCommutative:This)) isRing:This)

open isOrderedRing# public

module _ 𝑗 where
  OrderedRing = _ :& isOrderedRing# {𝑗}


{-
module _ {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} where
  module _ {R : 𝒰 _} {_ : Ring 𝑖 on R} {{_ : isOrderedRing 𝑗 ′ R ′}} where

    stronglyMonotone-r-⋆ : ∀{c} -> ∀{a b : R} -> (a < b) -> c ⋆ a < c ⋆ b
    stronglyMonotone-r-⋆ {c} {a} {b} p =
      c ⋆ a   ⟨ comm-⋆ ⟩-∼-<
      a ⋆ c   ⟨ stronglyMonotone-l-⋆ p ⟩-<-∼
      b ⋆ c   ⟨ comm-⋆ ⟩-∼
      c ⋆ b   ∎

    stronglyMonotone-l-⋅ : ∀{a b c : R} -> a < b -> (◌ < c) -> a ⋅ c < b ⋅ c
    stronglyMonotone-l-⋅ {a} {b} {c} p q = P₂
      where
          P₀ = ◌       ⟨ inv-r-⋆ ⁻¹ ⟩-∼-<
              a ⋆ ◡ a  ⟨ stronglyMonotone-l-⋆ p ⟩-<-∼
              b ⋆ ◡ a  ∎-∼

          P₁ = ◌                ⟨ preservesPositivity-⋅ P₀ q ⟩-<-∼
               (b ⋆ ◡ a) ⋅ c    ⟨ distr-r-⋅ ⟩-∼
               b ⋅ c ⋆ ◡ a ⋅ c  ∎-∼

          P₂ = a ⋅ c                      ⟨ unit-l-⋆ ⁻¹ ⟩-∼-<
               ◌ ⋆ a ⋅ c                  ⟨ stronglyMonotone-l-⋆ P₁ ⟩-<-∼
               (b ⋅ c ⋆ ◡ a ⋅ c) ⋆ a ⋅ c   ⟨ assoc-l-⋆ ⟩-∼
               b ⋅ c ⋆ (◡ a ⋅ c ⋆ a ⋅ c)   ⟨ refl ≀⋆≀ (switch-◡-⋅-l ⁻¹ ≀⋆≀ refl) ⟩-∼
               b ⋅ c ⋆ (◡(a ⋅ c) ⋆ a ⋅ c)  ⟨ refl ≀⋆≀ inv-l-⋆ ⟩-∼
               b ⋅ c ⋆ ◌                  ⟨ unit-r-⋆ ⟩-∼
               b ⋅ c                      ∎



  isPositive : {R : 𝒰 _} {{_ : Ring 𝑖 on R}} {{_ : isOrderedRing 𝑗 ′ R ′}} -> R -> 𝒰 _
  isPositive a = ◌ < a

-}


{-
  module _ {R : Ring 𝑖}
           {{_ : isOrderedRing 𝑗 R}} where

    cancel-⋅-<-r : ∀{a b c : El R} -> a ⋅ c < b ⋅ c -> isPositive c -> a < b
    cancel-⋅-<-r = {!!}

-}

{-
    -- NOTE: We do not make this an instance, since not every domain structures comes from an ordered ring structure.
    isDomain:OrderedRing : isDomain R
    isDomain.domain isDomain:OrderedRing = {!!}
-}


{-








{-
  record isDecidable-OrderedRing (R : Ring 𝑖 :& isOrderedRing 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
    field overlap {{DecOProof}} : (isTotalorder :> isDecidable-Totalorder) ′ El R ′

-- module _ {𝑖 : 𝔏 ^ 2} {𝑗 : \}
  module _ (R : Ring 𝑖) {{_ : isOrderedRing 𝑗 R}} {{_ : isDecidable-OrderedRing ′ El R ′}} where

    -- isPositive-⨡ : isPositive ⨡
    -- isPositive-⨡ with compare ◌ ⨡
    -- ... | LT x = {!!}
    -- ... | EQ x = transp-< {!!} {!!} refl-<
    -- ... | GT x = {!!}

-}
-}

