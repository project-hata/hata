
module Verification.Workspace.Structure.Definition2 where

open import Verification.Conventions

record hasU2 (A : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field getU : 𝒰 𝑗
  -- field getP : getU -> 𝒰 𝑘
  -- field reconstruct : ∑ getP -> A
  field destructEl : A -> getU

open hasU2 public

-- record _:&'_ {𝑘 𝑙} (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ⁺ ､ 𝑙 ⁺) where

record _:&'_ (UU : 𝒰 𝑖) {{U : hasU2 UU 𝑘}} (P : UU -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor make:&'
  -- field overlap {{ifst}} : A
  field ifst : UU
  -- field {{hasU:ifst}} : hasU A 𝑘 𝑙
  -- field overlap {{isnd}} : B (ifst)
  field isnd : P (ifst)
open _:&'_ public

El : {UU : 𝒰 𝑖} {{U : hasU2 UU 𝑘}} -> UU -> getU U
El {UU = UU} {{U}} A = destructEl U A


-- record _:&'_ (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) : 𝒰 (𝑗 ､ 𝑘 ､ 𝑙) where
--   constructor make:&'
--   field ⟨_⟩ : getU U
--   -- field overlap {{oldProof}} : getP U ⟨_⟩
--   field oldProof' : getP U ⟨_⟩
--   field of'_ : P (reconstruct U (⟨_⟩ , oldProof'))
--   -- field {{of_}} : P (reconstruct U (⟨_⟩ , oldProof))
-- -- open _:&'_ {{...}} public hiding (⟨_⟩)
-- -- open _:&'_ public using (⟨_⟩)
-- open _:&'_ public

-- pattern ′_′ = ′_′
infixl 30 _:&'_

record ∑i'_ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor make∑i
  -- field overlap {{ifst}} : A
  field ifst : A
  -- field overlap {{isnd}} : B (ifst)
  field isnd : B (ifst)
open ∑i'_ public

record _:,'_ {UU : 𝒰 𝑖} {{U : hasU2 UU 𝑘}} (P : UU -> 𝒰 𝑗) (Q : UU -> 𝒰 𝑗₂) (a : UU) : 𝒰 (𝑗 ､ 𝑗₂) where
  constructor make,
  field Proof1, : P a
  field Proof2, : Q a
open _:,'_ public

infixr 80 _:,'_

{-
record _:>'_ {UU : 𝒰 𝑖} {{U : hasU2 UU 𝑘}} (P : UU -> 𝒰 𝑗) (Q : UU :&' P -> 𝒰 𝑗₂) (a : UU) : 𝒰 (𝑗 ､ 𝑗₂ ､ 𝑘) where
  constructor make:>'
  field Proof1> : P (reconstruct U (destructEl U a , destructP U a))
  field Proof2> : Q (′_′ (destructEl U a) {destructP U a} {{Proof1>}})

open _:>'_ public
-}


instance
  hasU:&' : {UU : 𝒰 𝑖} {{U : hasU2 UU 𝑘}} {P : UU -> 𝒰 𝑗} -> hasU2 (UU :&' P) _
  getU (hasU:&' {UU = A} {{U}}) = getU U
  -- getP (hasU:&' {UU = A} {{U}} {P = P}) a = ∑i' λ (p1 : getP U a) -> P (reconstruct U (a , p1))
  -- reconstruct (hasU:&' {UU = A} {{U}} {P = P}) (a , pa) = {!!} -- make:&' a (pa .ifst) (pa .isnd)
  destructEl (hasU:&' {UU = A} ⦃ U ⦄ {P = P}) (make:&' a _) = El a
  -- destructP (hasU:&' {UU = A} {{U}} {P = P}) _ = {!!}
  -- (record { ⟨_⟩ = a ; oldProof' = pmain ; of'_ = pof }) = make∑i pmain pof


instance
  hasU2:𝒰 : ∀{𝑖 : 𝔏} -> hasU2 (𝒰 𝑖) (𝑖 ⁺)
  getU (hasU2:𝒰 {𝑖}) = 𝒰 𝑖
  destructEl (hasU2:𝒰 {𝑖}) a = a
