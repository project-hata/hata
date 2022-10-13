
module Verification.Workspace.Structure.Definition where

open import Verification.Conventions


record _:&'_ (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) : 𝒰 (𝑗 ､ 𝑘 ､ 𝑙) where
  constructor make:&'
  field ⟨_⟩ : getU U
  -- field overlap {{oldProof}} : getP U ⟨_⟩
  field oldProof' : getP U ⟨_⟩
  field of'_ : P (reconstruct U (⟨_⟩ , oldProof'))
  -- field {{of_}} : P (reconstruct U (⟨_⟩ , oldProof))
-- open _:&'_ {{...}} public hiding (⟨_⟩)
-- open _:&'_ public using (⟨_⟩)
open _:&'_ public

-- pattern ′_′ = ′_′
infixl 30 _:&'_


record ∑i'_ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor make∑i
  -- field overlap {{ifst}} : A
  field ifst : A
  -- field overlap {{isnd}} : B (ifst)
  field isnd : B (ifst)
open ∑i'_ public



instance
  hasU:&' : {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} {P : UU -> 𝒰 𝑗} -> hasU (UU :&' P) _ _
  getU (hasU:&' {UU = A} {{U}}) = getU U
  getP (hasU:&' {UU = A} {{U}} {P = P}) a = ∑i' λ (p1 : getP U a) -> P (reconstruct U (a , p1))
  reconstruct (hasU:&' {UU = A} {{U}} {P = P}) (a , pa) = make:&' a (pa .ifst) (pa .isnd)
  destructEl (hasU:&' {UU = A} ⦃ U ⦄ {P = P}) (make:&' a _ _) = a
  destructP (hasU:&' {UU = A} {{U}} {P = P}) (record { ⟨_⟩ = a ; oldProof' = pmain ; of'_ = pof }) = make∑i pmain pof



