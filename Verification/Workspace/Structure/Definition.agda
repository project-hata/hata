
module Verification.Workspace.Structure.Definition where

open import Verification.Conventions


record _:&'_ (UU : ð° ð) {{U : hasU UU ð ð}} (P : UU -> ð° ð) : ð° (ð ï½¤ ð ï½¤ ð) where
  constructor make:&'
  field â¨_â© : getU U
  -- field overlap {{oldProof}} : getP U â¨_â©
  field oldProof' : getP U â¨_â©
  field of'_ : P (reconstruct U (â¨_â© , oldProof'))
  -- field {{of_}} : P (reconstruct U (â¨_â© , oldProof))
-- open _:&'_ {{...}} public hiding (â¨_â©)
-- open _:&'_ public using (â¨_â©)
open _:&'_ public

-- pattern â²_â² = â²_â²
infixl 30 _:&'_


record âi'_ {A : ð° ð} (B : A -> ð° ð) : ð° (ð ï½¤ ð) where
  constructor makeâi
  -- field overlap {{ifst}} : A
  field ifst : A
  -- field overlap {{isnd}} : B (ifst)
  field isnd : B (ifst)
open âi'_ public



instance
  hasU:&' : {UU : ð° ð} {{U : hasU UU ð ð}} {P : UU -> ð° ð} -> hasU (UU :&' P) _ _
  getU (hasU:&' {UU = A} {{U}}) = getU U
  getP (hasU:&' {UU = A} {{U}} {P = P}) a = âi' Î» (p1 : getP U a) -> P (reconstruct U (a , p1))
  reconstruct (hasU:&' {UU = A} {{U}} {P = P}) (a , pa) = make:&' a (pa .ifst) (pa .isnd)
  destructEl (hasU:&' {UU = A} â¦ U â¦ {P = P}) (make:&' a _ _) = a
  destructP (hasU:&' {UU = A} {{U}} {P = P}) (record { â¨_â© = a ; oldProof' = pmain ; of'_ = pof }) = makeâi pmain pof



