
module Verification.Workspace.Structure.Definition2 where

open import Verification.Conventions

record hasU2 (A : ð° ð) ð : ð° (ð ï½¤ ð âº) where
  field getU : ð° ð
  -- field getP : getU -> ð° ð
  -- field reconstruct : â getP -> A
  field destructEl : A -> getU

open hasU2 public

-- record _:&'_ {ð ð} (A : ð° ð) (B : A -> ð° ð) : ð° (ð ï½¤ ð ï½¤ ð âº ï½¤ ð âº) where

record _:&'_ (UU : ð° ð) {{U : hasU2 UU ð}} (P : UU -> ð° ð) : ð° (ð ï½¤ ð) where
  constructor make:&'
  -- field overlap {{ifst}} : A
  field ifst : UU
  -- field {{hasU:ifst}} : hasU A ð ð
  -- field overlap {{isnd}} : B (ifst)
  field isnd : P (ifst)
open _:&'_ public

El : {UU : ð° ð} {{U : hasU2 UU ð}} -> UU -> getU U
El {UU = UU} {{U}} A = destructEl U A


-- record _:&'_ (UU : ð° ð) {{U : hasU UU ð ð}} (P : UU -> ð° ð) : ð° (ð ï½¤ ð ï½¤ ð) where
--   constructor make:&'
--   field â¨_â© : getU U
--   -- field overlap {{oldProof}} : getP U â¨_â©
--   field oldProof' : getP U â¨_â©
--   field of'_ : P (reconstruct U (â¨_â© , oldProof'))
--   -- field {{of_}} : P (reconstruct U (â¨_â© , oldProof))
-- -- open _:&'_ {{...}} public hiding (â¨_â©)
-- -- open _:&'_ public using (â¨_â©)
-- open _:&'_ public

-- pattern â²_â² = â²_â²
infixl 30 _:&'_

record âi'_ {A : ð° ð} (B : A -> ð° ð) : ð° (ð ï½¤ ð) where
  constructor makeâi
  -- field overlap {{ifst}} : A
  field ifst : A
  -- field overlap {{isnd}} : B (ifst)
  field isnd : B (ifst)
open âi'_ public

record _:,'_ {UU : ð° ð} {{U : hasU2 UU ð}} (P : UU -> ð° ð) (Q : UU -> ð° ðâ) (a : UU) : ð° (ð ï½¤ ðâ) where
  constructor make,
  field Proof1, : P a
  field Proof2, : Q a
open _:,'_ public

infixr 80 _:,'_

{-
record _:>'_ {UU : ð° ð} {{U : hasU2 UU ð}} (P : UU -> ð° ð) (Q : UU :&' P -> ð° ðâ) (a : UU) : ð° (ð ï½¤ ðâ ï½¤ ð) where
  constructor make:>'
  field Proof1> : P (reconstruct U (destructEl U a , destructP U a))
  field Proof2> : Q (â²_â² (destructEl U a) {destructP U a} {{Proof1>}})

open _:>'_ public
-}


instance
  hasU:&' : {UU : ð° ð} {{U : hasU2 UU ð}} {P : UU -> ð° ð} -> hasU2 (UU :&' P) _
  getU (hasU:&' {UU = A} {{U}}) = getU U
  -- getP (hasU:&' {UU = A} {{U}} {P = P}) a = âi' Î» (p1 : getP U a) -> P (reconstruct U (a , p1))
  -- reconstruct (hasU:&' {UU = A} {{U}} {P = P}) (a , pa) = {!!} -- make:&' a (pa .ifst) (pa .isnd)
  destructEl (hasU:&' {UU = A} â¦ U â¦ {P = P}) (make:&' a _) = El a
  -- destructP (hasU:&' {UU = A} {{U}} {P = P}) _ = {!!}
  -- (record { â¨_â© = a ; oldProof' = pmain ; of'_ = pof }) = makeâi pmain pof


instance
  hasU2:ð° : â{ð : ð} -> hasU2 (ð° ð) (ð âº)
  getU (hasU2:ð° {ð}) = ð° ð
  destructEl (hasU2:ð° {ð}) a = a
