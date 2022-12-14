
module Verification.Conventions.Meta2.Structure where

open import Verification.Conventions.Prelude hiding (â²_â²)
open import Verification.Conventions.Meta.Universe
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Order.Preorder renaming (IPreorder to isPreorder)

private
  variable ðâ : ð

record âi_ {A : ð° ð} (B : A -> ð° ð) : ð° (ð ï½¤ ð) where
  instance constructor makeâi
  -- field overlap {{ifst}} : A
  field {ifst} : A
  -- field overlap {{isnd}} : B (ifst)
  field {{isnd}} : B (ifst)
open âi_ {{...}} public


record hasU (A : ð° ð) ð ð : ð° (ð ï½¤ ð âº ï½¤ ð âº) where
  field getU : ð° ð
  field getP : getU -> ð° ð
  field reconstruct : â getP -> A
  field destructEl : A -> getU
  field destructP : (a : A) -> getP (destructEl a)
open hasU public


record _:&_ (UU : ð° ð) {{U : hasU UU ð ð}} (P : UU -> ð° ð) : ð° (ð ï½¤ ð ï½¤ ð) where
  constructor â²_â²
  field â¨_â© : getU U
  -- field overlap {{oldProof}} : getP U â¨_â©
  field {oldProof} : getP U â¨_â©
  field {{of_}} : P (reconstruct U (â¨_â© , oldProof))
  -- field {{of_}} : P (reconstruct U (â¨_â© , oldProof))
open _:&_ {{...}} public hiding (â¨_â©)
open _:&_ public using (â¨_â©)

-- pattern â²_â² = â²_â²
infixl 30 _:&_

module _ {UU : ð° ð} {{U : hasU UU ð ð}} {P : UU -> ð° ð} where
  â³_ : (UU :& P) -> UU
  â³_ val = (reconstruct U (â¨ val â© , oldProof {{_}} {{val}}))


-- El-:& : {UU : ð° ð} {{U : hasU UU ð ð}} {P : UU -> ð° ð}
--      -> UU :& P -> getU U
-- El-:& a = â¨ a â©

-- syntax El-:& a = âª a â«

{-
-- A test for getting a better syntax for casting, i.e., what we currently do with â² â¨ A â© â².
-- But it doesn't work because we have to use an intermediary type result `resType`
-- since we need to pattern-match on refl to get the proof that the two universes
-- of U and of U2 are the same.
-- But then at the call site the type `resType` does not match with the wanted
-- actual type `... :& ...`
resType : {UU : ð° ð} {{U : hasU UU ð ð}} (a : UU)
        -> (UU2 : ð° ðâ) {{U2 : hasU UU2 ð ðâ}} -> (P2 : UU2 -> ð° ðâ) -> (getU U â¡-Str getU U2) -> ð° _
resType {UU = UU} {{U}} a UU2 {{U2}} P2 refl-StrId =
        {{oldProof : getP U2 (destructEl U a)}}
        -> {{_ : P2 (reconstruct U2 (destructEl U a , oldProof))}}
        -> UU2 :& P2

% : {UU : ð° ð} {{U : hasU UU ð ð}} (a : UU)
  -> {UU2 : ð° ðâ} {{U2 : hasU UU2 ð ðâ}} {P2 : UU2 -> ð° ðâ}
     -> {{pp : (getU U â¡-Str getU U2)}}
     -> resType a UU2 P2 pp
% {UU = UU} {{U}} a {UU2} {{U2}} {P2} {{refl-StrId}} {{oldProof}} {{newProof}} = â² destructEl U a â²
-}

record _:>_ {UU : ð° ð} {{U : hasU UU ð ð}} (P : UU -> ð° ð) (Q : UU :& P -> ð° ðâ) (a : UU) : ð° (ð ï½¤ ðâ ï½¤ ð ï½¤ ð) where
  instance constructor make:>
  field {{Proof1>}} : P (reconstruct U (destructEl U a , destructP U a))
  field {{Proof2>}} : Q (â²_â² (destructEl U a) {destructP U a} {{Proof1>}})

open _:>_ {{...}} public

-- record _:&2_:â£_ (UU : ð° ð) {{U : hasU UU ð ð}} (P : UU -> ð° ð) (Q : UU -> ð° ðâ) : ð° (ð ï½¤ ðâ ï½¤ ð ï½¤ ð) where
--   constructor â²_â²2
--   field El : getU U
--   field overlap {{oldProof2}} : getP U El
--   field overlap {{Proof2-P}} : P (reconstruct U (El , oldProof2))
--   field overlap {{Proof2-Q}} : Q (reconstruct U (El , oldProof2))
-- open _:&2_:â£_ {{...}} public hiding (El)
-- open _:&2_:â£_ public using (El)

-- infixl 30 _:&2_:â£_

-- instance
--   ElPrev : (UU : ð° ð) {{U : hasU UU ð ð}} (P : UU -> ð° ð) -> 

record _:,_ {UU : ð° ð} {{U : hasU UU ð ð}} (P : UU -> ð° ð) (Q : UU -> ð° ðâ) (a : UU) : ð° (ð ï½¤ ðâ) where
  instance constructor make,
  field {{Proof1,}} : P a
  field {{Proof2,}} : Q a
open _:,_ {{...}} public

infixr 80 _:,_

record isAnything {A : ð° ð} (a : A) (ð : ð) : ð° (ð) where

instance
  isAnything:anything : {A : ð° ð} {a : A} {ð : ð} -> isAnything a ð
  isAnything:anything = record {}

-- instance
--   hasU:ð° : â{ð ð : ð} -> hasU (ð° ð) (ð âº) (ð âº â ð)
--   getU (hasU:ð° {ð}) = ð° ð
--   getP (hasU:ð° {ð} {ð = ð}) u = isAnything u ð

instance
  hasU:ð° : â{ð : ð} -> hasU (ð° ð) (ð âº) (ââ)
  getU (hasU:ð° {ð}) = ð° ð
  getP (hasU:ð° {ð}) u = isAnything u ââ
  reconstruct (hasU:ð° {ð}) (x , _) = x
  destructEl (hasU:ð° {ð}) a = a
  destructP (hasU:ð° {ð}) a = record {}

instance
  hasU:Exp : â{A : ð° ð} {B : ð° ð} -> hasU (A -> B) _ _
  getU (hasU:Exp {A = A} {B}) = A -> B
  getP (hasU:Exp {ð} {ð} {A = A} {B}) u = isAnything u (ââ)
  reconstruct (hasU:Exp {A = A} {B}) (x , _) = x
  destructEl (hasU:Exp {A = A} {B}) f = f
  destructP (hasU:Exp {A = A} {B}) _ = record {}

instance
  hasU:â : â{A : ð° ð} {B : A -> ð° ð} -> hasU (â{a} -> B a) _ _
  getU (hasU:â {A = A} {B}) = â{a} -> B a
  getP (hasU:â {ð} {ð} {A = A} {B}) u = isAnything {A = â{a} -> B a} u (ââ)
  reconstruct (hasU:â {A = A} {B}) (x , _) = x
  destructEl (hasU:â {A = A} {B}) f = f
  destructP (hasU:â {A = A} {B}) _ = record {}

hasU:Base : â(X : ð° ð) -> hasU X _ _
getU (hasU:Base X) = X
getP (hasU:Base X) u = isAnything u ââ
reconstruct (hasU:Base X) (x , _) = x
destructEl (hasU:Base X) a = a
destructP (hasU:Base X) a = record {}

-- instance
--   hasU:ExpFam : â{K : ð° ð} {A : K -> ð° ð} {B : K -> ð° ð} -> hasU (â{k : K} -> A k -> B k) _ _
--   getU (hasU:ExpFam {K = K}{A = A} {B}) = â{k : K} -> A k -> B k
--   getP (hasU:ExpFam {ð} {ð} {A = A} {B}) u = isAnything {A = â{k} -> A k -> B k} u (ââ)
--   reconstruct (hasU:ExpFam {A = A} {B}) (x , _) = x
--   destructEl (hasU:ExpFam {A = A} {B}) f = f
--   destructP (hasU:ExpFam {A = A} {B}) _ = record {}

instance
  hasU:& : {UU : ð° ð} {{U : hasU UU ð ð}} {P : UU -> ð° ð} -> hasU (UU :& P) _ _
  getU (hasU:& {UU = A} {{U}}) = getU U
  getP (hasU:& {UU = A} {{U}} {P = P}) a = âi Î» (p1 : getP U a) -> P (reconstruct U (a , p1))
  reconstruct (hasU:& {UU = A} {{U}} {P = P}) (a , pa) = â²_â² a {pa .ifst} {{pa .isnd}}
  destructEl (hasU:& {UU = A} â¦ U â¦ {P = P}) (â²_â² a) = a
  destructP (hasU:& {UU = A} {{U}} {P = P}) (record { â¨_â© = a ; oldProof = pmain ; of_ = pof }) = makeâi {ifst = pmain} {{pof}}
  -- makeâi -- {ifst = pold}

_on_ : (UU : ð° ð) {{U : hasU UU ð ð}} -> (a : getU U) -> ð° _
_on_ UU {{U}} a = getP U a

is-syntax : (UU : ð° ð) {{U : hasU UU ð ð}} -> (a : getU U) -> ð° _
is-syntax UU {{U}} a = getP U a

syntax is-syntax a b = b is a



--------------------------------------------------------------------
-- Allowing the subsumption of all structures under a single name

-- record hasStructure {A : ð° ð} (a : A) (UU : ð° ð) (U : hasU UU ð ð) : ð° ((ð âº) ï½¤ ð) where
--   constructor hasstructure
--   field isUniverseOf : A â¡-Str getU U
--   field isWithStructure : getP U (transport-Str (isUniverseOf) a)

-- instance
--   hasStructure:Structure : â{UU : ð° ð} {{U : hasU UU ð ð}} -> {a : getU U} -> {{_ : getP U a}} -> hasStructure {A = getU U} a UU U -- {{{!!}}}
--   hasStructure.isUniverseOf hasStructure:Structure = refl
--   hasStructure.isWithStructure (hasStructure:Structure {{U = U}} {{P}}) = P

---------------------------------------------------------------
-- Still not quite working
{-
record hasStructure {A : ð° ð} (a : A) (UU : ð° ð) ð : ð° ((ð âº) ï½¤ ð ï½¤ ð âº) where
  no-eta-equality
  pattern
  constructor hasstructure
  field myU : hasU UU ð ð
  field isUniverseOf : A â¡-Str getU myU
  field isWithStructure : getP myU (transport-Str (isUniverseOf) a)


instance
  -- hasStructure:Structure : â{UU : ð° ð} {{U : hasU UU ð ð}} -> â{A} -> {{pp : A â¡-Str getU U}} -> {a : A} -> {{P : getP U (transport-Str pp a)}} -> hasStructure {A = A} (a) UU ð -- {{{!!}}}
  hasStructure:Structure : â{UU : ð° ð} {{U : hasU UU ð ð}} -> {a : getU U} -> {{P : getP U a}} -> hasStructure {A = getU U} a UU ð
  hasStructure:Structure {{U = U}} {{P = P}} = hasstructure U refl P
  -- hasStructure.myU (hasStructure:Structure {{U = U}}) = U
  -- hasStructure.isUniverseOf (hasStructure:Structure) = refl
  -- -- hasStructure.isUniverseOf (hasStructure:Structure {{pp = pp}}) = pp
  -- hasStructure.isWithStructure (hasStructure:Structure {{U = U}} {{P = P}}) = P

-- structureOn : {A : ð° ð} (a : A) {UU : ð° ð} {U : hasU UU ð ð} -> {{pp : A â¡-Str getU U}} -> {{_ : hasStructure {A = A} a UU ð}} -> UU
structureOn : {A : ð° ð} (a : A) {UU : ð° ð} {{_ : hasStructure {A = A} a UU ð}} -> UU
structureOn {A = .(getU myU)} a {UU} â¦ hasstructure myU refl-StrId isWithStructure â¦ = reconstruct myU (a , isWithStructure)
-- structureOn {A = .(getU U)} a {UU} { U } â¦ hasstructure refl-StrId isWithStructure â¦ = reconstruct U (a , isWithStructure)

SomeStructure : {A : ð° ð} -> {a : A} -> ð°Ï
SomeStructure {A = A} {a = a} = â{ð ð} -> {UU : ð° ð} -> {{XX : hasStructure a UU ð}} -> UU

-- SomeStructure : {A : ð° ð} -> {a : A} -> ð°Ï
-- SomeStructure {A = A} {a = a} = â{ð} -> {UU : ð° ð} -> UU

AA : SomeStructure
AA {{XX = XX}} = structureOn â¤ {{XX}}
-- AA : SomeStructure
-- AA = structureOn â¤
-}

---------------------------------------------------------------
-- Still not quite working

{-

record hasStructure {ð ð : ð} {A : ð° ð} (a : A) (UU : ð° ð) : ð° ð where
  no-eta-equality
  pattern
  constructor hasstructure
  field myUU : UU
  -- field myU : hasU UU ð ð
  -- field isUniverseOf : A â¡-Str getU myU
  -- field isWithStructure : getP myU (transport-Str (isUniverseOf) a)


instance
  hasStructure:Structure : â{ð ð ð : ð} -> â{UU : ð° ð} {{U : hasU UU ð ð}} -> {a : getU U} -> {{P : getP U a}} -> hasStructure {A = getU U} a UU
  hasStructure:Structure {{U = U}} {a = a} {{P = P}} = hasstructure (reconstruct U (a , P))

structureOn : â{ð ð : ð} {A : ð° ð} (a : A) {UU : ð° ð} {{_ : hasStructure {A = A} a UU}} -> UU
structureOn a {UU = UU} {{hasstr}} = hasStructure.myUU hasstr

SomeStructure : â{ð : ð} {A : ð° ð} -> {a : A} -> ð°Ï
SomeStructure {A = A} {a = a} = â{ð} -> {UU : ð° ð} -> {{XX : hasStructure a UU}} -> UU


AA : SomeStructure
AA {{XX = XX}} = structureOn â¤ {{XX}}
-}

---------------------------------------------------------------
-- Now without middle man

-- record hasStructure {ð ð : ð} {A : ð° ð} (a : A) (UU : ð° ð) : ð° ð where
--   no-eta-equality
--   pattern
--   constructor hasstructure
--   field myUU : UU


-- instance
--   hasStructure:Structure : â{ð ð ð : ð} -> â{UU : ð° ð} {{U : hasU UU ð ð}} -> {a : getU U} -> {{P : getP U a}} -> hasStructure {A = getU U} a UU
--   hasStructure:Structure {{U = U}} {a = a} {{P = P}} = hasstructure (reconstruct U (a , P))

{-

structureOn : â{ð ð ð : ð} {A : ð° ð} (a : A) {UU : ð° ð} {{U : hasU UU ð ð}} {{pp : A â¡-Str getU U}} {{P : getP U (transport-Str pp a)}} -> UU
structureOn a {UU = UU} {{U}} {{refl-StrId}} {{P}} = reconstruct U (a , P)
-- hasStructure.myUU hasstr

SomeStructure : â{ð : ð} {A : ð° ð} -> {a : A} -> ð°Ï
SomeStructure {ð = ð} {A = A} {a = a} = â{ð ð} -> {UU : ð° ð} -> {{U : hasU UU ð ð}} {{pp : A â¡-Str getU U}} {{P : getP U (transport-Str pp a)}} -> UU

-- SomeStructure : â{ð : ð} {A : ð° ð} -> {a : A} -> ð°Ï
-- SomeStructure {A = A} {a = a} = â{ð} -> {UU : ð° ð} -> {{XX : hasStructure a UU}} -> UU


AA : SomeStructure
AA = structureOn â¤
-}


---------------------------------------------------------------
-- And here only for :&


{-
structureOn' : â{ð ð ð ð} -> {A : ð° ð} -> (a : A) -> {UU : ð° ð} {{U : hasU UU ð ð}} {P : UU -> ð° ð} -> {{pp : A â¡-Str getU U}}
               -> {oldP : getP U (transport-Str pp a)} -> {{ofP : P (reconstruct U (transport-Str pp a , oldP))}}
               -> UU :& P
structureOn' a {{pp = pp}} = â² transport-Str pp a â²


SomeStructure' : â{ð : ð} {A : ð° ð} -> {a : A} -> ð°Ï
SomeStructure' {ð = ð} {A = A} {a = a} = â{ð ð ð} -> {UU : ð° ð} {{U : hasU UU ð ð}} {P : UU -> ð° ð} -> {{pp : A â¡-Str getU U}}
               -> {oldP : getP U (transport-Str pp a)} -> {{ofP : P (reconstruct U (transport-Str pp a , oldP))}}
               -> UU :& P

BB : SomeStructure'
BB = structureOn' â¤

-- pattern CCC = â² â¤ â²

-}
