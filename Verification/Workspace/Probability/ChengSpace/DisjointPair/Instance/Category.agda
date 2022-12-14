
module Verification.Workspace.Probability.ChengSpace.DisjointPair.Instance.Category where

open import Verification.Conventions
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Imports
open import Verification.Workspace.Probability.ChengSpace.DisjointPair.Definition


module _ {ð : DCLC ð} where
  record Hom-ðð¢ð¬ððð¢ð« (a b : DisjointPair ð) : ð° ð where
    constructor _,_
    field fst : fst a â¶ fst b
    field snd : snd b â¶ snd a

  open Hom-ðð¢ð¬ððð¢ð« public

  module _ {a b : ðð¢ð¬ððð¢ð« ð} where
    instance
      isSetoid:Hom-ðð¢ð¬ððð¢ð« : isSetoid (Hom-ðð¢ð¬ððð¢ð« a b)
      isSetoid:Hom-ðð¢ð¬ððð¢ð« = isSetoid:byCodiscrete {ð = ââ}

  id-ðð¢ð¬ððð¢ð« : â{a : ðð¢ð¬ððð¢ð« ð} -> Hom-ðð¢ð¬ððð¢ð« a a
  id-ðð¢ð¬ððð¢ð« = id , id

  _â-ðð¢ð¬ððð¢ð«_ : â{a b c : ðð¢ð¬ððð¢ð« ð} -> Hom-ðð¢ð¬ððð¢ð« a b -> Hom-ðð¢ð¬ððð¢ð« b c -> Hom-ðð¢ð¬ððð¢ð« a c
  _â-ðð¢ð¬ððð¢ð«_ (f , fÊ³) (g , gÊ³) = f â g , gÊ³ â fÊ³

  instance
    isCategory:DisjointPair : isCategory (DisjointPair ð)
    isCategory.Hom isCategory:DisjointPair = Hom-ðð¢ð¬ððð¢ð«
    isCategory.isSetoid:Hom isCategory:DisjointPair = isSetoid:Hom-ðð¢ð¬ððð¢ð«
    isCategory.id isCategory:DisjointPair = id-ðð¢ð¬ððð¢ð«
    isCategory._â_ isCategory:DisjointPair = _â-ðð¢ð¬ððð¢ð«_
    isCategory.unit-l-â isCategory:DisjointPair = tt
    isCategory.unit-r-â isCategory:DisjointPair = tt
    isCategory.unit-2-â isCategory:DisjointPair = tt
    isCategory.assoc-l-â isCategory:DisjointPair = tt
    isCategory.assoc-r-â isCategory:DisjointPair = tt
    isCategory._â_ isCategory:DisjointPair = Î» x xâ â tt

