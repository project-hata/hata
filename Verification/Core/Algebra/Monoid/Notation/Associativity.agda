
module Verification.Core.Algebra.Monoid.Notation.Associativity where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition


module _ {M : ð° _} {{_ : Monoid ð on M}} where
  assoc-[ab][cd]âža[bc]d-â : {f g h i : M}
                            -> (f â g) â (h â i) âž f â (g â h) â i
  assoc-[ab][cd]âža[bc]d-â {f = f} {g} {h} {i} =
    (f â g) â (h â i)    âĻ assoc-r-â âĐ-âž
    (f â g) â h â i      âĻ assoc-l-â âââ refl âĐ-âž
    f â (g â h) â i      â

  assoc-[abcd]âža[bcd]-â : {f g h i : M}
                          -> f â g â h â i âž f â (g â h â i)
  assoc-[abcd]âža[bcd]-â {f = f} {g} {h} {i} =
    f â g â h â i     âĻ assoc-l-â âĐ-âž
    f â g â (h â i)   âĻ assoc-l-â âĐ-âž
    f â (g â (h â i)) âĻ refl âââ assoc-r-â âĐ-âž
    f â (g â h â i)   â

  assoc-[abcd]âža[bc]d-â : {f g h i : M}
                            -> f â g â h â i âž f â (g â h) â i
  assoc-[abcd]âža[bc]d-â {f = f} {g} {h} {i} = assoc-l-â âââ refl
