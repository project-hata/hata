
module Verification.Core.Category.Std.Category.Notation.Associativity where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition


module _ {ð : ð° ð} {{_ : isCategory {ð} ð}} where
  assoc-[ab][cd]âža[bc]d-â : â{a b c d e : ð}
                            -> {f : a âķ b} -> {g : b âķ c} -> {h : c âķ d} -> {i : d âķ e}
                            -> (f â g) â (h â i) âž f â (g â h) â i
  assoc-[ab][cd]âža[bc]d-â {f = f} {g} {h} {i} =
    (f â g) â (h â i)    âĻ assoc-r-â âĐ-âž
    (f â g) â h â i      âĻ assoc-l-â â refl âĐ-âž
    f â (g â h) â i      â

  assoc-[abcd]âža[bcd]-â : â{a b c d e : ð}
                          -> {f : a âķ b} -> {g : b âķ c} -> {h : c âķ d} -> {i : d âķ e}
                          -> f â g â h â i âž f â (g â h â i)
  assoc-[abcd]âža[bcd]-â {f = f} {g} {h} {i} =
    f â g â h â i     âĻ assoc-l-â âĐ-âž
    f â g â (h â i)   âĻ assoc-l-â âĐ-âž
    f â (g â (h â i)) âĻ refl â assoc-r-â âĐ-âž
    f â (g â h â i)   â

  assoc-[abcd]âža[bc]d-â : â{a b c d e : ð}
                            -> {f : a âķ b} -> {g : b âķ c} -> {h : c âķ d} -> {i : d âķ e}
                            -> f â g â h â i âž f â (g â h) â i
  assoc-[abcd]âža[bc]d-â {f = f} {g} {h} {i} = assoc-l-â â refl

