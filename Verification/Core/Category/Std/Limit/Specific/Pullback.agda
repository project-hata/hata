
module Verification.Core.Category.Std.Limit.Specific.Pullback where

open import Verification.Core.Conventions
open import Verification.Core.Setoid
open import Verification.Core.Category.Std.Category.Definition



module _ {ð : Category ð} where

  record PullbackData : ð° ð where
    constructor pullbackData
    field {sourceâ} {sourceâ} {target} : â¨ ð â©
    field mapâ : sourceâ â¶ target
    field mapâ : sourceâ â¶ target

  open PullbackData public

  record isPullbackCandidate (ð¹ : PullbackData) (x : Obj ð) : ð° ð where
    constructor is-PullbackCandidate
    field Ïâ-Pb : â¨ x â© â¶ ð¹ .sourceâ
    field Ïâ-Pb : â¨ x â© â¶ ð¹ .sourceâ
    field â¼-Pb : Ïâ-Pb â ð¹ .mapâ â¼ Ïâ-Pb â ð¹ .mapâ

  open isPullbackCandidate {{...}} public

  PullbackCandidate : â (ð¹ : PullbackData) -> ð° _
  PullbackCandidate ð¹ = _ :& isPullbackCandidate ð¹

  record isPullback {ð¹ : PullbackData} (c : PullbackCandidate ð¹) : ð° ð where
    constructor is-pullback
    field intro-Pb : â{d : PullbackCandidate ð¹} -> â¨ d â© â¶ â¨ c â©
    -- field unique-Pb : â{d : PullbackCandidate ð¹} -> â{f : â¨ d â© â¶ â¨ c â©} -> f â¼ intro-Pb

record hasPullbacks (ð : Category ð) : ð° ð where
  constructor has-Pullbacks
  field pullback : â{a b c : â¨ ð â©} -> (f : a â¶ c) -> (g : b â¶ c) -> PullbackCandidate {ð = ð} (pullbackData f g)
  field isPullback:pullback : â{a b c : â¨ ð â©} -> {f : a â¶ c} -> {g : b â¶ c}
                              -> isPullback (pullback f g)

  _â°_ : â{a b c : â¨ ð â©} -> (f : a â¶ c) -> (g : b â¶ c) -> â¨ ð â©
  _â°_ f g = â¨ pullback f g â©



  -- record isCoequalizer {a b : X} (f g : a â¶ b) (x : X) : ð° (ð ï½¤ ð) where
  --   field Ï-Coeq : b â¶ x
  --         â¼-Coeq : f â Ï-Coeq â¼ g â Ï-Coeq
  --         elim-Coeq : â{c : X} -> (h : b â¶ c) -> (f â h â¼ g â h) -> x â¶ c
  --         reduce-Coeq : â{c : X} -> (h : b â¶ c) -> (p : f â h â¼ g â h)
  --                       -> Ï-Coeq â elim-Coeq h p â¼ h
  --         expand-Coeq : â{c : X} -> (h : x â¶ c) -> (p : f â (Ï-Coeq â h) â¼ g â (Ï-Coeq â h)) -> h â¼ elim-Coeq (Ï-Coeq â h) p
  --         -- (assoc-r-â â (â¼-Coeq â refl) â assoc-l-â)

  -- open isCoequalizer {{...}} public


