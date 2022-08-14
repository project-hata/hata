
module Verification.Application.CompGen.Languages.CubeLang.Definition where

open import Verification.Conventions


open import Agda.Builtin.IO

infixl 1 _>>=_

postulate
  return : ∀ {a} {A : 𝒰 a} → A → IO A
  _>>=_  : ∀ {a b} {A : 𝒰 a} {B : 𝒰 b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}
{-# COMPILE UHC return = \_ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILE UHC _>>=_  = \_ _ _ _ x y -> UHC.Agda.Builtins.primBind x y #-}

mymain : IO (ℕ)
mymain = return 4


{-# COMPILE GHC mymain as mymain #-}


