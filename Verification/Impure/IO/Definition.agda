
module Verification.Impure.IO.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Agda.Builtin.IO using (IO) public

{-# FOREIGN GHC import Data.Text as T #-}

infixl 1 _>>=_ _>>_

postulate
  return : ∀ {a} {A : 𝒰 a} → A → IO A
  _>>=_  : ∀ {a b} {A : 𝒰 a} {B : 𝒰 b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}
{-# COMPILE UHC return = \_ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILE UHC _>>=_  = \_ _ _ _ x y -> UHC.Agda.Builtins.primBind x y #-}

_>>_ : ∀ {a b} {A : 𝒰 a} {B : 𝒰 b} → IO A → IO B → IO B
x >> y = x >>= (λ _ -> y)

postulate
  putStrLn : Text -> IO (⊤-𝒰 {ℓ₀})

{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

