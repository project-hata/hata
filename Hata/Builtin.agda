
module Hata.Builtin where

open import Verification.Conventions

{-# FOREIGN GHC import Data.Text as T #-}

-- FilePath = Text

postulate
  FilePath : 𝒰₀
  tofp : Text -> FilePath

{-# COMPILE GHC FilePath = type FilePath #-}
{-# COMPILE GHC tofp = T.unpack #-}



