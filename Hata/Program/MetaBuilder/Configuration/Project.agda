
module Hata.Program.MetaBuilder.Configuration.Project where

open import Verification.Conventions
open import Hata.Builtin
open import Hata.Reflection.Definition

{-# FOREIGN GHC import HataGeneratedModules.Types.Hata.Program.MetaBuilder.Configuration.Project #-}

-- data HaskellStackProjectConfig = HaskellStackProjectConfig
--   { haskellStackBin_RelFile   :: FilePath
--   , haskellStackSource_RelDir :: FilePath
--   , haskellStackDependencySibling_RelDirs :: [FilePath]
--   , haskellStackAutobuild     :: Bool
--   , installGlobal             :: Bool
--   }
--   deriving (Generic, Show)
-- instance FromJSON HaskellStackProjectConfig




record RustProjectConfig : 𝒰₀ where
  field
    rustSource-RelDir : FilePath
    rustBin-Name : FilePath


_ = #generate-haskell RustProjectConfig
--  -----------------
--  |
--  | GENERATED CODE for haskell bindings is here.
--  v
--------------------------------------------------
{-# COMPILE GHC RustProjectConfig = data RustProjectConfig (RustProjectConfig) #-}
postulate
  toJSON-RustProjectConfig : RustProjectConfig -> Text
{-# COMPILE GHC toJSON-RustProjectConfig = toJSON_RustProjectConfig #-}