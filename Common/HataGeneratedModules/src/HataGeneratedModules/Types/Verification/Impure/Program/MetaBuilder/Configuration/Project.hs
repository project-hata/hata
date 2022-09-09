module HataGeneratedModules.Types.Verification.Impure.Program.MetaBuilder.Configuration.Project where

import GHC.Generics
import Data.Aeson

data RustProjectConfig = RustProjectConfig
  { rustSource_RelDir :: FilePath
  , rustBin_Name :: FilePath
  }
  deriving (Show, Generic)
instance ToJSON RustProjectConfig
instance FromJSON RustProjectConfig