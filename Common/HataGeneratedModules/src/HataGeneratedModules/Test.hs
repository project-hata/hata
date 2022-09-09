
module HataGeneratedModules where

import GHC.Generics
import Data.Aeson

data RustProjectConfig = RustProjectConfig
  {
  rustSource_RelDir :: FilePath
  }
  deriving (Show, Generic)
instance ToJSON RustProjectConfig
instance FromJSON RustProjectConfig



