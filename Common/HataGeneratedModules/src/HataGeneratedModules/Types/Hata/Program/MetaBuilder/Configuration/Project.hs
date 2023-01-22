module HataGeneratedModules.Types.Hata.Program.MetaBuilder.Configuration.Project where

import GHC.Generics
import Data.Aeson
import Data.Text as T
import Data.Text.Lazy.Encoding
import Data.Text.Lazy (toStrict)

data RustProjectConfig = RustProjectConfig
  { rustSource_RelDir :: FilePath
  , rustBin_Name :: FilePath
  }
  deriving (Show, Generic)
instance ToJSON RustProjectConfig
instance FromJSON RustProjectConfig

toJSON_RustProjectConfig :: RustProjectConfig -> Text
toJSON_RustProjectConfig = toStrict . f . decodeUtf8' . encode
  where f (Left e) = "error"
        f (Right r) = r