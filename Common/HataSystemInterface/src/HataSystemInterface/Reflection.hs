
module HataSystemInterface.Reflection
  (
    getModuleFromFQ
  , getNameFromFQ
  , FQName (..)
  )
where

import Data.Text as T
import GHC.Generics
import Data.Aeson

newtype FQName = FQName {unFQName :: Text}
  deriving (Generic, Eq)

instance Show FQName where
  show = T.unpack . unFQName

instance ToJSON FQName
instance FromJSON FQName

getModuleFromFQ :: FQName -> FQName
getModuleFromFQ = FQName . dropEnd 1 . fst . breakOnEnd "." . unFQName

getNameFromFQ :: FQName -> Text
getNameFromFQ = snd . breakOnEnd "." . unFQName

