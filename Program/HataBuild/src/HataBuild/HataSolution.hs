
{- | Definition of the file format for .hataproj files.
-}
module HataBuild.HataSolution
  (
    HataSolution (..)
  ) where

import GHC.Generics
import Data.Aeson

data HataSolution = HataSolution
  {
    projects :: [FilePath]
  }
  deriving (Generic, Show)
instance FromJSON HataSolution

