
module Core.Exception where

import Control.Exception
import Data.Typeable
import Data.Text as T

data HataCmdException
  = CouldNotFindRootFile
  | FoundMultipleRootFiles
  | ET_FunctionNotRegistered Text
  deriving (Typeable)

instance Show HataCmdException where
  show CouldNotFindRootFile   = "Error: Could not find a .metabuild-root file."
  show FoundMultipleRootFiles = "Error: Found multiple .metabuild-root files in same directory."
  show (ET_FunctionNotRegistered name) = "Error: The function " <> T.unpack name <> " is not registered."

instance Exception HataCmdException

