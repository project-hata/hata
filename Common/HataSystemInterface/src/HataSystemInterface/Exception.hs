
module HataSystemInterface.Exception
  (
    HataCmdException (..)
  )
  where

import Control.Exception
import Data.Typeable
import Data.Text as T

import HataSystemInterface.Reflection

data HataCmdException
  = CouldNotFindRootFile
  | FoundMultipleRootFiles
  | ET_FunctionNotRegistered FQName
  | ET_CurrentFileUpdated
  | ET_FileHasWrongFormat Text
  deriving (Typeable)

instance Show HataCmdException where
  show CouldNotFindRootFile   = "Error: Could not find a .metabuild-root file."
  show FoundMultipleRootFiles = "Error: Found multiple .metabuild-root files in same directory."
  show (ET_FunctionNotRegistered name) = "Error: The function " <> show name <> " is not registered."
  show ET_CurrentFileUpdated = "Note: The current file was updated. Please load again."
  show (ET_FileHasWrongFormat msg) = "Error: The current file has a wrong format: " <> T.unpack msg

instance Exception HataCmdException



