
module State.Definition
  (
    RegisteredFunction (..)
  , HataCmdState (..)
  , CompilationState (..)
  , readState
  , writeState
  , findProjectRootDir
  )
where

import qualified Data.Text as T
import Data.Text as T (Text)
import GHC.Generics
import Data.Aeson
import System.FilePath
import Control.Exception
import System.Directory
import Data.Default

import Utility.Echo

import HataSystemInterface.Exception
import HataSystemInterface.Path
import HataSystemInterface.Reflection

data CompilationState = IsCompiled | NotCompiled
  deriving (Generic, Show)

instance ToJSON CompilationState
instance FromJSON CompilationState

data RegisteredFunction = RegisteredFunction
  {
    qualifiedNameRF :: FQName
  , compilationStateRF :: CompilationState
  }
  deriving (Generic, Show)

instance ToJSON RegisteredFunction
instance FromJSON RegisteredFunction


data HataCmdState = HataCmdState
  {
    registeredFunctions :: [RegisteredFunction]
  }
  deriving (Generic, Show)

instance Default HataCmdState
instance ToJSON HataCmdState
instance FromJSON HataCmdState

statePath root = root </> "_state" </> "hata-cmd" </> "state.json"


readState :: IO HataCmdState
readState = do
  rootDir <- findProjectRootDir
  let file = (statePath rootDir)

  bExists <- doesFileExist file
  case bExists of
    True -> pure ()
    False -> writeState def

  res <- decodeFileStrict (statePath rootDir)
  case res of
    Just a -> return a
    Nothing -> echoToDaemon "Could not find state file, assuming empty." >> return def

writeState :: HataCmdState -> IO ()
writeState state = do
  rootDir <- findProjectRootDir
  let file = (statePath rootDir)
  let dir = takeDirectory file
  createDirectoryIfMissing True dir
  encodeFile file state




