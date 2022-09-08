
module Edittime.Commands where

import Data.Text (Text)
import Data.Text.IO as TIO
import qualified Data.Text as T
import State.Definition
import Control.Exception (throw)
import Core.Exception (HataCmdException(ET_FunctionNotRegistered))
import System.Command
import Utility.Echo
import System.FilePath
import Edittime.MainGeneration

registerFunction :: Text -> IO ()
registerFunction name = do
  echoToDaemon $ "registering: " <> T.unpack name
  state <- readState
  let newListOfFunctions =
        filter (\rf -> qualifiedNameRF rf /= name) (registeredFunctions state)
        <> [RegisteredFunction name NotCompiled]
  let newState = state {registeredFunctions = newListOfFunctions}
  writeState newState
  return ()


executeFunction :: Text -> IO ()
executeFunction name = do
  -- get root
  rootDir <- findProjectRootDir

  -- get state
  state <- readState
  let funs = filter (\rf -> qualifiedNameRF rf == name) (registeredFunctions state)

  -- compile edittime if needed
  case funs of
    [] -> throw (ET_FunctionNotRegistered name)
    [RegisteredFunction _ IsCompiled] -> pure ()
    [RegisteredFunction _ NotCompiled] -> do
      echoToDaemon $ "Need to recompile for: " <> T.unpack name
      compileEdittime rootDir (registeredFunctions state)
    _ -> undefined -- shouldn't happen

  echoToDaemon "Calling hata-edittime."

  -- call edittime
  let edittime = rootDir </> "_build" </> "bin" </> "hata-edittime"
  (Exit c, Stdout out, Stderr err) <- command [] edittime [T.unpack name]

  echoToDaemon "Done calling hata-edittime."
  echoToDaemon out

  return ()


compileEdittime :: FilePath -> [RegisteredFunction] -> IO ()
compileEdittime root funs = do
  -- generate main
  TIO.writeFile (root </> "_generated" </> "Agda" </> "Edittime" </> "Main.agda") (getMain funs)

  -- compile
  (Exit c, Stdout out, Stderr err) <- command [] "metabuild" ["hata-edittime"]
  echoToDaemon $ "compilation end, code: " <> show c
  echoToDaemon $ err

  -- update state
  let newFuns = fmap (\(RegisteredFunction name _) -> RegisteredFunction name IsCompiled) funs
  writeState (HataCmdState newFuns)

