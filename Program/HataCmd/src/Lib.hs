module Lib
    ( run
    ) where

import Options.Applicative

import Utility.Echo
import Edittime.Commands.Function
import Data.Text as T
import qualified Data.Text.IO as TIO

import HataSystemInterface.Reflection
import Edittime.Commands.Generation (writeGeneratedHaskellFile, updateAgdaDatatypeSourceFile)

data Command =
  CommandEcho String
  | Command_ET_RegisterFunction String
  | Command_ET_ExecuteFunction String
  | Command_ET_writeGeneratedHaskellFile String String
  | Command_ET_updateAgdaDatatypeSourceFile String String String
  | Command_HSI_getNameFromFQ String
  | Command_HSI_getModuleFromFQ String

pCmd :: Parser Command
pCmd = subparser
  ( command "echo"
    (info (CommandEcho <$> strOption (long "text" <> help "the text to echo"))
     ( progDesc "Echo via the daemon." ))

  ----------------------
  -- Edittime commands
 <> command "edittime:register-function"
    (info (Command_ET_RegisterFunction
           <$> strOption (long "name" <> help "function name"))
     (progDesc "Record changes to the repository"))

 <> command "edittime:execute-function"
    (info (Command_ET_ExecuteFunction
           <$> strOption (long "name" <> help "function name"))
     (progDesc "Record changes to the repository"))

 <> command "ET:writeGeneratedHaskellFile"
    (info (Command_ET_writeGeneratedHaskellFile
           <$> strOption (long "module" <> help "modulepath")
           <*> strOption (long "content" <> help "file content")
          )
     (progDesc "write generated haskell file"))

 <> command "ET:updateAgdaDatatypeSourceFile"
    (info (Command_ET_updateAgdaDatatypeSourceFile
           <$> strOption (long "module" <> help "modulepath")
           <*> strOption (long "rspart" <> help "reflection statement part")
           <*> strOption (long "content" <> help "file content")
          )
     (progDesc "write generated haskell file"))

  ----------------------
  -- Hata System Interface commands

 <> command "hsi:getNameFromFQ"
    (info (Command_HSI_getNameFromFQ
           <$> strOption (long "name"))
     (progDesc "get name from fully qualified name"))
 <> command "hsi:getModuleFromFQ"
    (info (Command_HSI_getModuleFromFQ
           <$> strOption (long "name"))
     (progDesc "get module name from fully qualified name"))
  )


run :: IO ()
run = execute =<< execParser opts
  where
    opts = info (pCmd <**> helper)
      ( fullDesc
     <> progDesc "Execute commands for hata. This is usually called automatically."
     <> header "hata-cmd - command executor for hata development" )

execute :: Command -> IO ()
execute (CommandEcho text) = echoToDaemon text
execute (Command_ET_RegisterFunction name) = registerFunction (FQName $ T.pack name)
execute (Command_ET_ExecuteFunction name) = executeFunction (FQName $ T.pack name)
execute (Command_ET_writeGeneratedHaskellFile m content) =
  writeGeneratedHaskellFile (FQName (T.pack m)) (T.pack content)
execute (Command_ET_updateAgdaDatatypeSourceFile m rspart content) =
  updateAgdaDatatypeSourceFile (FQName (T.pack m)) (T.pack rspart) (T.pack content)
execute (Command_HSI_getNameFromFQ name) = TIO.putStr $ getNameFromFQ $ FQName (T.pack name)
execute (Command_HSI_getModuleFromFQ name) = TIO.putStr $ unFQName $ getModuleFromFQ $ FQName (T.pack name)


-- sample :: Parser Sample
-- sample = Sample
--       <$> strOption
--           ( long "hello"
--          <> metavar "TARGET"
--          <> help "Target for the greeting" )
--       <*> switch
--           ( long "quiet"
--          <> short 'q'
--          <> help "Whether to be quiet" )
--       <*> option auto
--           ( long "enthusiasm"
--          <> help "How enthusiastically to greet"
--          <> showDefault
--          <> value 1
--          <> metavar "INT" )
