module Lib
    ( run
    ) where

import Options.Applicative

import Utility.Echo
import Edittime.Commands
import Data.Text as T

data Command =
  CommandEcho String
  | Command_ET_RegisterFunction String
  | Command_ET_ExecuteFunction String

pCmd :: Parser Command
pCmd = subparser
  ( command "echo"
    (info (CommandEcho <$> strOption (long "text" <> help "the text to echo"))
     ( progDesc "Echo via the daemon." ))
 <> command "edittime:register-function"
    (info (Command_ET_RegisterFunction
           <$> strOption (long "name" <> help "function name")
           -- <*> strOption (long "short" <> help "short name")
          )
     (progDesc "Record changes to the repository"))

 <> command "edittime:execute-function"
    (info (Command_ET_ExecuteFunction
           <$> strOption (long "name" <> help "function name")
           -- <*> strOption (long "short" <> help "short name")
          )
     (progDesc "Record changes to the repository"))
  )

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

run :: IO ()
run = execute =<< execParser opts
  where
    opts = info (pCmd <**> helper)
      ( fullDesc
     <> progDesc "Execute commands for hata. This is usually called automatically."
     <> header "hata-cmd - command executor for hata development" )

execute :: Command -> IO ()
execute (CommandEcho text) = echoToDaemon text
execute (Command_ET_RegisterFunction name) = registerFunction (T.pack name)
execute (Command_ET_ExecuteFunction name) = executeFunction (T.pack name)


