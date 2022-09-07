module Lib
    ( run
    ) where

import Options.Applicative

import Utility.Echo

data Command = CommandEcho String

pCmd :: Parser Command
pCmd = subparser
  ( command "echo" (info (CommandEcho <$> strOption (long "text" <> help "the text to echo")) ( progDesc "Echo via the daemon." ))
 <> command "commit" (info undefined ( progDesc "Record changes to the repository" ))
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

-- greet :: Sample -> IO ()
-- greet (Sample h False n) = putStrLn $ "Hello, " ++ h ++ replicate n '!'
-- greet _ = return ()


  

