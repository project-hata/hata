
module Utility.RunCmd where

import           Control.Concurrent
import           Control.Concurrent.Async (Concurrently (..))
import qualified Data.ByteString          as B
import           Data.Conduit             (($$), (=$))
import qualified Data.Conduit.Binary      as CB
import qualified Data.Conduit.List        as CL
import           Data.Conduit.Process     (ClosedStream (..), shell,
                                           streamingProcess,
                                           waitForStreamingProcess)
import           Data.Monoid              ((<>))
import           System.Environment       (getArgs)

import Utility.Echo

data Msg = Quit | Msg Int B.ByteString

{-| Run @cmd@ and send both its output and stdout into the @chan'@.
 -}
runProcess :: Chan Msg -> Int -> String -> IO ()
runProcess chan i cmd = do
    let cmd' = "script -qfc \"" <> cmd <> "\" /dev/null"
    (ClosedStream, fromProcess, fromProcessErr, cph) <-
        streamingProcess (shell cmd')

    let output h = CB.sourceHandle h $$ CB.lines =$ CL.mapM_
            (writeChan chan . Msg i)

    _ <- runConcurrently $
        Concurrently (output fromProcess) *>
        Concurrently (output fromProcessErr) *>
        Concurrently (waitForStreamingProcess cph)

    writeChan chan Quit


{-| Wrap a bytestring in ANSI color sequences.
 -}
colored :: Int -> B.ByteString -> B.ByteString
colored i d = let col = colors !! i
              in "\ESC[" <> col <> ";1m" <> d <> "\ESC[0m\n"
  where
    colors = cycle ["36", "35", "32", "33", "34", "31"]

{-| Read everything from the channel and print it. This function returns only
 - when all processes send a Quit message.
 -}
reader :: Chan Msg -> Int -> IO ()
reader _ 0 = return ()
reader chan num = do
    msg <- readChan chan
    case msg of
        Quit -> reader chan (num - 1)
        Msg i d -> do
            B.putStr $ colored i d
            echoToDaemonBS $ colored i d
            reader chan num

runSingleCmd :: String -> IO ()
runSingleCmd command = do
    -- args <- getArgs
    readEnd <- newChan
    writeEnd <- dupChan readEnd

    mapM_ (forkIO . uncurry (runProcess writeEnd)) [(0, command)] -- (zip [0..] args)

    reader readEnd 1 -- (length args)



