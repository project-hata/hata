module Lib
    ( run
    ) where

import Network.Simple.TCP
import qualified Data.Text as T
import Data.Text.Encoding

defaultPort = "49999"

run :: IO ()
run = do
  serve (Host "127.0.0.1") defaultPort $ \(connectionSocket, remoteAddr) -> do
    -- putStrLn $ "TCP connection established from " ++ show remoteAddr

    let loop = do
          text_bs <- recv connectionSocket 200
          case text_bs of
            Nothing -> pure ()
            Just text_bs ->
              case decodeUtf8' text_bs of
                Left err -> putStrLn "Error: Could not decode text." >> loop
                Right text -> putStrLn (T.unpack text) >> loop

    loop
    closeSock connectionSocket



