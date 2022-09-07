
module Utility.Echo where

import Network.Simple.TCP
import qualified Data.Text as T
import Data.Text.Encoding


defaultPort = "49999"

  -- Now you may use connectionSocket as you please within this scope,
  -- possibly using recv and send to interact with the remote end.


echoToDaemon :: String -> IO ()
echoToDaemon text = do
  connect "localhost" defaultPort $ \(connectionSocket, remoteAddr) -> do
    -- putStrLn $ "Connection established to " ++ show remoteAddr
    let text_bs = encodeUtf8 (T.pack text)
    send connectionSocket text_bs
    closeSock connectionSocket


