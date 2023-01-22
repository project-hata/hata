
module Utility.File where

-- import Network.Simple.TCP
import Data.Text as T
import Data.Text.IO as TIO
import Data.Text.Encoding
import System.FilePath
import System.Directory (createDirectoryIfMissing)
-- import qualified Data.ByteString          as B

writeFileCmd :: Text -> Text -> IO ()
writeFileCmd path content = do
  -- root <- path_HataGeneratedModules_src
  -- let relpath = replace "." "/" (unFQName m)
  -- let path = root </> T.unpack relpath <.> "hs"
  createDirectoryIfMissing True $ takeDirectory (T.unpack path)
  TIO.writeFile (T.unpack path) content

