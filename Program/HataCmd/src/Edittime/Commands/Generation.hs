
module Edittime.Commands.Generation where

import HataSystemInterface.Path
import HataSystemInterface.Reflection
import Data.Text as T
import Data.Text.IO as TIO
import System.FilePath
import System.Directory (createDirectoryIfMissing)


writeGeneratedHaskellFile :: FQName -> Text -> IO ()
writeGeneratedHaskellFile m content = do
  root <- path_HataGeneratedModules_src
  let relpath = replace "." "/" (unFQName m)
  let path = root </> T.unpack relpath <.> "hs"
  createDirectoryIfMissing True $ takeDirectory path
  TIO.writeFile path content



