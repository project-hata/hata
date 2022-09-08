
module HataSystemInterface.Path
  (
    findProjectRootFile
  , findProjectRootDir
  )
  where

import System.FilePath
import Control.Exception
import System.Directory
-- import Data.Default

import HataSystemInterface.Exception

------------------------------------------------------------
-- Finding the root file

filterRoot :: FilePath -> Bool
filterRoot file = takeExtension file == ".metabuild-root"

findProjectRootFile_impl :: FilePath -> IO FilePath
findProjectRootFile_impl cur_dir = do
  files <- listDirectory cur_dir
  let filtered = filter filterRoot files
  case filtered of
    [] -> let parent = takeDirectory cur_dir
          in if isDrive cur_dir || parent == cur_dir
             then throw CouldNotFindRootFile
             else findProjectRootFile_impl parent
    [x] -> return (cur_dir </> x)
    _:_ -> throw FoundMultipleRootFiles

findProjectRootFile :: IO FilePath
findProjectRootFile = do
  getCurrentDirectory >>= findProjectRootFile_impl

findProjectRootDir :: IO FilePath
findProjectRootDir = takeDirectory <$> findProjectRootFile


