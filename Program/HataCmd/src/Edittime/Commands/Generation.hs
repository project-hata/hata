
module Edittime.Commands.Generation
  ( writeGeneratedHaskellFile
  , updateAgdaDatatypeSourceFile
  )
where

import HataSystemInterface.Path
import HataSystemInterface.Reflection
import HataSystemInterface.Exception
import Control.Exception
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


-- | Parse an Agda file containing a data type / record declaration and a "reflection"
--   statement. Given a string to fill after the reflection statement, fill that in if
--   it would change the file, do nothing else.
updateAgdaDatatypeSourceFile :: FQName -> Text -> Text -> IO ()
updateAgdaDatatypeSourceFile m rspart textToFill = do
  -- RS = reflectionStatement
  root <- findProjectRootDir
  let relpath = replace "." "/" (unFQName m)
  let file_path = root </> T.unpack relpath <.> ".agda"
  file_content <- TIO.readFile file_path

  -- find the part that goes until the reflection line
  let (file_upto_rspart, file_after_rspart) = breakOnEnd rspart file_content
  let (rspart_until_eol, _) = breakOn "\n" file_after_rspart
  let file_upto_rs_noeol = file_upto_rspart <> rspart_until_eol

  -- error out if we did not find what we searched for:
  if T.length file_after_rspart == T.length file_content
    then throw (ET_FileHasWrongFormat ("could not find the string '" <> rspart <> "'"))
    else pure ()

  -- this is what would be our new content
  let new_file_content = file_upto_rs_noeol <> "\n" <> textToFill

  -- write content if it would change
  if new_file_content == file_content
    then pure ()
    else do
      TIO.writeFile file_path new_file_content
      throw ET_CurrentFileUpdated


