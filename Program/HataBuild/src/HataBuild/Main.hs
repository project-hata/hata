
module HataBuild.Main where

import Data.Yaml (decodeFileThrow)

import HataSystemInterface.Path
import HataBuild.HataSolution


main :: IO ()
main = do
  solutionfile_Path <- findProjectRootFile
  solutionfile <- decodeFileThrow solutionfile_Path

  projects <- loadProjects solutionfile

  return undefined


loadProjects :: HataSolution -> IO ()
loadProjects = undefined


