
module MetaBuilder.Project.Type.Haskell where

import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake
import MetaBuilder.Core
import MetaBuilder.Core (ExtraGlobalConfig(buildAbDir))


data HaskellStackProjectConfig = HaskellStackProjectConfig
  { haskellStackBin_RelFile   :: FilePath
  , haskellStackSource_RelDir :: FilePath
  , haskellStackDependencySibling_RelDirs :: [FilePath]
  , haskellStackAutobuild     :: Bool
  , installGlobal             :: Bool
  }
  deriving (Generic, Show)
instance FromJSON HaskellStackProjectConfig


data ExtraHaskellStackProjectConfig = ExtraHaskellStackProjectConfig
  { haskellStackBin_AbFile     :: FilePath
  , haskellStackSource_AbDir   :: FilePath
  , haskellStackDependencySibling_AbDirs :: [(FilePath, FilePath)] -- copy [from] [to]
  -- original settings
  , originalHaskellStackConfig :: HaskellStackProjectConfig
  }
  deriving (Show)

deriveExtraProjectConfig_HaskellStack :: ExtraGlobalConfig -> HaskellStackProjectConfig -> ExtraHaskellStackProjectConfig
deriveExtraProjectConfig_HaskellStack egpc hpc =
  let haskellStackBin_AbFile   = if hpc.>installGlobal
                                    then (egpc.>home_AbDir) </> ".local" </> "bin"  </> hpc.>haskellStackBin_RelFile <.> exe
                                    else egpc.>binAbDir </> hpc.>haskellStackBin_RelFile <.> exe
      haskellStackSource_AbDir = egpc.>rootAbDir </> hpc.>haskellStackSource_RelDir
      haskellStackDependencySibling_AbDirs = (f) <$> hpc.>haskellStackDependencySibling_RelDirs
        where f reldir = (egpc.>rootAbDir </> reldir , egpc.>buildAbDir </> reldir)

  in ExtraHaskellStackProjectConfig
     { haskellStackBin_AbFile     = haskellStackBin_AbFile
     , haskellStackSource_AbDir    = haskellStackSource_AbDir
     , haskellStackDependencySibling_AbDirs = haskellStackDependencySibling_AbDirs
     , originalHaskellStackConfig  = hpc
     }

makeRules_HaskellStackProject :: ExtraGlobalConfig -> ExtraHaskellStackProjectConfig -> Rules ()
makeRules_HaskellStackProject egpc ehc = do
  if (ehc.>originalHaskellStackConfig.>haskellStackAutobuild)
    then want [ehc.>haskellStackBin_AbFile]
    else return ()

  phony (ehc.>originalHaskellStackConfig.>haskellStackBin_RelFile) $ do
    need [ehc.>haskellStackBin_AbFile]

  haskellStack_Files <- liftIO $ getDirectoryFilesIO (ehc.>haskellStackSource_AbDir) ["//*.hs", "//*.yaml", "//*.cabal", "//*.metabuild-template"]
  let haskellStackSource_Files = ((ehc.>haskellStackSource_AbDir </>) <$> haskellStack_Files)

  phony "copy-folder-dependencies" $ do
    let copySingleDep (from,to) = do
          files <- getDirectoryFiles from (["//*"])
          mapM_ (\f -> copyFileChanged (from </> f) (to </> f)) files
    mapM_ copySingleDep (ehc.>haskellStackDependencySibling_AbDirs)

  ehc.>haskellStackBin_AbFile %> \_ -> do
    need ["copy-folder-dependencies"]
    need haskellStackSource_Files
    cmd_ "stack" (Cwd (ehc.>haskellStackSource_AbDir)) ["install", "--local-bin-path=" ++ (dropFileName (ehc.>haskellStackBin_AbFile))]

instance ProjectType HaskellStackProjectConfig ExtraHaskellStackProjectConfig where
  deriveExtraConfig = deriveExtraProjectConfig_HaskellStack
  makeRules = makeRules_HaskellStackProject


