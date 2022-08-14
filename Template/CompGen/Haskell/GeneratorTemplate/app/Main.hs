module Main (main) where

import Lib
import MAlonzo.Code.Verification.Application.CompGen.Languages.CubeLang.Definition

main :: IO ()
main = putStrLn =<< show <$> mymain
