module Lib
    ( run
    ) where


import MAlonzo.Code.Q_generated.Agda.Edittime.Main
import System.Environment
import Data.Text as T

run :: IO ()
run = do
  args <- getArgs                  -- IO [String]
  case args of
    [] -> putStrLn "Too few args!"
    [arg] -> mymain (T.pack arg)
    _ -> putStrLn "Too many args!"


