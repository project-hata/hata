
module Edittime.MainGeneration where

import Data.Text as T
import State.Definition


getModule :: Text -> Text
getModule fullyqualified = dropEnd 1 $ fst $ breakOnEnd "." fullyqualified

getMain :: [RegisteredFunction] -> Text
getMain funs = T.unlines $
  [
    "module _generated.Agda.Edittime.Main where"
  , ""
  , "open import Verification.Impure.IO.Definition"
  , "open import Verification.Conventions"
  ]
  <> fmap (\s -> "open import " <> s) (getModule <$> qualifiedNameRF <$> funs)
  <>
  [ ""
  , "mymain : String -> IO (⊤-𝒰 {ℓ₀})"
  ]
  <> fmap (\s -> "mymain \"" <> s <> "\" = " <> s) (qualifiedNameRF <$> funs)
  <>
  [
    "mymain a = putStrLn (\"The input \" <> a <> \" is not a registered function.\")"
  , "{-# COMPILE GHC mymain as mymain #-}"
  , ""
  ]




