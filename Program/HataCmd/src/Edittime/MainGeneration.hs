
module Edittime.MainGeneration
  (
    getMain
  )
where

import Data.Text as T
import State.Definition

import HataSystemInterface.Reflection

getMain :: [RegisteredFunction] -> Text
getMain funs = T.unlines $
  [
    "module _generated.Agda.Edittime.Main where"
  , ""
  , "open import Impure.IO.Definition"
  , "open import Verification.Conventions"
  ]
  <> fmap ("open import " <>) (unFQName <$> getModuleFromFQ <$> qualifiedNameRF <$> funs)
  <>
  [ ""
  , "mymain : String -> IO (⊤-𝒰 {ℓ₀})"
  ]
  <> fmap (\s -> "mymain \"" <> s <> "\" = " <> s) (unFQName <$> qualifiedNameRF <$> funs)
  <>
  [
    "mymain a = putStrLn (\"The input \" <> a <> \" is not a registered function.\")"
  , "{-# COMPILE GHC mymain as mymain #-}"
  , ""
  ]




