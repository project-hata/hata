
module Hata.Program.HataDaemon.Message where

open import Hata.Conventions
open import Hata.Abstract.Path.Definition


data BuildResult : 𝒰₀ where
  BuildSuccess : BuildResult
  BuildError : BuildResult

data EchoType : 𝒰₀ where
  BuildEcho UserEcho : EchoType

data Message : 𝒰₀ where
  Echo : EchoType -> Text -> Message
  BuildStart : Message
  BuildDone : BuildResult -> Message



---------------------------------------------------------------------



data ReflectionCommand : 𝒰₀ where
  generateHs : (Rel , HsProj)-Path -> (Rel , Mod)-Path -> ReflectionCommand
  templateHs : (Rel , HsProj)-Path -> (Rel , Mod)-Path -> ReflectionCommand

postulate
  -- #mreflect : List 𝒰₀ -> ReflectionCommand -> ℕ
  mod_ : (Rel , Dir)-Path -> (File)-Name

infix 20 mod_


open import Verification.Conventions.Meta.Term
open import Hata.Program.HataCmd.Common
open import Hata.Program.HataCmd.HataSystemInterface

expectName : Term -> TC Name
expectName (con c args) = return c
expectName (def c args) = return c
expectName other = typeError (strErr "Got wrong term " ∷ strErr (show other) ∷ [])

echoallmembers : List 𝒰₀ -> TC 𝟙-𝒰
echoallmembers [] = return tt
echoallmembers (x ∷ xs) = do
  `x` <- quoteTC x
  `xn` <- expectName `x`
  nam <- call-hsi-getNameFromFQ `xn`
  call-echo nam
  echoallmembers xs

  return tt


macro
  #mreflect : List 𝒰₀ -> ReflectionCommand -> Term -> TC 𝟙-𝒰
  #mreflect xs cmd hole = do
    echoallmembers xs
    unify hole (lit (string "a"))


HataSystemInterface : (Rel , HsProj)-Path
HataSystemInterface = (::  /  "Common" / hsproj "HataSystemInterface" )


_ = #mreflect (Message ∷ EchoType ∷ BuildResult ∷ [])
              (generateHs HataSystemInterface (:: / "HataSystemInterface" / "HataDaemon" / "Message"))


-- open import Hata.Program.HataCmd.Common
-- _ = #temp abc


-- generateHs (:: / "hallo" / {!!})
-- open import Hata.Program.HataCmd.Common
-- _ = #echo "hello?"


