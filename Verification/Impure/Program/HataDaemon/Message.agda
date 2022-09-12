
module Verification.Impure.Program.HataDaemon.Message where

open import Verification.Impure.SpecialConventions
open import Verification.Impure.Abstract.Path.Definition


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
  genHs : (Rel , File)-Path -> ReflectionCommand

postulate
  #mreflect : List 𝒰₀ -> ReflectionCommand -> ℕ
  mod_ : (Rel , Dir)-Path -> (File)-Name

infix 20 mod_

HataSystemInterface : (Rel , Dir)-Path
HataSystemInterface = (::  /  "Common" / "HataSystemInterface" )

_ = #mreflect (Message ∷ EchoType ∷ BuildResult ∷ []) $
       genHs (HataSystemInterface / (mod :: / "Generated" / "HataDaemon" / "Messages"))


-- genHs (:: / "hallo" / {!!})
-- open import Verification.Impure.Program.HataCmd.Common
-- _ = #echo "hello?"


