
module Verification.Impure.Program.HataDaemon.Message where

open import Verification.Conventions
open import Verification.Impure.Basics


data BuildResult : 𝒰₀ where
  Success : BuildResult
  Error : BuildResult

data EchoType : 𝒰₀ where
  BuildEcho UserEcho : EchoType

data Message : 𝒰₀ where
  Echo : EchoType -> Text -> Message
  BuildStart : Message
  BuildDone : BuildResult -> Message


open import Verification.Impure.Program.HataCmd.Common
_ = #echo "hello?"


