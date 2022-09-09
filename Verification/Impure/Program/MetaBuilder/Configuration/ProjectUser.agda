
module Verification.Impure.Program.MetaBuilder.Configuration.ProjectUser where

open import Verification.Conventions
open import Verification.Impure.Builtin
open import Verification.Impure.IO.Definition
open import Verification.Impure.Reflection.Definition
open import Verification.Impure.Reflection.Definition
open import Verification.Impure.Program.HataCmd.Common
open import Verification.Impure.Program.MetaBuilder.Configuration.Project


aaa = FilePath

myconfig : RustProjectConfig
myconfig = record { rustSource-RelDir = tofp "Template/Rust" ; rustBin-Name = tofp "this-is-different" }


myfun : IO (⊤-𝒰 {ℓ₀})
myfun = putStrLn (toJSON-RustProjectConfig myconfig)

_  = #reflect myfun


_ = #call myfun

