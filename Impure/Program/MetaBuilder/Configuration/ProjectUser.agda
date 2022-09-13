
module Impure.Program.MetaBuilder.Configuration.ProjectUser where

open import Verification.Conventions
open import Impure.Builtin
open import Impure.IO.Definition
open import Impure.Reflection.Definition
open import Impure.Reflection.Definition
open import Impure.Program.HataCmd.Common
open import Impure.Program.MetaBuilder.Configuration.Project


aaa = FilePath

myconfig : RustProjectConfig
myconfig = record { rustSource-RelDir = tofp "Template/Rust" ; rustBin-Name = tofp "this-is-different" }


myfun : IO (⊤-𝒰 {ℓ₀})
myfun = putStrLn (toJSON-RustProjectConfig myconfig)

-- _ = #echo "bla"

_  = #reflect myfun
_ = #call myfun

