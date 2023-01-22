
module Hata.Program.MetaBuilder.Configuration.ProjectUser where

open import Verification.Conventions
open import Hata.Builtin
open import Hata.Base.IO.Definition
open import Hata.Reflection.Definition
open import Hata.Reflection.Definition
open import Hata.Program.HataCmd.Common
open import Hata.Program.MetaBuilder.Configuration.Project


aaa = FilePath

myconfig : RustProjectConfig
myconfig = record { rustSource-RelDir = tofp "Template/Rust" ; rustBin-Name = tofp "this-is-different" }


myfun : IO (⊤-𝒰 {ℓ₀})
myfun = do
  putStrLn (toJSON-RustProjectConfig myconfig)
  putStrLn "hello"

_ = #echo "bla"




_  = #register-function myfun
_ = #execute-function myfun





