
module Hata.Base.HIO.Translate.TC where

open import Hata.Conventions
open import Hata.Base.HIO.Definition hiding (_>>_) renaming (_>>=_ to _>>='_)
open import Verification.Conventions.Meta.Term
open import Hata.Program.HataCmd.Edittime

open import Hata.Base.TCMEXEC.Definition


runTC : ∀{A} -> HIO A -> TC A
runTC (return-HIO x) = return x
runTC (echoLn x) = echo x
runTC (runCommand-HIO x y) = call-program x y
runTC (writeFile path text) = call-program "hata-cmd" ("UTIL:writeGeneratedHaskellFile" ∷ "--file" ∷ path ∷ "--content" ∷ text ∷ []) >> return tt
runTC (editFile x x₁ x₂ x₃) = {!!}
runTC (x >>=' f) = do
  x' <- runTC x
  runTC (f x')

open import Hata.Reflection.Definition



