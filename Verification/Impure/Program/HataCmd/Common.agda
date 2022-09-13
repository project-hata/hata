
module Verification.Impure.Program.HataCmd.Common where


open import Verification.Conventions
open import Verification.Conventions.Meta.Term

postulate
  execTC : (exe : Text) (args : List Text) (stdIn : Text)
         → TC (Σ ℕ (λ _ → Σ Text (λ _ → Text)))

{-# BUILTIN AGDATCMEXEC execTC #-}


call-echo : Text -> TC 𝟙-𝒰
call-echo mytext = do
    (exitCode , (stdOut , stdErr)) ← execTC "hata-cmd" ("echo" ∷ "--text" ∷ mytext ∷ []) ""
    if exitCode ≟ 0
      then (return tt)
      else (typeError (strErr "Got error: " ∷ strErr stdErr ∷ []))

call-hatacmd : List Text -> TC Text
call-hatacmd args = do
    (exitCode , (stdOut , stdErr)) ← execTC "hata-cmd" args ""
    if exitCode ≟ 0
      then (return stdOut)
      else (typeError (strErr "Got error: " ∷ strErr stdErr ∷ []))


macro
  getTName : Term -> Term → TC 𝟙-𝒰
  getTName (def n args) hole = do
    call-echo (primShowQName n)
    unify hole (lit (string "text"))
  getTName _ _ = typeError (strErr "this is not a name." ∷ [])

macro
  #reflect : Term -> Term → TC 𝟙-𝒰
  #reflect (def n args) hole = do
    call-hatacmd ("edittime:register-function" ∷ "--name" ∷ (primShowQName n) ∷ [])
    unify hole (lit (string "text"))
  #reflect _ _ = typeError (strErr "this is not a name." ∷ [])

macro
  #call : Term -> Term → TC 𝟙-𝒰
  #call (def n args) hole = do
    call-hatacmd ("edittime:execute-function" ∷ "--name" ∷ (primShowQName n) ∷ [])
    unify hole (lit (string "text"))
  #call _ _ = typeError (strErr "this is not a name." ∷ [])


macro
  #echo : Text → Term → TC 𝟙-𝒰
  #echo mytext hole = do
    call-echo mytext
    unify hole (lit (string mytext))

---------------------------
-- new reflection


-- bla = echo "hello! this or"


-- open import Verification.Impure.IO.Definition

-- myfuntocall : IO (⊤-𝒰 {ℓ₀})
-- myfuntocall = putStrLn "now the text changes!"


-- _ = #reflect myfuntocall
-- _ = #call myfuntocall
