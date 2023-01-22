
module Hata.Program.HataCmd.Common where


-- open import Verification.Conventions
open import Hata.Conventions
open import Verification.Conventions.Meta.Term

postulate
  execTC : (exe : Text) (args : List Text) (stdIn : Text)
         → TC (Σ ℕ (λ _ → Σ Text (λ _ → Text)))

{-# BUILTIN AGDATCMEXEC execTC #-}

call-program : Text -> List Text -> TC Text
call-program prog args = do
    (exitCode , (stdOut , stdErr)) ← execTC prog args ""
    if exitCode ≟ 0
      then (return stdOut)
      else (typeError (strErr "Got error: " ∷ strErr stdErr ∷ []))

call-echo : Text -> TC 𝟙-𝒰
call-echo mytext = do
    (exitCode , (stdOut , stdErr)) ← execTC "hata-cmd" ("echo" ∷ "--text" ∷ mytext ∷ []) ""
    if exitCode ≟ 0
      then (return tt)
      else (typeError (strErr "Got error: " ∷ strErr stdErr ∷ []))

call-hatacmd : List Text -> TC Text
call-hatacmd = call-program "hata-cmd"


macro
  getTName : Term -> Term → TC 𝟙-𝒰
  getTName (def n args) hole = do
    call-echo (primShowQName n)
    unify hole (lit (string "text"))
  getTName _ _ = typeError (strErr "this is not a name." ∷ [])

macro
  #register-function : Term -> Term → TC 𝟙-𝒰
  #register-function (def n args) hole = do
    call-hatacmd ("edittime:register-function" ∷ "--name" ∷ (primShowQName n) ∷ [])
    unify hole (lit (string "text"))
  #register-function _ _ = typeError (strErr "this is not a name." ∷ [])

macro
  #execute-function : Term -> Term → TC 𝟙-𝒰
  #execute-function (def n args) hole = do
    call-hatacmd ("edittime:execute-function" ∷ "--name" ∷ (primShowQName n) ∷ [])
    unify hole (lit (string "text"))
  #execute-function _ _ = typeError (strErr "this is not a name." ∷ [])


echo : Text -> TC ⊤
echo txt = call-program "hata-cmd" ("echo" ∷ "--text" ∷ txt ∷ []) >> return tt

macro
  # : ∀{A : 𝒰 𝑖} -> TC A -> Term -> TC 𝟙-𝒰
  # f hole = do
    res <- f
    res-quoted <- quoteTC res
    unify hole res-quoted

macro
  #echo : Text → Term → TC 𝟙-𝒰
  #echo mytext hole = do
    call-echo mytext
    unify hole (lit (string mytext))

macro
  #echo-term : (a : Term) -> (t : Term) -> TC 𝟙-𝒰
  #echo-term a hole = do
    call-echo (show a)
    unify hole (lit (string ""))

---------------------------
-- new register-functionion


-- bla = echo "hello! this or"


-- open import Hata.IO.Definition

-- myfuntocall : IO (⊤-𝒰 {ℓ₀})
-- myfuntocall = putStrLn "now the text changes!"


-- _ = #register-function myfuntocall
-- _ = #execute-function myfuntocall
