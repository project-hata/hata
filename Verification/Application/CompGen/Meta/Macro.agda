
module Verification.Application.CompGen.Meta.Macro where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term

postulate
  execTC : (exe : String) (args : List String) (stdIn : String)
         → TC (Σ ℕ (λ _ → Σ String (λ _ → String)))

{-# BUILTIN AGDATCMEXEC execTC #-}


callEcho : String -> TC 𝟙-𝒰
callEcho mytext = do
    (exitCode , (stdOut , stdErr)) ← execTC "hata-cmd" ("echo" ∷ "--text" ∷ mytext ∷ []) ""
    return tt

call-hata-cmd : List String -> TC 𝟙-𝒰
call-hata-cmd args = do
    (exitCode , (stdOut , stdErr)) ← execTC "hata-cmd" args ""
    if exitCode ≟ 0
      then (return tt)
      else (typeError (strErr "Got error: " ∷ strErr stdErr ∷ []))


macro
  getTName : Term -> Term → TC 𝟙-𝒰
  getTName (def n args) hole = do
    callEcho (primShowQName n)
    unify hole (lit (string "text"))
  getTName _ _ = typeError (strErr "this is not a name." ∷ [])

macro
  #reflect : Term -> Term → TC 𝟙-𝒰
  #reflect (def n args) hole = do
    call-hata-cmd ("edittime:register-function" ∷ "--name" ∷ (primShowQName n) ∷ [])
    unify hole (lit (string "text"))
  #reflect _ _ = typeError (strErr "this is not a name." ∷ [])

macro
  #call : Term -> Term → TC 𝟙-𝒰
  #call (def n args) hole = do
    call-hata-cmd ("edittime:execute-function" ∷ "--name" ∷ (primShowQName n) ∷ [])
    unify hole (lit (string "text"))
  #call _ _ = typeError (strErr "this is not a name." ∷ [])


macro
  echo : String → Term → TC 𝟙-𝒰
  echo mytext hole = do
    callEcho mytext
    unify hole (lit (string mytext))



-- bla = echo "hello! this or"



open import Verification.Impure.IO.Definition

myfuntocall : IO (⊤-𝒰 {ℓ₀})
myfuntocall = putStrLn "now the text changes!"
_ = #reflect myfuntocall



_ = #call myfuntocall


