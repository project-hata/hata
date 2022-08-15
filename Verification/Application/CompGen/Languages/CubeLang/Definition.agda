
module Verification.Application.CompGen.Languages.CubeLang.Definition where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural

open import Verification.Impure.IO.Definition


mymain : IO (ℕ)
mymain = (putStrLn "hello!") >>= λ _ -> return 3



{-# COMPILE GHC mymain as mymain #-}

 --------------------------------------------
-- language

private variable
  i : ♮ℕ

data Type : 𝒰₀ where
  $Float $Int : Type
  _$->_ : Type -> Type -> Type


data Term : ♮ℕ -> 𝒰₀ where
  def_,_ : Term i -> Term (tt ∷ i) -> Term i
  var : i ∍♮ tt -> Term i
  litint : ℕ -> Term i
  litfloat : ℕ -> ℕ -> Term i
  bAdd : Term i -> Term i -> Term i


---------------------------------------------
-- examples

v0 : Term (tt ∷ i)
v0 = var incl

v1 : Term (tt ∷ tt ∷ i)
v1 = var (skip incl)

v2 : Term (tt ∷ tt ∷ tt ∷ i)
v2 = var (skip (skip incl))

t1 : Term 2
t1 =
  def bAdd v0 v1 ,
  def bAdd v2 v2 ,
  v2







