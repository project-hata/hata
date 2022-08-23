
module Verification.Application.CompGen.Languages.CubeLang.Definition where

open import Verification.Conventions hiding (_⊔_; _==_ ; refl ; zero)
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





-- _==_ = _≣_

-- infixl 5 _==_

-- record isSemigroup (A : 𝒰₀) : 𝒰₀ where
--   field
--     _⋆_ : A -> A -> A
--     assoc-⋆-l : ∀(a b c : A) -> (a ⋆ b) ⋆ c == a ⋆ (b ⋆ c)

-- assoc-+-l-ℕ : ∀(a b c : ℕ) -> (a +-ℕ b) +-ℕ c == a +-ℕ (b +-ℕ c)
-- assoc-+-l-ℕ = {!!} -- this needs to be proven

-- instance
--   isSemigroupNat : isSemigroup ℕ
--   isSemigroupNat =
--     record
--     { _⋆_ = _+-ℕ_
--     ; assoc-⋆-l = assoc-+-l-ℕ -- we put the proof into the record here
--     }





--------------------------------------------
-- sketch
--
-- Our metabuilder gets AgdaHaskellRust (CompGen) projects.
-- We define build dependencies formally, because we have:
--  - MetaBuilder has build dependencies for AgdaC -> StackC
--  - CompGen has build dependencies for




-- we say that there are -EX-> arrow that are not quite exponentiable
-- we have `agdac : AgdaSource A -Ex-> HaskellSource B`
--            where A ~ B have same representations
--                  A B : ExTypes
-- we have `stack : HaskellSource A -Ex-> A`
--
-- if `A : ExType, a : A` then `a` can be executed
--
-- we have `cubegen : AgdaSource (ExWrite (RustSource (CubeSource X -Ex-> X)))`
-- AgdaC -> StackC -> CompGen ->
--
--
--
--
--
--
--
--




data _==_ {a} {A : 𝒰 a} (x : A) : A → 𝒰 a where
  refl : x == x

data ⊥ : 𝒰₀ where

infixl 5 _==_

_≠_ : {A : 𝒰₀} → A → A → 𝒰₀
a ≠ b = a == b → ⊥


record isField (K : 𝒰₀) : 𝒰₀ where
  field
    zero : K
    one  : K

    _·_ : K → K → K
    _+_ : K → K → K

    assoc-+-l : ∀(a b c : K) → (a + b) + c == a + (b + c)
    assoc-·-l : ∀(a b c : K) → (a · b) · c == a · (b · c)

    comm-+ : ∀(a b : K) → a + b == b + a
    comm-· : ∀(a b : K) → a · b == b · a

    - : K → K
    mulInv : (a : K) → (proof : a ≠ zero) → K

    _/_ : K → K

    plusZero : ∀(a : K) → a + zero == a
    timesOne : ∀(a : K) → a · one == a

    aMinusAIsZero   : ∀(a : K) → a + (- a) == zero

    distributive : ∀(a b c : K) → a · (b + c) == (a · b) + (a · c)

record Vector (K V : 𝒰₀) : 𝒰₀ where
  field
    scalar : isField K
    vector : V

record isKVectorSpace (K V : 𝒰₀) : 𝒰₀ where
  field
    zero : Vector K V

    _++_ : Vector K V → Vector K V → Vector K V
    _∗_ : K → Vector K V → Vector K V

    assoc-++-l : ∀(a b c : Vector K V) → (a ++ b) ++ c == a ++ (b ++ c)

    comm-++ : ∀(a b : Vector K V) → a ++ b == b ++ a

