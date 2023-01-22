
module Verification.Workspace.PTA.example-2023-01-20 where

open import Verification.Conventions hiding (Bool ; _+-ℕ_)

_∘_ : ∀{A B C : 𝒰 𝑖} -> (B -> C) -> (A -> B) -> A -> C
_∘_ g f = λ x -> g (f x)

id : ∀{A : 𝒰 𝑖} -> A -> A
id a = a

comp' : (A : 𝒰 𝑖) -> (f : A -> A) -> ℕ -> A -> A
comp' A f zero = id
comp' A f (suc n) = f ∘ comp' A f n

_+-ℕ_ : ℕ -> ℕ -> ℕ
zero +-ℕ n = n
suc m +-ℕ n = suc (m +-ℕ n)

assoc-add : (m n k : ℕ) -> (m +-ℕ n) +-ℕ k ≣ m +-ℕ (n +-ℕ k)
assoc-add zero n k = refl
assoc-add (suc m) n k = cong-Str suc (assoc-add m n k)

monoid-homomorphism : (A : 𝒰₀) -> (f : A -> A) -> (m n : ℕ) -> comp' A f (m +-ℕ n) ≣ comp' A f m ∘ comp' A f n
monoid-homomorphism A f zero n = refl-≣
monoid-homomorphism A f (suc m) n = let P = (monoid-homomorphism A f m n)
                                    in ?
                                    -- cong-Str (λ g -> f ∘ g) P
                                    -- cong-Str (comp' A f (suc (m +-ℕ n)))
identity-proof : (A : 𝒰₀) -> (f : A -> A) -> comp' A f zero ≣ id
identity-proof A f = refl-≣


