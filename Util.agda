module Util where

open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Maybe
open import Function

upd : {a : Set} → {n : ℕ} → Fin n → (a → a) → Vec a n → Vec a n
upd zero f (x ∷ xs) = f x ∷ xs
upd (suc n) f (x ∷ xs) = x ∷ upd n f xs

ins : {a : Set} → {n : ℕ} → Fin n → a → Vec a n → Vec a n
ins zero e xs = e ∷ init xs
ins (suc n) e (x ∷ xs) = x ∷ ins n e xs

next : {n : ℕ} → Fin n → Maybe (Fin n)
next {0} impossible = nothing
next {1} x = nothing
next {suc (suc n)} zero = just (suc zero)
next {suc (suc n)} (suc x) = case next x of λ
  { nothing → nothing
  ; (just y) → just (suc y)
  }

tozero : {n : ℕ} → Fin n → Fin n
tozero {0} impossible = impossible
tozero {suc n} x = zero

fst : {A : Set} → {B : Set} → (A × B) → A
fst (x , _) = x

snd : {A : Set} → {B : Set} → (A × B) → B
snd (_ , y) = y
