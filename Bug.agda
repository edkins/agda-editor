module Bug where

open import Data.Product
open import Data.Nat using (ℕ; _≤_; suc; _+_; s≤s)
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; raise)
open import Data.Vec using (Vec; init; _∷_)
open import Data.Maybe
open import Data.List
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Data.Nat.Properties.Simple
open Data.Nat.≤-Reasoning

elimFin0 : {a : Set} → Fin 0 → a
elimFin0 ()

elem : {a : Set} → (xs : List a) → Fin (length xs) → a
elem [] n = elimFin0 n
elem (x ∷ xs) zero = x
elem (x ∷ xs) (suc n) = elem xs n

foo : (x : ℕ) → (y : ℕ) → (xs : List ℕ) → (ys : List ℕ) → (p0 : length (x ∷ xs) ≡ length (y ∷ ys)) →
  elem (y ∷ ys) (subst Fin p0 zero) ≡ elem (y ∷ ys) zero
foo x y xs ys p0 = cong (elem (y ∷ ys)) refl
