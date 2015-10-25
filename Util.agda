module Util where

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

{-
fst : {A : Set} → {B : Set} → (A × B) → A
fst (x , _) = x

snd : {A : Set} → {B : Set} → (A × B) → B
snd (_ , y) = y
-}

elimFin0 : {a : Set} → Fin 0 → a
elimFin0 ()

elem : {a : Set} → (xs : List a) → Fin (length xs) → a
elem [] n = elimFin0 n
elem (x ∷ xs) zero = x
elem (x ∷ xs) (suc n) = elem xs n

lset : {a : Set} → (xs : List a) → Fin (length xs) → a → List a
lset [] n _ = elimFin0 n
lset (x ∷ xs) zero y = y ∷ xs
lset (x ∷ xs) (suc i) y = x ∷ lset xs i y

suclength : {a : Set} → List a → ℕ
suclength xs = suc (length xs)

fintake : {a : Set} → (xs : List a) → Fin (suclength xs) → List a
fintake xs zero = []
fintake (x ∷ xs) (suc n) = x ∷ fintake xs n
fintake [] (suc n) = elimFin0 n

imap : {a : Set} → {b : Set} → (xs : List a) → (Fin (length xs) → b) → List b
imap [] f = []
imap (x ∷ xs) f = f zero ∷ imap xs (λ n → f (suc n))

elim0=s : {a : Set} → {n : ℕ} → 0 ≡ suc n → a
elim0=s ()

+≤ : {x : ℕ} → {y : ℕ} → (z : ℕ) →
  x ≤ y → z + x ≤ z + y
+≤ 0 p = p
+≤ (suc z) p = s≤s (+≤ z p)

≤+ : {x : ℕ} → {y : ℕ} → (z : ℕ) →
  x ≤ y → x + z ≤ y + z
≤+ {x} {y} z p = begin
  x + z ≡⟨ +-comm x z ⟩
  z + x ≤⟨ +≤ z p ⟩
  z + y ≡⟨ +-comm z y ⟩
  y + z ∎

sum≤ :
  (xs : List ℕ) →
  (ys : List ℕ) →
  (p0 : length xs ≡ length ys) →
  (∀ (i : Fin (length xs)) → elem xs i ≤ elem ys (subst Fin p0 i)) →
  sum xs ≤ sum ys
sum≤ [] [] p0 p1 = Data.Nat.z≤n
sum≤ (x ∷ xs) (y ∷ ys) p0 p1 =
  let
    x<y = begin
      x ≡⟨ refl ⟩
      elem (x ∷ xs) zero ≤⟨ p1 zero ⟩
      elem (y ∷ ys) (subst Fin p0 zero) ≡⟨ cong (elem (y ∷ ys)) refl ⟩
      elem (y ∷ ys) zero ≡⟨ refl ⟩
      y ∎
    p0' = cancel-+-left 1 p0
    p1' = λ i → begin
      elem xs i ≡⟨ refl ⟩
      elem (x ∷ xs) (raise 1 i) ≤⟨ p1 (raise 1 i) ⟩
      elem (y ∷ ys) (subst Fin p0 (raise 1 i)) ≡⟨ cong (elem (y ∷ ys)) refl ⟩
      elem (y ∷ ys) (raise 1 (subst Fin p0' i)) ≡⟨ refl ⟩
      elem ys (subst Fin p0' i) ∎
    sx<sy = sum≤ xs ys p0' p1'
  in
  begin
    sum (x ∷ xs) ≡⟨ refl ⟩
    x + sum xs ≤⟨ ≤+ (sum xs) x<y ⟩
    y + sum xs ≤⟨ +≤ y sx<sy ⟩
    y + sum ys ≡⟨ refl ⟩
    sum (y ∷ ys)
  ∎
sum≤ [] (y ∷ ys) p0 p1 = elim0=s p0
sum≤ (x ∷ xs) [] p0 p1 = elim0=s (sym p0)
