module Util where

open import Data.Product
open import Data.Nat using (ℕ; _≤_; suc; _+_; s≤s; pred; z≤n; _<_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; raise; toℕ; fromℕ)
open import Data.Fin.Properties
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

≤+≤ : {x : ℕ} → {y : ℕ} → {x' : ℕ} → {y' : ℕ} →
  x ≤ x' → y ≤ y' → x + y ≤ x' + y'
≤+≤ {x} {y} {x'} {y'} p0 p1 = begin
  x + y ≤⟨ +≤ x p1 ⟩
  x + y' ≤⟨ ≤+ y' p0 ⟩
  x' + y' ∎

sucinj : {m : ℕ} → {n : ℕ} → suc m ≡ suc n → m ≡ n
sucinj p0 = cong pred p0

finsubst : {m : ℕ} → {n : ℕ} → m ≡ n → Fin m → Fin n
finsubst {suc m} {suc n} p0 zero = zero
finsubst {suc m} {suc n} p0 (suc k) = suc (finsubst (sucinj p0) k)
finsubst {0} _ n = elimFin0 n
finsubst {suc m} {0} p0 _ = elim0=s (sym p0)

sum≤ :
  (xs : List ℕ) →
  (ys : List ℕ) →
  (p0 : length xs ≡ length ys) →
  (∀ (i : Fin (length xs)) → elem xs i ≤ elem ys (finsubst p0 i)) →
  sum xs ≤ sum ys
sum≤ [] [] p0 p1 = Data.Nat.z≤n
sum≤ (x ∷ xs) (y ∷ ys) p0 p1 =
  let
    x<y = begin
      x ≡⟨ refl ⟩
      elem (x ∷ xs) zero ≤⟨ p1 zero ⟩
      elem (y ∷ ys) (finsubst p0 zero) ≡⟨ refl ⟩
      elem (y ∷ ys) zero ≡⟨ refl ⟩
      y ∎
    p0' = cancel-+-left 1 p0
    p1' = λ i → begin
      elem xs i ≡⟨ refl ⟩
      elem (x ∷ xs) (raise 1 i) ≤⟨ p1 (raise 1 i) ⟩
      elem (y ∷ ys) (finsubst p0 (raise 1 i)) ≡⟨ refl ⟩
      elem (y ∷ ys) (raise 1 (finsubst p0' i)) ≡⟨ refl ⟩
      elem ys (finsubst p0' i) ∎
    sx<sy = sum≤ xs ys p0' p1'
  in
    ≤+≤ x<y sx<sy
sum≤ [] (y ∷ ys) p0 p1 = elim0=s p0
sum≤ (x ∷ xs) [] p0 p1 = elim0=s (sym p0)

≤-refl : (n : ℕ) → n ≤ n
≤-refl 0 = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

z<s : {n : ℕ} → 0 < suc n
z<s {n} = s≤s z≤n

s<s : {m : ℕ} → {n : ℕ} → m < n → suc m < suc n
s<s = s≤s

toℕ-suc : {n : ℕ} → (a : Fin n) → suc (toℕ a) ≡ toℕ (suc a)
toℕ-suc a = refl

fsucinj : {n : ℕ} → {a : Fin n} → {b : Fin n}
  → suc a ≡ suc b → a ≡ b
fsucinj {n} {a} {b} p0 = toℕ-injective (sucinj (cong toℕ p0))
