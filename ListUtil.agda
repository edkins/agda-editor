module ListUtil where

open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; _≤_; suc; _∸_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; _∷_; init; [])
open import Data.List using (List; length; _∷_; map; sum; [])
open import Data.List.Properties
open import Data.Product using (_×_; _,_)
open Data.Nat.≤-Reasoning
open import FinUtil

upd : {a : Set} → {n : ℕ} → Fin n → (a → a) → Vec a n → Vec a n
upd zero f (x ∷ xs) = f x ∷ xs
upd (suc n) f (x ∷ xs) = x ∷ upd n f xs

ins : {a : Set} → {n : ℕ} → Fin n → a → Vec a n → Vec a n
ins zero e xs = e ∷ init xs
ins (suc n) e (x ∷ xs) = x ∷ ins n e xs

ins+ : {a : Set} → {n : ℕ} → Fin (suc n) → a → Vec a n → Vec a (suc n)
ins+ zero e xs = e ∷ xs
ins+ (suc n) e [] = elimFin0 n
ins+ (suc n) e (x ∷ xs) = x ∷ ins+ n e xs

elem : {a : Set} → (xs : List a) → Fin (length xs) → a
elem [] n = elimFin0 n
elem (x ∷ xs) zero = x
elem (x ∷ xs) (suc n) = elem xs n

elem-map : {a : Set} → {b : Set} → (f : a → b) → (xs : List a) → (i : Fin (length xs)) →
  elem (map f xs) (finsubst (sym (length-map f xs)) i) ≡ f (elem xs i)
elem-map _ [] n = elimFin0 n
elem-map f (x ∷ xs) zero = refl
elem-map f (x ∷ xs) (suc n) = elem-map f xs n

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

length-imap : {a : Set} → {b : Set} → (xs : List a) → (f : Fin (length xs) → b) →
  length (imap xs f) ≡ length xs
length-imap [] f = refl
length-imap (x ∷ xs) f = cong suc (length-imap xs (λ n → f (suc n)))

elem-imap : {a : Set} → {b : Set} → (xs : List a) → (f : Fin (length xs) → b) → (i : Fin (length xs)) →
  elem (imap xs f) (finsubst (sym (length-imap xs f)) i) ≡ f i
elem-imap [] _ i = elimFin0 i
elem-imap (x ∷ xs) f zero = refl
elem-imap (x ∷ xs) f (suc i) = elem-imap xs (λ n → f (suc n)) i

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
      elem (x ∷ xs) (suc i) ≤⟨ p1 (suc i) ⟩
      elem (y ∷ ys) (finsubst p0 (suc i)) ≡⟨ refl ⟩
      elem (y ∷ ys) (suc (finsubst p0' i)) ≡⟨ refl ⟩
      elem ys (finsubst p0' i) ∎
    sx<sy = sum≤ xs ys p0' p1'
  in
    ≤+≤ x<y sx<sy
sum≤ [] (y ∷ ys) p0 p1 = elim0=s p0
sum≤ (x ∷ xs) [] p0 p1 = elim0=s (sym p0)

mapIndices' : {a : Set} → {b : Set} →
  (a → ℕ → b) → List a → ℕ → List b
mapIndices' f [] i = []
mapIndices' f (x ∷ xs) i = f x i ∷ mapIndices' f xs (suc i)

mapIndices : {a : Set} → {b : Set} →
  (a → ℕ → b) → List a → List b
mapIndices f xs = mapIndices' f xs 0

withIndices : {a : Set} → List a → List (a × ℕ)
withIndices xs = mapIndices _,_ xs

vecTake : {a : Set} →
  (n : ℕ) → a → List a → Vec a n
vecTake 0 _ _ = []
vecTake (suc n) x [] = x ∷ vecTake n x []
vecTake (suc n) x (y ∷ ys) = y ∷ vecTake n x ys

vtake : {a : Set} → {n : ℕ} → Vec a n → (m : Fin (suc n)) → Vec a (toℕ m)
vtake xs zero = []
vtake [] (suc m) = elimFin0 m
vtake (x ∷ xs) (suc m) = x ∷ vtake xs m

vdrop : {a : Set} → {n : ℕ} → Vec a n → (m : Fin (suc n)) → Vec a (n ∸ toℕ m)
vdrop xs zero = xs
vdrop [] (suc m) = elimFin0 m
vdrop (x ∷ xs) (suc m) = vdrop xs m

lins : {a : Set} → (xs : List a) → Fin (suc (length xs)) → a → List a
lins xs zero y = y ∷ xs
lins (x ∷ xs) (suc n) y = x ∷ lins xs n y
lins [] (suc n) _ = elimFin0 n
