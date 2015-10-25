module List1 where

open import Data.List
open import Data.List.Properties
open import Data.Product
open import Data.Nat using (ℕ; _≤_; suc)
open import Data.Fin using (Fin; zero; suc)
open import FinUtil
open import ListUtil
open import Relation.Binary.PropositionalEquality

{- A list containing at least one element -}

List' : (a : Set) → Set
List' a = (a × List a)

head' : {a : Set} → List' a → a
head' (x , _) = x

tolist' : {a : Set} → List' a → List a
tolist' (x , xs) = x ∷ xs

tail' : {a : Set} → List' a → List a
tail' (_ , xs) = xs

cons' : {a : Set} → a → List' a → List' a
cons' x (y , ys) = (x , y ∷ ys)

last'' : {a : Set} → a → List a → a
last'' x [] = x
last'' x (y ∷ ys) = last'' y ys

last' : {a : Set} → List' a → a
last' (x , xs) = last'' x xs

init'' : {a : Set} → a → List a → List a
init'' x [] = []
init'' x (y ∷ ys) = x ∷ init'' y ys

init' : {a : Set} → List' a → List a
init' (x , xs) = init'' x xs

append' : {a : Set} → List a → List' a → List' a
append' [] ys = ys
append' (x ∷ xs) ys = cons' x (append' xs ys)

length' : {a : Set} → List' a → ℕ
length' (x , xs) = length (x ∷ xs)

elem' : {a : Set} → (xs : List' a) → Fin (length' xs) → a
elem' (x , xs) i = elem (x ∷ xs) i

lset' : {a : Set} → (xs : List' a) → Fin (length' xs) → a → List' a
lset' (x , xs) zero y = (y , xs)
lset' (x , xs) (suc i) y = (x , lset xs i y)

fintake' : {a : Set} → (xs : List' a) → Fin (suc (length' xs)) → List a
fintake' (x , xs) n = fintake (x ∷ xs) n

imap' : {a : Set} → {b : Set} → (xs : List' a) → (Fin (length' xs) → b) → List' b
imap' (x , xs) f = (f zero , imap xs (λ n → f (suc n)))

length-imap' : {a : Set} → {b : Set} → (xs : List' a) → (f : Fin (length' xs) → b) →
  length' (imap' xs f) ≡ length' xs
length-imap' (x , xs) f = cong suc (length-imap xs (λ n → f (suc n)))

elem-imap' : {a : Set} → {b : Set} → (xs : List' a) → (f : Fin (length' xs) → b) → (i : Fin (length' xs)) →
  elem' (imap' xs f) (finsubst (sym (length-imap' xs f)) i) ≡ f i
elem-imap' (x , xs) f zero = refl
elem-imap' (x , xs) f (suc i) = elem-imap xs (λ n → f (suc n)) i

elem-imap-sym' : {a : Set} → {b : Set} → (xs : List' a) → (f : Fin (length' xs) → b) → (i : Fin (length' (imap' xs f))) →
  elem' (imap' xs f) i ≡ f (finsubst (length-imap' xs f) i)
elem-imap-sym' xs f i =
  let
    a=b = cong (elem' (imap' xs f)) (finsubst-subst (length-imap' xs f) (sym (length-imap' xs f)) i)
    c=b = elem-imap' xs f (finsubst (length-imap' xs f) i)
  in
    trans (sym a=b) c=b

sum' : List' ℕ → ℕ
sum' (x , xs) = sum (x ∷ xs)

sum'≤ :
  (xs : List' ℕ) →
  (ys : List' ℕ) →
  (p0 : length' xs ≡ length' ys) →
  (∀ (i : Fin (length' xs)) → elem' xs i ≤ elem' ys (finsubst p0 i)) →
  sum' xs ≤ sum' ys
sum'≤ (x , xs) (y , ys) p0 p1 =
  sum≤ (x ∷ xs) (y ∷ ys) p0 p1

map' : {a : Set} → {b : Set} → (a → b) → List' a → List' b
map' f (x , xs) = (f x , Data.List.map f xs)

length-map' : {a : Set} → {b : Set} → (f : a → b) → (xs : List' a) →
  length' (map' f xs) ≡ length' xs
length-map' f (x , xs) = cong suc (length-map f xs)

elem-map' : {a : Set} → {b : Set} → (f : a → b) → (xs : List' a) → (i : Fin (length' xs)) →
  elem' (map' f xs) (finsubst (sym (length-map' f xs)) i) ≡ f (elem' xs i)
elem-map' f (x , xs) i = elem-map f (x ∷ xs) i
