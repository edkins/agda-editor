module List1 where

open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Util

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
length' (x , xs) = suc (length xs)

elem' : {a : Set} → (xs : List' a) → Fin (length' xs) → a
elem' (x , xs) zero = x
elem' (x , xs) (suc i) = elem xs i

lset' : {a : Set} → (xs : List' a) → Fin (length' xs) → a → List' a
lset' (x , xs) zero y = (y , xs)
lset' (x , xs) (suc i) y = (x , lset xs i y)
