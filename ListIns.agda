module ListIns where

open import Data.List
open import Data.Fin
open import Data.Nat
open import Function
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import ListsAppend
open import Util
open import List1
open import Lists

lins : {a : Set} → (xs : List a) → Fin (suc (length xs)) → a → List a
lins xs zero y = y ∷ xs
lins (x ∷ xs) (suc n) y = x ∷ lins xs n y
lins [] (suc n) _ = elimFin0 n

suclength : {a : Set} → List a → ℕ
suclength xs = suc (length xs)

Row : {a : Set} → (xss : Lists a) → Set
Row xss = Fin (length' xss)

Column : {a : Set} → (xss : Lists a) → Row xss → Set
Column xss i = Fin (suclength (elem' xss i))

RowCol : {a : Set} → (xss : Lists a) → Set
RowCol xss = Σ(Row xss) (Column xss)

charLength : {a : Set} → (xss : Lists a) → ℕ
charLength (xs , xss) = length xs + sum (map suclength xss)

charIndex : {a : Set} → (xss : Lists a) → RowCol xss → Fin (charLength xss)
charIndex xss (i , j) = map suclength 

lsins : {a : Set} → (xss : Lists a) → RowCol xss → a → Lists a
lsins xss (i , j) x =
  let
    row = elem' xss i
    row' = lins row j x
  in
    lset' xss i row'

{-
lsinsUnsplit : {a : Set} → {xss : Lists a} → (i : Fin (length' xss)) → (j : Fin (suc (length (elem' xss i)))) → (x : a) →
  listUnsplit (lsins xss i j x) ≡ 
-}
