module Lists where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Bool
open import Function
open import Relation.Binary.PropositionalEquality

{- A list of (at least one) lists -}

Lists : (a : Set) → Set
Lists a = List (List a)

listSplit' : {a : Set} → (a → Bool) → List a → List a → Lists a
listSplit' f xs [] = reverse xs ∷ []
listSplit' f xs (y ∷ ys) =
  if f y then
    reverse xs ∷ listSplit' f (y ∷ []) ys
  else
    listSplit' f (y ∷ xs) ys

{-
f returns true for the characters that are supposed to appear
as the first line in a row.
-}

listSplit : {a : Set} → (a → Bool) → List a → Lists a
listSplit f xs = listSplit' f [] xs

maps : {a : Set} → {b : Set} →
  (a → b) → Lists a → Lists b
maps f xss = Data.List.map (Data.List.map f) xss
