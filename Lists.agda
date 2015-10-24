module Lists where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import List1

{- A list of (at least one) lists -}

Lists : (a : Set) → Set
Lists a = List' (List a)

hdnew : {a : Set} → Lists a → Lists a
hdnew xss = cons' [] xss

hdcons : {a : Set} → a → Lists a → Lists a
hdcons x (xs , xss) = (x ∷ xs , xss)

listSplit : {a : Set} → List (Maybe a) → Lists a
listSplit [] = ( [] , [] )
listSplit (nothing ∷ xs) = hdnew (listSplit xs)
listSplit ((just x) ∷ xs) = hdcons x (listSplit xs)

lmap = Data.List.map

listUnsplit' : {a : Set} → List a → List (List a) → List (Maybe a)
listUnsplit' xs [] = lmap just xs
listUnsplit' xs (ys ∷ yss) = lmap just xs ++ (nothing ∷ listUnsplit' ys yss)

listUnsplit : {a : Set} → Lists a → List (Maybe a)
listUnsplit (xs , xss) = listUnsplit' xs xss

hdconsSplit : {a : Set} → (x : a) → (xs : List (Maybe a)) →
  (hdcons x (listSplit xs) ≡ listSplit (just x ∷ xs))
hdconsSplit x xs = refl

hdconsUnsplit : {a : Set} → (x : a) → (xss : Lists a) →
  listUnsplit (hdcons x xss) ≡ just x ∷ listUnsplit xss
hdconsUnsplit x (xs , []) = refl
hdconsUnsplit x (xs , ys ∷ yss) = refl

hdnewSplit : {a : Set} → (xs : List (Maybe a)) →
  listSplit (nothing ∷ xs) ≡ hdnew (listSplit xs)
hdnewSplit xs = refl

hdnewUnsplit : {a : Set} → (xss : Lists a) →
  listUnsplit (hdnew xss) ≡ nothing ∷ listUnsplit xss
hdnewUnsplit xss = refl

listSplitUnsplit : {a : Set} → (xs : List (Maybe a)) →
  listUnsplit (listSplit xs) ≡ xs
listSplitUnsplit [] = refl
listSplitUnsplit (nothing ∷ xs) =
  cong (λ ys → nothing ∷ ys) (listSplitUnsplit xs)
listSplitUnsplit (just x ∷ xs) = trans (hdconsUnsplit x (listSplit xs)) (cong (λ ys → just x ∷ ys) (listSplitUnsplit xs))

listSplitJust : {a : Set} → (xs : List a) →
  listSplit (lmap just xs) ≡ (xs , [])
listSplitJust [] = refl
listSplitJust (x ∷ xs) = cong (hdcons x) (listSplitJust xs)

listUnsplitSplit' : {a : Set} → (xs : List a) → (xss : List (List a)) →
  listSplit (listUnsplit (xs , xss)) ≡ (xs , xss)
listUnsplitSplit' xs [] = listSplitJust xs
listUnsplitSplit' [] (ys ∷ yss) =
  cong hdnew (listUnsplitSplit' ys yss)
listUnsplitSplit' (x ∷ xs) (ys ∷ yss) =
  cong (hdcons x) (listUnsplitSplit' xs (ys ∷ yss))

listUnsplitSplit : {a : Set} → (xss : Lists a) →
  listSplit (listUnsplit xss) ≡ xss
listUnsplitSplit (xs , xss) = listUnsplitSplit' xs xss
