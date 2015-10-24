module ListsAppend where

open import Data.List
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import List1
open import Lists

lsappend' : {a : Set} → List a → List (List a) → Lists a → Lists a
lsappend' xs [] (ys , yss) = (xs ++ ys , yss)
lsappend' xs (xs' ∷ xss) yss = cons' xs (lsappend' xs' xss yss)

lsappend : {a : Set} → Lists a → Lists a → Lists a
lsappend (xs , xss) yss = lsappend' xs xss yss

lsappendCons : {a : Set} → (x : a) → (xss : Lists a) → (yss : Lists a) →
  lsappend (hdcons x xss) yss ≡ hdcons x (lsappend xss yss)
lsappendCons x (xs , []) yss = refl
lsappendCons x (xs , xs' ∷ xss) yss = refl

lsappendlistSplit : {a : Set} → (xs : List (Maybe a)) → (ys : List (Maybe a)) →
  lsappend (listSplit xs) (listSplit ys) ≡ listSplit (xs ++ ys)
lsappendlistSplit [] ys = refl
lsappendlistSplit (nothing ∷ xs) ys = cong hdnew (lsappendlistSplit xs ys)
lsappendlistSplit (just x ∷ xs) ys =
  let
    p0 = cong (hdcons x) (lsappendlistSplit xs ys)
    p1 = lsappendCons x (listSplit xs) (listSplit ys)
  in trans p1 p0
