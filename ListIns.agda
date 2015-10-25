module ListIns where

open import Data.List
open import Data.Fin using (Fin; zero; suc; inject₁; fromℕ; toℕ; compare; less; equal; greater; _<_)
open import Data.Fin.Properties using (prop-toℕ-≤)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-step)
open import Function
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; Σ; _,_)
open import Relation.Binary

open import ListsAppend
open import Util
open import List1
open import Lists

lins : {a : Set} → (xs : List a) → Fin (suc (length xs)) → a → List a
lins xs zero y = y ∷ xs
lins (x ∷ xs) (suc n) y = x ∷ lins xs n y
lins [] (suc n) _ = elimFin0 n

Row : {a : Set} → (xss : Lists a) → Set
Row xss = Fin (length' xss)

Column : {a : Set} → (xss : Lists a) → Row xss → Set
Column xss i = Fin (suclength (elem' xss i))

RowCol : {a : Set} → (xss : Lists a) → Set
RowCol xss = Σ(Row xss) (Column xss)

suclengthsum : {a : Set} → (xss : List (List a)) → ℕ
suclengthsum xss = sum (map suclength xss)

charLength : {a : Set} → (xss : Lists a) → ℕ
charLength (xs , xss) = length xs + suclengthsum xss

rowLength : {a : Set} → (xss : Lists a) → (i : Row xss) → Column xss i
rowLength xss i = fromℕ (length (elem' xss i))

data CmpWitness {n : ℕ} (a : Fin n) (b : Fin n) : Set where
  Lt : (a < b) → CmpWitness a b
  Eq : (a ≡ b) → CmpWitness a b
  Gt : (b < a) → CmpWitness a b

cmpFin : {n : ℕ} → (a : Fin n) → (b : Fin n) → CmpWitness a b
cmpFin zero zero = Eq refl
cmpFin (suc m) zero = Gt z<s
cmpFin zero (suc n) = Lt z<s
cmpFin (suc m) (suc n) = case cmpFin m n of λ{
    (Lt p0) → Lt (s<s p0)
  ; (Eq p0) → Eq (cong suc p0)
  ; (Gt p0) → Gt (s<s p0)
  }

amountTaken : {a : Set} → (xss : Lists a) → RowCol xss → (i : Row xss) → ℕ
amountTaken xss (i , j) i' =
  case cmpFin i' i of λ{
    (Lt _) → suclength (elem' xss i')
  ; (Eq _) → toℕ j
  ; (Gt _) → 0
  }

amountTaken≤ : {a : Set} → (xss : Lists a) → (ij : RowCol xss) → (i' : Row xss) →
  amountTaken xss ij i' ≤ suclength (elem' xss i')
amountTaken≤ xss (i , j) i' = case cmpFin i' i of λ{
   (Lt p0) → {!!}
 ; (Eq p0) → {!!}
 ; (Gt p0) → {!!}
 }

charIndex : {a : Set} → (xss : Lists a) → RowCol xss → Fin (charLength xss)
charIndex xss (i , j) =
  let
    n = sum' (imap' xss (amountTaken xss (i , j)))
  in
    {!!}

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
