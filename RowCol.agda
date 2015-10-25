module RowCol where

open import Data.List
open import Data.Fin using (Fin; zero; suc; inject₁; fromℕ; toℕ; compare; less; equal; greater; _<_)
open import Data.Fin.Properties using (prop-toℕ-≤)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; pred)
open import Data.Nat.Properties using (≤-step; n≤1+n)
open import Function
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary
open Data.Nat.≤-Reasoning

open import FinUtil
open import ListsAppend
open import ListUtil
open import List1
open import Lists

Row : {a : Set} → (xss : Lists a) → Set
Row xss = Fin (length' xss)

Column : {a : Set} → (xss : Lists a) → Row xss → Set
Column xss i = Fin (suclength (elem' xss i))

RowCol : {a : Set} → (xss : Lists a) → Set
RowCol xss = Σ(Row xss) (Column xss)

suclengthsum : {a : Set} → (xss : List (List a)) → ℕ
suclengthsum xss = sum (map suclength xss)

charSucLength : {a : Set} → (xss : Lists a) → ℕ
charSucLength xss = sum' (map' suclength xss)

charLength : {a : Set} → (xss : Lists a) → ℕ
charLength xss = pred (charSucLength xss)

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

amountTakenHelper : {a : Set} → (xss : Lists a) → (ij : RowCol xss) → (i' : Row xss) → CmpWitness i' (proj₁ ij) → ℕ
amountTakenHelper xss (i , j) i' (Lt _) = suclength (elem' xss i')
amountTakenHelper xss (i , j) i' (Eq _) = toℕ j
amountTakenHelper xss (i , j) i' (Gt _) = 0

amountTaken : {a : Set} → (xss : Lists a) → RowCol xss → (i : Row xss) → ℕ
amountTaken xss (i , j) i' =
  amountTakenHelper xss (i , j) i' (cmpFin i' i)
{-  case cmpFin i' i of λ{
    (Lt _) → suclength (elem' xss i')
  ; (Eq _) → toℕ j
  ; (Gt _) → 0
  }-}

amountTaken≤Helper : {a : Set} → (xss : Lists a) → (ij : RowCol xss) → (i' : Row xss) → (c : CmpWitness i' (proj₁ ij)) →
  amountTakenHelper xss ij i' c ≤ suclength (elem' xss i')
amountTaken≤Helper xss (i , j) i' (Lt _) = ≤-refl
amountTaken≤Helper xss (i , j) i' (Eq p0) =
  let
    p0' : suclength (elem' xss i) ≡ suclength (elem' xss i')
    p0' = cong (λ i0 → suclength (elem' xss i0)) (sym p0)
    j' = finsubst p0' j
    j=j' : toℕ j' ≡ toℕ j
    j=j' = finsubst-toℕ p0' j
  in begin
    amountTakenHelper xss (i , j) i' (Eq p0) ≡⟨ refl ⟩
    toℕ j ≡⟨ sym j=j' ⟩
    toℕ j' ≤⟨ prop-toℕ-≤ j' ⟩
    length (elem' xss i') ≤⟨ n≤1+n _ ⟩
    suclength (elem' xss i') ∎
amountTaken≤Helper xss (i , j) i' (Gt _) = z≤n

amountTaken≤ : {a : Set} → (xss : Lists a) → (ij : RowCol xss) → (i' : Row xss) →
  amountTaken xss ij i' ≤ suclength (elem' xss i')
amountTaken≤ xss (i , j) i' = amountTaken≤Helper xss (i , j) i' (cmpFin i' i)

charIndex : {a : Set} → (xss : Lists a) → RowCol xss → Fin (charSucLength xss)
charIndex xss (i , j) =
  let
    f = amountTaken xss (i , j)
    lss = map' suclength xss
    yss = imap' xss f
    lx=ll : length' xss ≡ length' lss
    lx=ll = sym (length-map' suclength xss)
    ly=lx : length' yss ≡ length' xss
    ly=lx = length-imap' xss f
    ly=ll : length' yss ≡ length' lss
    ly=ll = trans ly=lx lx=ll
    p1 : (∀ (i' : Fin (length' yss)) → elem' yss i' ≤ elem' lss (finsubst ly=ll i'))
    p1 = λ i' → begin
      elem' yss i'
        ≡⟨ elem-imap-sym' xss f i' ⟩
      amountTaken xss (i , j) (finsubst ly=lx i')
        ≤⟨ amountTaken≤ xss (i , j) (finsubst ly=lx i') ⟩
      suclength (elem' xss (finsubst ly=lx i'))
        ≡⟨ sym (elem-map' suclength xss (finsubst ly=lx i')) ⟩
      elem' lss (finsubst lx=ll (finsubst ly=lx i'))
        ≡⟨ cong (elem' lss) (finsubst-trans ly=lx lx=ll i') ⟩
      elem' lss (finsubst ly=ll i') ∎
    p0 = sum'≤ yss lss ly=ll p1
  in
    {!!}
