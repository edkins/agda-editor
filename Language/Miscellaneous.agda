module Miscellaneous where

open import Data.Fin using (Fin; raise; toℕ; inject+; inject₁; fromℕ; zero; suc; pred) renaming (_+_ to _F+_)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _I+_)
open import Data.Vec using (Vec; _++_; lookup)
open import Data.Nat using (ℕ; _+_; _∸_; suc)
open import Data.Char using (Char)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; Σ)

BufferOfLength : ℕ → Set
BufferOfLength n = Vec Char n

NaturalNumberNoLargerThan : ℕ → Set
NaturalNumberNoLargerThan n = Fin (suc n)

reconsider_because_ : {a : Set} → {p : Set} → ¬ p → p → a
reconsider_because_ ¬p p = ⊥-elim (¬p p)

reconsider_becauseRangeIsZero : {a : Set} → Fin 0 → a
reconsider_becauseRangeIsZero ()

propertyOf : Set → Set₁
propertyOf x = x → Set

predecessorOf_whichExistsBecause_ : {n : ℕ} → (x : Fin (suc n)) → x ≢ zero → Fin (suc n)
predecessorOf_whichExistsBecause_ zero p = ⊥-elim (p refl)
predecessorOf_whichExistsBecause_ (suc n) _ = inject₁ n

--applyFunction_toBothSidesOf_observingThat_and_ : {a : Set} → {b : Set} → {p : propertyOf a} → {x : a} → {y : a} →
--  (f : (z : a) → p z → b) → (x ≡ y) → (px : p x) → (py : p y) → f x px ≡ f y py
--applyFunction_toBothSidesOf_observingThat_and_ f eq px py = {!!}

zeroIsNotASuccessor : {n : ℕ} → {x : Fin n} → zero ≢ suc x
zeroIsNotASuccessor ()

successorsAreEqual : {n : ℕ} → (x : Fin n) → (y : Fin n) → (p : suc {n} x ≡ suc {n} y) → x ≡ y
successorsAreEqual {0} x y p = reconsider x becauseRangeIsZero
successorsAreEqual {suc n} x y p = cong (pred {suc n}) p

inject₁≠max : {n : ℕ} → (x : Fin n) → inject₁ x ≢ fromℕ n
inject₁≠max {suc n} zero = λ p → (zeroIsNotASuccessor {suc n} {fromℕ n}) p
inject₁≠max {suc n} (suc x) = λ p → inject₁≠max x (successorsAreEqual (inject₁ x) (fromℕ n) p)

predecessorIsNotMaxGiven : {n : ℕ} → {x : Fin (suc n)} → (x≠0 : x ≢ zero) →
  (predecessorOf x whichExistsBecause x≠0) ≢ fromℕ n
predecessorIsNotMaxGiven {n} {zero} x≠0 = reconsider x≠0 because refl
predecessorIsNotMaxGiven {0} {suc x} x≠0 = reconsider x becauseRangeIsZero
predecessorIsNotMaxGiven {suc n} {suc x} x≠0 = inject₁≠max x

successorOf_whichExistsBecause_ : {n : ℕ} → (x : Fin (suc n)) → x ≢ fromℕ n → Fin (suc n)
successorOf_whichExistsBecause_ {0} zero p = ⊥-elim (p refl)
successorOf_whichExistsBecause_ {0} {suc x} p = reconsider x becauseRangeIsZero
successorOf_whichExistsBecause_ {suc n} zero p = suc zero
successorOf_whichExistsBecause_ {suc n} {suc x} p = suc (successorOf x whichExistsBecause (λ q → p (cong suc q)))

tighten_whichExistsBecause_ : {n : ℕ} → (x : Fin (suc n)) → x ≢ fromℕ n → Fin n
tighten_whichExistsBecause_ {0} zero p = ⊥-elim (p refl)
tighten_whichExistsBecause_ {0} {suc x} p = reconsider x becauseRangeIsZero
tighten_whichExistsBecause_ {suc n} zero p = zero
tighten_whichExistsBecause_ {suc n} {suc x} p = suc (tighten x whichExistsBecause (λ q → p (cong suc q)))

checkWhether : ∀ {ℓ} → {a : Set ℓ} → {proposition : Set} → Dec proposition → (proposition → a) → (¬ proposition → a) → a
checkWhether question f g = case question of λ{
  (yes itIs) → f itIs
  ; (no itIsnt) → g itIsnt
  }
