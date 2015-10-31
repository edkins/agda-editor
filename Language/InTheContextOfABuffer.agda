module InTheContextOfABuffer where

open import Data.Fin using (Fin; raise; toℕ; inject+; inject₁; fromℕ; zero; suc) renaming (_+_ to _F+_)
open import Data.Fin.Properties renaming (_≟_ to finEquality)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _I+_)
open import Data.Vec using (Vec; _++_; lookup)
open import Data.Nat using (ℕ; _+_; _∸_; suc; _≤_; _≤?_)
open import Data.Char using (Char)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Unary renaming (Decidable to _isDecidableProperty)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; Σ)

open import Miscellaneous

bufferLength : ℕ
bufferLength = {!!}

buffer : BufferOfLength bufferLength
buffer = {!!}

PositionWithinTheBuffer : Set
PositionWithinTheBuffer = NaturalNumberNoLargerThan bufferLength

_isAt_ : (i : PositionWithinTheBuffer) → (j : PositionWithinTheBuffer) → Dec (i ≡ j)
_isAt_ i j = finEquality i j

theStartOfTheBuffer : PositionWithinTheBuffer
theStartOfTheBuffer = zero

theEndOfTheBuffer : PositionWithinTheBuffer
theEndOfTheBuffer = fromℕ bufferLength

moveLeftFrom_ifYouCan : PositionWithinTheBuffer → PositionWithinTheBuffer
moveLeftFrom_ifYouCan x =
  checkWhether (x isAt theStartOfTheBuffer)
    (λ xIsAtTheStart → x)
    (λ xIsNotAtTheStart → predecessorOf x whichExistsBecause xIsNotAtTheStart)

moveRightFrom_ifYouCan : PositionWithinTheBuffer → PositionWithinTheBuffer
moveRightFrom_ifYouCan x =
  checkWhether (x isAt theEndOfTheBuffer)
    (λ xIsAtTheEnd → x)
    (λ xIsNotAtTheEnd → successorOf x whichExistsBecause xIsNotAtTheEnd)

characterAt_whichExistsBecause_ : (i : PositionWithinTheBuffer) → i ≢ theEndOfTheBuffer → Char
characterAt_whichExistsBecause_ i iNotAtEnd =
  lookup (tighten i whichExistsBecause iNotAtEnd) buffer

predecessorIsNotAtTheEndGiven : {x : PositionWithinTheBuffer} → (xIsNotAtTheStart : x ≢ theStartOfTheBuffer) →
  (predecessorOf x whichExistsBecause xIsNotAtTheStart) ≢ theEndOfTheBuffer
predecessorIsNotAtTheEndGiven xIsNotAtTheStart =
  predecessorIsNotMaxGiven xIsNotAtTheStart

_atTheStartOfALine : propertyOf PositionWithinTheBuffer
_atTheStartOfALine x =
  checkWhether (x isAt theStartOfTheBuffer)
    (λ xIsAtTheStart → ⊤)
    (λ xIsNotAtTheStart → let
      x' = predecessorOf x whichExistsBecause xIsNotAtTheStart
      ch = characterAt x' whichExistsBecause (predecessorIsNotAtTheEndGiven xIsNotAtTheStart)
    in (ch ≡ '\n'))

countDownFrom_until_ :
   ℕ →
   {p : propertyOf ℕ} →
   ((y : ℕ) → Dec (p y)) →
   ℕ

countDownFrom_until_ 0 _hasProperty = 0

countDownFrom_until_ (suc n) _hasProperty =
  checkWhether ((suc n) hasProperty)
    (λ nHasProperty → suc n)
    (λ otherwise → countDownFrom n until _hasProperty)

position_existsBecause_ : (n : ℕ) → (n ≤ bufferLength) → PositionWithinTheBuffer
position_existsBecause_ n n≤len = n isWithinRange n≤len

_asPropertyOfℕ : propertyOf PositionWithinTheBuffer → propertyOf ℕ
_asPropertyOfℕ p = λ n →
  checkWhether (n ≤? bufferLength)
    (λ n≤len → p (position n existsBecause n≤len))
    (λ otherwise → ⊥)

--decProp₁ : {p : propertyOf PositionWithinTheBuffer} →
--  p isDecidableProperty → (n : ℕ) → n ≤ bufferLength → Dec ((p asPropertyOfℕ) n)
--decProp₁ p n n≤len = p (position n existsBecause n≤len)


_asDecidablePropertyOfℕ : {p : propertyOf PositionWithinTheBuffer} →
  p isDecidableProperty → (p asPropertyOfℕ) isDecidableProperty
_asDecidablePropertyOfℕ {P} p = λ n →
  checkWhether (n ≤? bufferLength)
    (λ n≤len →
      checkWhether (p (position n existsBecause n≤len))
        (λ pIsTrue → {!!})
        (λ pIsFalse → {!!})
    )
    (λ otherwise → {!!})

searchBackwardsFrom_until_ :
   (x : PositionWithinTheBuffer) →
   {p : propertyOf PositionWithinTheBuffer} →
   p isDecidableProperty →
   PositionWithinTheBuffer
searchBackwardsFrom_until_ x property =
  let n = countDownFrom (toℕ x) until (property asDecidablePropertyOfℕ)
  in {!!}
