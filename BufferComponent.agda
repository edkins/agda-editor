module BufferComponent where

open import Data.Fin using (Fin; raise; toℕ; inject+; inject₁; fromℕ; zero; suc) renaming (_+_ to _F+_)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _I+_)
open import Data.Vec using (Vec; _++_; lookup)
open import Data.Nat using (ℕ; _+_; _∸_; suc)
open import Data.Char using (Char)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; Σ)

open import ListUtil
open import FinUtil
open import BufferInterface
open import Component

inTheContextOf : (n : ℕ) → BufferOfLength n → ℕ
inTheContextOf bufferLength buffer =
  let
    PositionWithinTheBuffer : Set
    PositionWithinTheBuffer = NaturalNumberNoLargerThan bufferLength

    _isAt_ : (i : PositionWithinTheBuffer) → (j : PositionWithinTheBuffer) → Dec (i ≡ j)
    _isAt_ i j = i F≟ j

    --_isNotAt_ i j = ¬ (i isAt j)

    theStartOfTheBuffer : PositionWithinTheBuffer
    theStartOfTheBuffer = zero

    theEndOfTheBuffer : PositionWithinTheBuffer
    theEndOfTheBuffer = fmax

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

    propertyOf : Set → Set₁
    propertyOf x = x → Set

    _atTheStartOfALine : propertyOf PositionWithinTheBuffer
    _atTheStartOfALine x =
      checkWhether (x isAt theStartOfTheBuffer)
        (λ xIsAtTheStart → ⊤)
        (λ xIsNotAtTheStart → let
          x' = predecessorOf x whichExistsBecause xIsNotAtTheStart
          ch = characterAt x' whichExistsBecause (predecessorIsNotAtTheEndGiven xIsNotAtTheStart)
        in (ch ≡ '\n'))

    PositionThatIs : (p : propertyOf PositionWithinTheBuffer) → Set
    PositionThatIs p = Σ PositionWithinTheBuffer p

    _whichHasTheRightPropertyBecause_ :
      {p : propertyOf PositionWithinTheBuffer} →
      PositionWithinTheBuffer →
      PositionThatIs p
    _whichHasTheRightPropertyBecause_ x xp = (x , xp)

    searchBackwardsFrom_until_whichIsTrueAtTheStartBecause_ :
       (x : PositionWithinTheBuffer) →
       {p : propertyOf PositionWithinTheBuffer} →
       ((y : PositionWithinTheBuffer) → Dec (p y)) →
       (startHasPropertyP : p theStartOfTheBuffer) →
       PositionThatIs p
    searchBackwardsFrom_until_whichIsTrueAtTheStartBecause_ x _hasPropertyP startHasPropertyP =
      checkWhether (x hasPropertyP)
        (λ xHasPropertyP → x whichHasTheRightPropertyBecause xHasPropertyP)
        (λ otherwise →
        let
          x' = predecessorOf x whichExistsBecause ?
        in
          searchBackwardsFrom_until_whichIsTrueAtTheStartBecause_ x' _hasPropertyP startHasPropertyP)
--          searchBackwardsFrom x' until _hasPropertyP whichIsTrueAtTheStartBecause startHasPropertyP)
  in
    0

{-
findStartOfLine : {n : ℕ} → Fin (suc n) → Vec Char n → Fin (suc n)
findStartOfLine 

insertChars : (n : ℕ) → Vec Char n → BufferState → BufferState
insertChars n ys (BufferS {m} i xs overhang) =
  let
    len = (toℕ i + n) + (m ∸ toℕ i)
    xs' : Vec Char len
    xs' = (vtake xs i ++ ys) ++ vdrop xs i
    i' : Fin (suc len)
    i' = inject+ (m ∸ toℕ i) (fromℕ (toℕ i + n))
  in
    BufferS i' xs' 0

moveChars : ℤ → BufferState → BufferState
moveChars n (BufferS i xs overhang) = BufferS (clampIntToFin (+ toℕ i I+ n)) xs 0

moveLines : ℤ → BufferState → BufferState


bufferFunction : BufferAction → BufferState → BufferState
bufferFunction (InsertChars n ys) buf = insertChars n ys buf
bufferFunction (MoveChars n) buf = moveChars n buf
bufferFunction (MoveLines n) buf = moveLines n buf

bufferComponent : Component BufferAction BufferState
bufferComponent = stateBroadcast bufferFunction
-}
