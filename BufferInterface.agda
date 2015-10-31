
module BufferInterface where

open import Data.Char using (Char)
open import Data.Nat using (ℕ; suc)
open import Data.Integer using (ℤ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

data BufferAction : Set where
  InsertChars : (n : ℕ) → Vec Char n → BufferAction
  MoveChars : ℤ → BufferAction
  MoveLines : ℤ → BufferAction
  DeleteLeft : ℕ → BufferAction
  DeleteRight : ℕ → BufferAction

data BufferState : Set where
  BufferS :
    {len : ℕ} →
    Fin (suc len) →
    Vec Char len →
    ℕ →
    BufferState
