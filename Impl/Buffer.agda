module Impl.Buffer where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc)
open import Data.Vec using (Vec)
open import Data.Char using (Char)

open import ListUtil

data BufferImpl : Set where
  BufferI : (n : ℕ) → Fin (suc n) → Vec Char n → BufferImpl

bufferIns : Char → BufferImpl → BufferImpl
bufferIns ch (BufferI n i cs)
  = BufferI (suc n) (suc i) (ins+ i ch cs)
