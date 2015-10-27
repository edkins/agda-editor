module Impl.Window where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Char using (Char)
open import Data.Product using (_×_, _,_)

open import Impl.Buffer
open import KeyboardBehaviour

data WindowImpl : Set where
  WindowI : BufferImpl → ℕ → ℕ → WindowImpl

windowImplInit : (WindowImpl × List Char)
windowImplInit = (bufferImplInit , "\e[2J")

windowImplKey : Key → WindowImpl → (WindowImpl × List Char)
windowImplKey k (buf , w , h) =
  case getKeyChar k
  case ch of λ{
    nothing → (buf , w , h)
    just ch → (
