module Behaviour where

open import Data.List using (List; []; _∷_)
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ)

open import OutputBehaviour
open import InputBehaviour

data Environment : Set where
  Env : ℕ → ℕ → Environment

okOutputSignals : FullState → OutputSignals → Set
okOutputSignals state expected = windowOutputs (getCurrentWindow state) ≡ expected

okBehaviour' : FullState → List InputEvent → OutputSignals → Set
okBehaviour' state [] expected = okOutputSignals state expected
okBehaviour' state (e ∷ es) expected = okBehaviour' (handleInput e state) es expected

okBehaviour : Environment → List InputEvent → OutputSignals → Set
okBehaviour (Env w h) es expected =
  okBehaviour' (initialState w h) es expected


