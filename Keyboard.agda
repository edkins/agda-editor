module Keyboard where

open import KeyboardBehaviour
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Char using (Char; toNat)
open import Data.Nat using (ℕ; _≤?_; _≟_)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function

data KeyboardState : Set where
  KeyboardDefault : KeyboardState
  KeyboardEscape : List Char → KeyboardState

isEscape : Char → Bool
isEscape ch = ⌊ toNat ch ≟ 27 ⌋

endsEscape : Char → Bool
endsEscape ch = ⌊ 64 ≤? toNat ch ⌋ ∧ ⌊ toNat ch ≤? 127 ⌋

keyEscape : List Char → Key
keyEscape str = keyUnknown

handleInputChar : Char → KeyboardState → (KeyboardState × Maybe Key)
handleInputChar ch KeyboardDefault =
  if isEscape ch then
    (KeyboardEscape [] , nothing)
  else
    (KeyboardDefault , just (keyChar ch))
handleInputChar ch (KeyboardEscape str) =
  let str' = str ++ ch ∷ [] in
  if endsEscape ch then
    (KeyboardDefault , just (keyEscape str'))
  else
    (KeyboardEscape str' , nothing)
