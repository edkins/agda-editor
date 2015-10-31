module Interfaces where

open import Data.Char using (Char)
open import Data.List using (List)

data SpecialKey : Set where
  KeyLeft : SpecialKey
  KeyRight : SpecialKey
  KeyUp : SpecialKey
  KeyDown : SpecialKey
  KeyBackspace : SpecialKey
  KeyDelete : SpecialKey

data InputEvent : Set where
  KeyChar : Char → InputEvent
  KeySpecial : SpecialKey → InputEvent

data BufferAction : Set where
  InsertChars : List Char → BufferAction
