module InputBehaviour where

open import Data.Char using (Char)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; nothing; just)
open import Function

open import BufferBehaviour
open import KeyboardBehaviour

data InputMode : Set where
  DefaultMode : InputMode

data InputCommand : Set where
  InsertChar : Char → InputCommand
  Nop : InputCommand

InputState : Set
InputState = (InputMode × Buffer)

getKeyCommand : Key → InputMode → (InputMode × InputCommand)
getKeyCommand k DefaultMode = case getKeyChar k of λ{
    (just ch) → (DefaultMode , InsertChar ch)
  ; nothing → (DefaultMode , Nop)
  }

bufferCommand : InputCommand → Buffer → Buffer
bufferCommand (InsertChar ch) buf = bufferInsertAtCursor ch buf
bufferCommand Nop buf = buf

-------------

getCurrentBuffer : InputState → Buffer
getCurrentBuffer = proj₂

handleKey : Key → InputState → InputState
handleKey k (mode , buffer) =
  let
    (mode' , cmd) = getKeyCommand k mode
    buffer' = bufferCommand cmd buffer
  in
    (mode' , buffer')
