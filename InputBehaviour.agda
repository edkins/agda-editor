module InputBehaviour where

open import Data.Char using (Char)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Function

open import BufferBehaviour
open import KeyboardBehaviour

data InputEvent : Set where
  InputKey : Key → InputEvent

data InputMode : Set where
  DefaultMode : InputMode

initialMode = DefaultMode

data InputCommand : Set where
  InsertChar : Char → InputCommand
  Nop : InputCommand

FullState : Set
FullState = (InputMode × Window)

getKeyCommand : Key → InputMode → (InputMode × InputCommand)
getKeyCommand k DefaultMode = case getKeyChar k of λ{
    (just ch) → (DefaultMode , InsertChar ch)
  ; nothing → (DefaultMode , Nop)
  }

windowCommand : InputCommand → Window → Window
windowCommand (InsertChar ch) (buf , w , h) = (bufferInsertAtCursor ch buf , w , h)
windowCommand Nop win = win

-------------

getCurrentWindow : FullState → Window
getCurrentWindow = proj₂

handleKey : Key → FullState → FullState
handleKey k (mode , window) =
  let
    (mode' , cmd) = getKeyCommand k mode
    window' = windowCommand cmd window
  in
    (mode' , window')

handleInput : InputEvent → FullState → FullState
handleInput (InputKey k) state = handleKey k state

initialState : ℕ → ℕ → FullState
initialState w h = (initialMode , initialWindow w h)
