module InputComponent where

open import Component
open import InputInterface
open import BufferInterface
open import Data.List using ([]; _∷_; [_])
open import Data.Integer using (+_; -_)

inputFunction : InputEvent → BufferAction
inputFunction (KeyChar ch) = InsertChars [ ch ]
inputFunction (KeySpecial KeyLeft) = MoveChars (- + 1)
inputFunction (KeySpecial KeyRight) = MoveChars (+ 1)
inputFunction (KeySpecial KeyUp) = MoveLines (- + 1)
inputFunction (KeySpecial KeyDown) = MoveLines (+ 1)
inputFunction (KeySpecial KeyBackspace) = DeleteLeft 1
inputFunction (KeySpecial KeyDelete) = DeleteRight 1

inputComponent : Component InputEvent BufferAction
inputComponent = stateless inputFunction
