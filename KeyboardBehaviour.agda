module KeyboardBehaviour where

open import Data.Char using (Char)
open import Data.Maybe using (Maybe; just; nothing)

Key = Maybe Char

getKeyChar : Key → Maybe Char
getKeyChar k = k

keyChar : Char → Key
keyChar ch = just ch

keyUnknown : Key
keyUnknown = nothing
