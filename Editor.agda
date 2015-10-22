module Editor where

open import IO
open import Data.Unit

mainIO : IO ⊤
mainIO = putStrLn "Hello"

main = run mainIO
