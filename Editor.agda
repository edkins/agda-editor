module Editor where

open import IO
open import Data.Unit
open import Data.List
open import Data.Char
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Relation.Nullary.Decidable

open import Util
open import Terminal

scrubCursor : List (List EditorChar) → List (List Char)
scrubCursor = Data.List.map (Data.List.map fst)

mainIO : IO ⊤
mainIO = putStrLn "Hello"

main = run mainIO
