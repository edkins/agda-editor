module Behaviour where

open import Data.Unit
open import Data.List
open import Data.Char
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Relation.Nullary.Decidable

open import Util


Buffer = (ℕ × ℕ × ℕ × List Char)

EditorChar = (Char × Bool)

isLineBreak : EditorChar → Bool
isLineBreak (ch , _) = ⌊ ch Data.Char.≟ '\n' ⌋

listLines : List EditorChar → List (List EditorChar)
listLines es = listSplit isLineBreak es

annotate : List Char → ℕ → List EditorChar
annotate [] n = []
annotate (c ∷ cs) 0 = (c , true) ∷
  Data.List.map ( λ c' → c' , false ) cs
annotate (c ∷ cs) (suc n) = (c , false) ∷ annotate cs n

buffer_annotate : Buffer → List EditorChar
buffer_annotate (w , h , pos , str) = annotate str pos
