module OutputBehaviour where

open import Data.List using (List; map; _∷_; [])
open import Data.Char using (Char)
open import Data.Nat using (ℕ; _+_; _≟_)
open import Data.Nat.DivMod
open import Data.Product using (_×_; _,_; proj₁; Σ)
open import Data.Bool using (Bool; if_then_else_; false; true)
open import Data.Fin using (Fin; toℕ)
open import Relation.Nullary.Decidable using (⌊_⌋; False)
open import Data.Vec using (replicate)
open import Function

open import ListUtil
open import Lists
open import TermBehaviour
open import BufferBehaviour

-- Annotated with width and height
Window = Buffer × ℕ × ℕ

withXY' : {a : Set} →
  ℕ → ℕ → (a → Bool) → List a → List (a × ℕ × ℕ)
withXY' x y f [] = []
withXY' x y f (c ∷ cs) =
  (c , x , y) ∷ (if f c then
      withXY' 0 (y + 1) f cs
  else
      withXY' (x + 1) y f cs)

withXY : {a : Set} → (a → Bool) → List a → List (a × ℕ × ℕ)
withXY = withXY' 0 0

----------------------

CharIndex = Char × ℕ

CharCursor = Char × ℕ × Bool

cursorize : Buffer → CharIndex → CharCursor
cursorize buf (ch , index) =
  let cursor = bufferCursor buf in
  ch , index , ⌊ index ≟ cursor ⌋

CharColour = Char × ℕ × Colour × Bool

colourize : CharCursor → CharColour
colourize (ch , index , cur) =
  case ch of λ{
    '\n' → (' ' , index , DefaultFG , cur)
  ; _ →
      if isPrintableChar ch then
        (ch , index , DefaultFG , cur)
      else
        ('?' , index , Blue , cur)
  }

isLineBreak1 : CharColour → Bool
isLineBreak1 (ch , _ , _ , _) =
  ⌊ ch Data.Char.≟ '\n' ⌋

CharXY = CharColour × ℕ × ℕ

isLineBreak2 : (w : ℕ) → {w≠0 : False (w ≟ 0)} → CharXY → Bool
isLineBreak2 w {w≠0} (_ , row , col) =
  ⌊ toℕ (_mod_ col w {w≠0}) Data.Nat.≟ 0 ⌋

dropXY : CharXY → TermChar
dropXY ((ch , _ , colour , cur) , _ , _) = (ch , colour) , cur

bufferVisual : (w : ℕ) → {w≠0 : False (w ≟ 0)} → (h : ℕ) →
  Buffer → Visual w h
bufferVisual w {w≠0} h buf =
  let
    chars = bufferFile buf
    charsIndices = withIndices chars
    charsCursor = map (cursorize buf) charsIndices
    charsColours = map colourize charsCursor
    charsXY = withXY isLineBreak1 charsColours

    emptyChar : TermChar
    emptyChar = (' ' , DefaultFG) , false
    emptyRow = replicate {n = w} emptyChar

    lines = listSplit (isLineBreak2 w {w≠0}) charsXY
    lines' = maps dropXY lines
    rows = map (vecTake w emptyChar) lines'
    grid = vecTake h emptyRow rows
  in
    VisualS w h grid
