module TermBehaviour where

open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ)
open import Data.Char using (Char; toNat)
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)
open import Data.Bool
open import Relation.Nullary.Decidable

{-

Describes the outward behaviour of a terminal. Does not include
implementation details such as how you send control codes and
other metadata to the terminal.

-}

data Colour : Set where
  Black : Colour
  Red : Colour
  Green : Colour
  Yellow : Colour
  Blue : Colour
  Magenta : Colour
  Cyan : Colour
  White : Colour
  DefaultFG : Colour

Grid : (a : Set) → ℕ → ℕ → Set
Grid a w h = Vec (Vec a w) h

ScreenChar : Set
ScreenChar = Char × Colour

-- annotated with whether cursor is present on this square
TermChar : Set
TermChar = ScreenChar × Bool

data Visual : (w : ℕ) → (h : ℕ) → Set where
  VisualS :
    (w : ℕ) →
    (h : ℕ) →
    Grid TermChar w h →
    Visual w h

isPrintableChar : Char → Bool
isPrintableChar ch = ⌊ 32 Data.Nat.≤? toNat ch ⌋ ∧ ⌊ toNat ch Data.Nat.≤? 127 ⌋
