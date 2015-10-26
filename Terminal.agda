module Terminal where

open import Data.String
open import Data.Fin
open import Data.Vec
open import Data.Nat
open import Data.Char
open import Data.Maybe
open import Data.Product
open import Data.Bool
open import Relation.Nullary.Decidable
open import Function
open import Data.List

open import TermBehaviour
open import ListUtil
open import FinUtil

data TerminalState : Set where
  StateDefault : TerminalState
  StateEscape : String -> TerminalState

data TerminalScreen : Set where
  Screen :
    (w : ℕ) →
    (h : ℕ) →
    (cx : Fin w) →
    (cy : Fin h) →
    Colour →
    Grid ScreenChar w h →
    TerminalScreen

Terminal = Maybe (TerminalState × TerminalScreen)

gridWith : {a : Set} → {w : ℕ} → {h : ℕ} → Fin w → Fin h → a → Grid a w h → Grid a w h
gridWith x y e grid = upd y (upd x (const e)) grid

screenPrint : Char → TerminalScreen → Maybe TerminalScreen
screenPrint ch (Screen w h cx cy colour grid) =
  let grid' = gridWith cx cy (ch , colour) grid in
  case next cx of λ
  { nothing →
      case next cy of λ
      { nothing → nothing
      ; (just cy') → just (Screen w h (tozero cx) cy' colour grid')
      }
  ; (just cx') →
      just (Screen w h cx' cy colour grid')
  }

screenNextLine : TerminalScreen → Maybe TerminalScreen
screenNextLine (Screen w h cx cy colour grid) =
  case next cy of λ
  { nothing → nothing
  ; (just cy') → just (Screen w h (tozero cx) cy' colour grid)
  }

screenSetColour : Colour → TerminalScreen → TerminalScreen
screenSetColour colour (Screen w h cx cy _ grid) =
  Screen w h cx cy colour grid

screenNop : TerminalScreen → Maybe TerminalScreen
screenNop screen = just screen

screenError : TerminalScreen → Maybe TerminalScreen
screenError screen = nothing

-- Insert a character but don't advance the cursor.
screenInsertChar : Char → TerminalScreen → TerminalScreen
screenInsertChar ch (Screen w h cx cy colour grid) =
  let grid' = upd cy (ins cx (ch , colour)) grid in
  Screen w h cx cy colour grid'

screenDoEscape : String → TerminalScreen → Maybe TerminalScreen
screenDoEscape str screen =
  case str of λ {
    "[@" → just (screenInsertChar ' ' screen)
  ; _ → nothing
  }

endsEscape : Char → Bool
endsEscape ch = ⌊ 64 Data.Nat.≤? toNat ch ⌋ ∧ ⌊ toNat ch Data.Nat.≤? 127 ⌋

isNewLine : Char → Bool
isNewLine ch = ⌊ 10 Data.Nat.≟ toNat ch ⌋

isEsc : Char → Bool
isEsc ch = ⌊ 27 Data.Nat.≟ toNat ch ⌋

termCharAction : Char → TerminalState →
  ((TerminalScreen → Maybe TerminalScreen) × TerminalState)
termCharAction ch state =
  case state of λ {
    StateDefault →
      if isPrintableChar ch then
        (screenPrint ch , StateDefault)
      else if isNewLine ch then
        (screenNextLine , StateDefault)
      else if isEsc ch then
        (screenNop , StateEscape "")
      else
        (screenError , StateDefault)
        
  ; (StateEscape str) →
      let str' = str Data.String.++ (Data.String.fromList (Data.List.[ ch ])) in
      if endsEscape ch then
        (screenDoEscape str' , StateDefault)
      else
        (screenNop , StateEscape str')
  }

termChar : Char → Terminal → Terminal
termChar ch nothing = nothing
termChar ch (just (state , screen)) =
  let (f , state') = termCharAction ch state in
    case f screen of λ {
      (just screen') → just (state' , screen')
    ; nothing → nothing
    }
