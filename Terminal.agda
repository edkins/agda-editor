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

data TerminalState : Set where
  StateDefault : TerminalState
  StateEscape : String -> TerminalState

Grid : (a : Set) → ℕ → ℕ → Set
Grid a w h = Vec (Vec a w) h

data TerminalScreen : Set where
  Screen :
    (w : ℕ) →
    (h : ℕ) →
    Fin w →
    Fin h →
    Grid Char w h →
    TerminalScreen

Terminal = Maybe (TerminalState × TerminalScreen)

upd : {a : Set} → {n : ℕ} → Fin n → (a → a) → Vec a n → Vec a n
upd zero f (x ∷ xs) = f x ∷ xs
upd (suc n) f (x ∷ xs) = x ∷ upd n f xs

gridWith : {a : Set} → {w : ℕ} → {h : ℕ} → Fin w → Fin h → a → Grid a w h → Grid a w h
gridWith x y e grid = upd y (upd x (const e)) grid

forceType : (a : Set) → a → a
forceType t x = x

next : {n : ℕ} → Fin n → Maybe (Fin n)
next {0} impossible = nothing
next {1} x = nothing
next {suc (suc n)} zero = just (suc zero)
next {suc (suc n)} (suc x) = case next x of λ
  { nothing → nothing
  ; (just y) → just (suc y)
  }

tozero : {n : ℕ} → Fin n → Fin n
tozero {0} impossible = impossible
tozero {suc n} x = zero

screenPrint : Char → TerminalScreen → Maybe TerminalScreen
screenPrint ch (Screen w h cx cy grid) =
  let grid' = gridWith cx cy ch grid in
  case next cx of λ
  { nothing →
      case next cy of λ
      { nothing → nothing
      ; (just cy') → just (Screen w h (tozero cx) cy' grid')
      }
  ; (just cx') →
      just (Screen w h cx' cy grid')
  }
