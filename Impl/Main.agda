module Impl.Main where

open import Data.Unit
open import IO
import IO.Primitive
open import Coinduction
open import Data.Colist
open import Data.Char using (Char)

open import Behaviour

double : Colist Char → Colist Char
double [] = []
double (c ∷ cs) = c ∷ ♯('\n' ∷ ♯ (double (♭ cs)))

mainIO : IO ⊤
mainIO =
  ♯ getContents >>= λ str →
  ♯ putStr∞ (double str)

main : IO.Primitive.IO ⊤
main = run mainIO
