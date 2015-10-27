module Impl.Main where

open import Data.Unit
open import IO
import IO.Primitive
open import Coinduction
open import Data.Colist
open import Data.Char using (Char)
open import Data.Bool using (Bool; false; true)

open import MyIO
open import Behaviour
open import Impl.Editor

double : Colist Char → Colist Char
double [] = []
double (c ∷ cs) = c ∷ ♯('\n' ∷ ♯ (double (♭ cs)))

mainIO : IO ⊤
mainIO =
  ♯(♯(♯(♯ hSetBufferingOut false >>
  ♯ hSetBufferingIn false) >>
  ♯ hSetEcho false) >>
  ♯ getContents) >>= λ str →
  ♯ putStr∞ (double str)

main : IO.Primitive.IO ⊤
main = run mainIO
