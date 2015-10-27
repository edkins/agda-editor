module BufferBehaviour where

open import Data.Char using (Char)
open import Data.Fin using (Fin; suc; toℕ; zero)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.List using (List)
open import Data.Vec using (Vec; toList; [])

open import ListUtil

-- A list of characters and a cursor position
-- (which may be one square beyond the end of the file)
data Buffer : Set where
  BufferS :
    {len : ℕ} →
    Fin (suc len) →
    Vec Char len →
    Buffer

-- Annotated with width and height
Window = Buffer × ℕ × ℕ

bufferFile : Buffer → List Char
bufferFile (BufferS _ v) = toList v

bufferCursor : Buffer → ℕ
bufferCursor (BufferS i _) = toℕ i

bufferInsertAtCursor : Char → Buffer → Buffer
bufferInsertAtCursor ch (BufferS i v) =
  BufferS (suc i) (ins+ i ch v)

initialBuffer = BufferS zero []

initialWindow : ℕ → ℕ → Window
initialWindow w h = (initialBuffer , w , h)
