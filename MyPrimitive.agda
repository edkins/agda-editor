module MyPrimitive where

open import IO.Primitive
open import Foreign.Haskell

{-# IMPORT System.IO #-}

postulate
  Handle : Set
  Int : Set

{-# COMPILED_TYPE Handle        System.IO.Handle        #-}
{-# COMPILED_TYPE Int           Int           #-}

data Bool : Set where
  True : Bool
  False : Bool

data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just : a → Maybe a

data BufferMode : Set where
  NoBuffering : BufferMode
  LineBuffering : BufferMode
  BlockBuffering : Maybe Int → BufferMode

{-# COMPILED_DATA Bool          Bool                  True False #-}
{-# COMPILED_DATA Maybe         Maybe                 Nothing Just #-}
{-# COMPILED_DATA BufferMode    System.IO.BufferMode  System.IO.NoBuffering System.IO.LineBuffering System.IO.BlockBuffering  #-}

postulate
  hSetBuffering : Handle → BufferMode → IO Unit
  hSetEcho : Handle → Bool → IO Unit
  stdout : Handle
  stdin : Handle

{-# COMPILED hSetBuffering System.IO.hSetBuffering #-}
{-# COMPILED hSetEcho      System.IO.hSetEcho      #-}
{-# COMPILED stdout        System.IO.stdout        #-}
{-# COMPILED stdin         System.IO.stdin         #-}
