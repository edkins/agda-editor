module MyIO where

open import IO
import MyPrimitive
open import Data.Bool
open import Data.Unit
open import Coinduction

primBool : Bool → MyPrimitive.Bool
primBool false = MyPrimitive.False
primBool true = MyPrimitive.True

primBuffering : Bool → MyPrimitive.BufferMode
primBuffering false = MyPrimitive.NoBuffering
primBuffering true = MyPrimitive.LineBuffering

hSetEcho : Bool → IO ⊤
hSetEcho b =
  ♯ lift (MyPrimitive.hSetEcho MyPrimitive.stdout (primBool b)) >>
  ♯ return _

hSetBufferingOut : Bool → IO ⊤
hSetBufferingOut b =
  ♯ lift (MyPrimitive.hSetBuffering MyPrimitive.stdout (primBuffering b)) >>
  ♯ return _
  
hSetBufferingIn : Bool → IO ⊤
hSetBufferingIn b =
  ♯ lift (MyPrimitive.hSetBuffering MyPrimitive.stdin (primBuffering b)) >>
  ♯ return _
  
