module Component where

open import Data.Product using (_×_; _,_)
open import Coinduction

{-

A component accepts an input token and produces an output token together with a new version of the component.

It has internal state but this state isn't exposed.

-}

data Component : (a : Set) → (b : Set) → Set₁ where
  Comp : {a : Set} → {b : Set} → ∞(a → (b × Component a b)) → Component a b

step : {a : Set} → {b : Set} → Component a b → a → (b × Component a b)
step (Comp f) = ♭ f

chain : {a : Set} → {b : Set} → {c : Set} →
  Component a b → Component b c → Component a c
chain (Comp f) (Comp g) =
  Comp (♯(λ x →
    let (y , cf) = (♭ f x) in
    let (z , cg) = (♭ g y) in
    (z , chain cf cg)))

makeComponent : {s : Set} → {a : Set} → {b : Set} →
  (a → s → (b × s)) → s → Component a b
makeComponent f s =
  Comp (♯(λ x →
    let (y , s') = f x s in
    (y , makeComponent f s')))

stateBroadcast : {s : Set} → {a : Set} → (a → s → s) → s → Component a s
stateBroadcast f s =
  Comp (♯(λ x →
    let s' = f x s in
    (s' , stateBroadcast f s')))

stateless : {a : Set} → {b : Set} → (a → b) → Component a b
stateless f = Comp (♯(λ x → (f x , stateless f)))
