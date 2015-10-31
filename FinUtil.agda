module FinUtil where

open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; suc; _≤_; pred; _+_; s≤s; z≤n; _<_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Fin using (Fin; zero; suc; toℕ; inject₁)
open import Data.Fin.Properties
open import Data.Integer using (ℤ; -[1+_]; +_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Bool using (Bool; true; false)
open Data.Nat.≤-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning renaming (begin_ to begin=_; _≡⟨_⟩_ to _=⟨_⟩_; _∎ to _end=)
open import Relation.Nullary using (Dec; yes; no)
open import Function

sucinj : {m : ℕ} → {n : ℕ} → suc m ≡ suc n → m ≡ n
sucinj p0 = cong pred p0

elimFin0 : {a : Set} → Fin 0 → a
elimFin0 ()

elim0=s : {a : Set} → {n : ℕ} → 0 ≡ suc n → a
elim0=s ()

elimF0=s : {a : Set} → {n : ℕ} → {x : Fin n} → zero ≡ suc x → a
elimF0=s ()

finsubst : {m : ℕ} → {n : ℕ} → m ≡ n → Fin m → Fin n
finsubst {suc m} {suc n} p0 zero = zero
finsubst {suc m} {suc n} p0 (suc k) = suc (finsubst (sucinj p0) k)
finsubst {0} _ n = elimFin0 n
finsubst {suc m} {0} p0 _ = elim0=s (sym p0)

finsubst-suc : {m : ℕ} → {n : ℕ} → (p : m ≡ n) → (a : Fin m) →
  finsubst (cong suc p) (suc a) ≡ suc (finsubst p a)
finsubst-suc p a = refl

finsubst-toℕ : {m : ℕ} → {n : ℕ} → (p : m ≡ n) → (a : Fin m) → toℕ (finsubst p a) ≡ toℕ a
finsubst-toℕ {suc m} {suc n} p zero = refl
finsubst-toℕ {suc m} {suc n} p (suc b) =
  cong Data.Nat.suc (finsubst-toℕ (sucinj p) b)
finsubst-toℕ {0} {_} _ a = elimFin0 a
finsubst-toℕ {suc m} {0} p _ = elim0=s (sym p)

finsubst-subst : {m : ℕ} → {n : ℕ} → (p : m ≡ n) → (q : n ≡ m) → (a : Fin m) →
  finsubst q (finsubst p a) ≡ a
finsubst-subst p q a = toℕ-injective (trans (finsubst-toℕ q (finsubst p a)) (finsubst-toℕ p a))

finsubst-trans : {m : ℕ} → {n : ℕ} → {o : ℕ} → (p : m ≡ n) → (q : n ≡ o) → (a : Fin m) →
  finsubst q (finsubst p a) ≡ finsubst (trans p q) a
finsubst-trans p q a = toℕ-injective (begin=
  toℕ (finsubst q (finsubst p a))
    =⟨ finsubst-toℕ q (finsubst p a) ⟩
  toℕ (finsubst p a)
    =⟨ finsubst-toℕ p a ⟩
  toℕ a
    =⟨ sym (finsubst-toℕ (trans p q) a) ⟩
  toℕ (finsubst (trans p q) a)
    end=)

+≤ : {x : ℕ} → {y : ℕ} → (z : ℕ) →
  x ≤ y → z + x ≤ z + y
+≤ 0 p = p
+≤ (suc z) p = s≤s (+≤ z p)

≤+ : {x : ℕ} → {y : ℕ} → (z : ℕ) →
  x ≤ y → x + z ≤ y + z
≤+ {x} {y} z p = begin
  x + z ≡⟨ +-comm x z ⟩
  z + x ≤⟨ +≤ z p ⟩
  z + y ≡⟨ +-comm z y ⟩
  y + z ∎

≤+≤ : {x : ℕ} → {y : ℕ} → {x' : ℕ} → {y' : ℕ} →
  x ≤ x' → y ≤ y' → x + y ≤ x' + y'
≤+≤ {x} {y} {x'} {y'} p0 p1 = begin
  x + y ≤⟨ +≤ x p1 ⟩
  x + y' ≤⟨ ≤+ y' p0 ⟩
  x' + y' ∎

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

≤-refl : {n : ℕ} → n ≤ n
≤-refl {0} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

z<s : {n : ℕ} → 0 < suc n
z<s {n} = s≤s z≤n

s<s : {m : ℕ} → {n : ℕ} → m < n → suc m < suc n
s<s = s≤s

toℕ-suc : {n : ℕ} → (a : Fin n) → suc (toℕ a) ≡ toℕ (suc a)
toℕ-suc a = refl

fsucinj : {n : ℕ} → {a : Fin n} → {b : Fin n}
  → suc a ≡ suc b → a ≡ b
fsucinj {n} {a} {b} p0 = toℕ-injective (sucinj (cong toℕ p0))

--toℕ< : {n : ℕ} → {a : Fin n} → toℕ a < n
--toℕ< {n} {a} = prop-toℕ-≤ {suc n} (suc a)

clampNatToFin : {n : ℕ} → ℕ → Fin (suc n)
clampNatToFin {n} 0 = zero
clampNatToFin {0} (suc _) = zero
clampNatToFin {suc n} (suc x) = suc (clampNatToFin x)

clampIntToFin : {n : ℕ} → ℤ → Fin (suc n)
clampIntToFin (-[1+ _ ]) = zero
clampIntToFin (+ x) = clampNatToFin x

finIsZero : {n : ℕ} → Fin n → Bool
finIsZero zero = true
finIsZero (suc n) = false

finIsMax : {n : ℕ} → Fin n → Bool
finIsMax {suc 0} zero = true
finIsMax {suc 0} {suc x} = elimFin0 x
finIsMax {suc (suc n)} zero = false
finIsMax {suc (suc n)} {suc x} = finIsMax {suc n} x

_F≟_ : {n : ℕ} → (x : Fin n) → (y : Fin n) → Dec (x ≡ y)
_F≟_ zero zero = yes refl
_F≟_ zero (suc n) = no (λ eq → elimF0=s eq)
_F≟_ (suc m) zero = no (λ eq → elimF0=s (sym eq))
_F≟_ (suc m) (suc n) = case m ≟ n of λ{
  (yes p) → yes (cong suc p)
  ; (no p) → no (λ sm=sn → (p (fsucinj sm=sn)))
  }

fmax : {n : ℕ} → Fin (suc n)
fmax {0} = zero
fmax {suc n} = suc (fmax {n})

inj≠fmax : {n : ℕ} → (x : Fin n) → inject₁ x ≢ fmax
inj≠fmax zero = λ p → elimF0=s p
inj≠fmax (suc x) = λ p → inj≠fmax x (fsucinj p)
