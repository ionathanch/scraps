{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality
open import Data.Empty

-- base : Size
-- next : Delay → Size
-- later : Size → Delay
record Delay : Set
data Size : Set

record Delay where
  coinductive
  constructor later
  field now : Size
open Delay

data Size where
  base : Size
  next : Delay → Size

-- ω ≡ next ω' ≡ next (later (next ω')) ≡ ...
--   ≡ next (later ω) ≡ ...
ω : Size
ω = next ω' -- next (later (next ω))
  where
  ω' : Delay
  -- ω' = later (next ω')
  now ω' = next ω'

next' : Size → Size
next' s = next (later s)

{-# ETA Delay #-}
lim : ω ≡ next' ω
lim = refl

data FSize : Size → Set where
  fbase : FSize base
  fnext : {d : Delay} → FSize (now d) → FSize (next d)

inf : FSize ω → ⊥
inf (fnext s) = inf s

data Nat : Size → Set where
  zero : (s : Size) → Nat (next' s)
  succ : (s : Size) → Nat s → Nat (next' s)

shift : ∀ s → Nat s → Nat (next' s)
shift _ (zero s) = zero (next' s)
shift _ (succ s n) = succ (next' s) (shift s n)

postulate blocker : ∀ s → Nat s → Nat s

-- The guard condition passes due to recursion on n,
-- not due to recusion on the size, since it doesn't know that
-- `now s` is in fact smaller than s without using Agda's sized types
-- (or the old version of coinductive types with musical notation).
zeroify : ∀ s → Nat s → Nat s
zeroify base ()
zeroify (next s) (zero _) = zero _
zeroify (next s) (succ _ n) = shift (now s) (zeroify (now s) (blocker (now s) n))
