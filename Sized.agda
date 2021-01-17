open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Function.Base
open import Data.Product

data SList (A : Set) : (k : ℕ) → Set where
  SNil : (k : ℕ) → SList A k
  SCons : (k : ℕ) → A → SList A k → SList A (suc k)

leq : ℕ → ℕ → Bool
leq zero _ = true
leq _ zero = false
leq (suc k) (suc l) = leq k l

shift : ∀ {A k} → SList A k → SList A (suc k)
shift (SNil k) = SNil (suc k)
shift (SCons k hd tl) = SCons (suc k) hd (shift tl)

shiftBy : ∀ {A} → (k offset : ℕ) → SList A k → SList A (k + offset)
shiftBy _ offset (SNil k) = SNil (k + offset)
shiftBy _ offset (SCons k hd tl) = SCons (k + offset) hd (shiftBy k offset tl)

filter : ∀ {A} → (k : ℕ) → (A → Bool) → SList A k → SList A k
filter zero _ ls = ls
filter (suc k) _ (SNil _) = SNil _
filter (suc k) pred (SCons k hd tl) =
  if (pred hd)
  then SCons k hd (filter k pred tl)
  else shift (filter k pred tl)

append : ∀ {A} → (k l : ℕ) → SList A k → SList A l → SList A (k + l)
append zero _ _ ls = ls
append k l (SNil _) ls rewrite (+-comm k l) = shiftBy l k ls
append (suc k) l (SCons k hd tl) ls = SCons (k + l) hd (append k l tl ls)

qsort : (k : ℕ) → SList ℕ k → ∃[ k ] (SList ℕ k)
qsort zero ls = zero , shiftBy zero _ ls
qsort k (SNil _) = k , SNil _
qsort (suc k) (SCons k hd tl) =
  let k1 , q1 = qsort k (filter k (leq hd) tl)
      k2 , q2 = qsort k (filter k (not ∘ leq hd) tl)
  in  suc (k1 + k2) , SCons (k1 + k2) hd (append k1 k2 q1 q2)
