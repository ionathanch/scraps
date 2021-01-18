open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Function.Base
open import Data.Product

-- Sizes are ordinals up to ω, i.e. naturals

𝕊 : Set
𝕊 = ℕ

hat : 𝕊 → 𝕊
hat = suc

-- Sized naturals and lists indexed by a size

data SNat : (k : 𝕊) → Set where
  SZero : (k : 𝕊) → SNat k
  SSucc : (k : 𝕊) → SNat k → SNat (hat k)

data SList (A : Set) : (k : 𝕊) → Set where
  SNil : (k : 𝕊) → SList A k
  SCons : (k : 𝕊) → A → SList A k → SList A (hat k)

-- Helpers to shift the size of lists up as needed

shift : ∀ {A k} → SList A k → SList A (suc k)
shift (SNil k) = SNil (suc k)
shift (SCons k hd tl) = SCons (suc k) hd (shift tl)

shiftBy : ∀ {A} → (k offset : 𝕊) → SList A k → SList A (k + offset)
shiftBy _ offset (SNil k) = SNil (k + offset)
shiftBy _ offset (SCons k hd tl) = SCons (k + offset) hd (shiftBy k offset tl)

-- Minus and div functions, no unrolling needed
-- Minus is size-preserving in the first argument, with an arbitrary second argument size
-- Div is the same, also happening to be size-preesrving in the first argument

minus : (k l : 𝕊) → SNat k → SNat l → SNat k
minus _ _ (SZero k) _ = SZero k
minus _ _ k (SZero l) = k
minus _ _ (SSucc k n) (SSucc l m) = SSucc k (minus k l n m)

div : (k l : 𝕊) → SNat k → SNat l → SNat k
div _ _ (SZero k) _ = SZero k
div _ _ (SSucc k n) m = SSucc _ (div k _ (minus k _ n m) m)

-- Size-preserving filter

filter : ∀ {A} → (k : 𝕊) → (A → Bool) → SList A k → SList A k
filter zero _ ls = ls
filter (suc k) _ (SNil _) = SNil _
filter (suc k) pred (SCons k hd tl) =
  if (pred hd)
  then SCons k hd (filter k pred tl)
  else shift (filter k pred tl)

-- Two appends: First one explicitly returns a list whose size is the sum of the input list sizes,
-- while the second one returns a list with *some* size, which we don't know is the sum of the sizes

append : ∀ {A} → (k l : 𝕊) → SList A k → SList A l → SList A (k + l)
append zero _ _ ls = ls
append k l (SNil _) ls rewrite (+-comm k l) = shiftBy l k ls
append (suc k) l (SCons k hd tl) ls = SCons (k + l) hd (append k l tl ls)

append' : ∀ {A} → (k l : 𝕊) → SList A k → SList A l → ∃[ kl ] SList A kl
append' zero l _ ls = l , ls
append' k l (SNil _) ls = l , ls
append' (suc k) l (SCons k hd tl) ls =
  let kl , kls = append' k l tl ls
  in  suc kl , SCons kl hd kls

-- Qsort returning a list of some size
-- The most specific size we could give it would probably be exponential
qsort : (k : 𝕊) → SList ℕ k → ∃[ k ] (SList ℕ k)
qsort zero ls = zero , shiftBy zero _ ls
qsort k (SNil _) = k , SNil _
qsort (suc k) (SCons k hd tl) =
  let k1 , q1 = qsort k (filter k (_<ᵇ hd) tl)
      k2 , q2 = qsort k (filter k (not ∘ _<ᵇ_ hd) tl)
  in  suc (k1 + k2) , SCons (k1 + k2) hd (append k1 k2 q1 q2)

-- Longer example: base 2 logarithm

data LogDom : (s : 𝕊) → (p : ℕ) → Set where
  LogDom1 : (s : 𝕊) → LogDom s (suc zero)
  LogDom2 : (s : 𝕊) → (p : ℕ) → LogDom s (suc ⌊ p /2⌋) → LogDom (hat s) (suc (suc p))

postulate logdomInv : (s : 𝕊) → (p : ℕ) → LogDom (hat s) (suc (suc p)) → LogDom s (suc ⌊ p /2⌋)
