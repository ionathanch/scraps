open import Data.Empty using (⊥; ⊥-elim)

infix 30 ↑_
infix 30 ⊔_

{-# NO_UNIVERSE_CHECK #-}
data Ord : Set where
  ↑_ : Ord → Ord
  ⊔_ : {A : Set} → (A → Ord) → Ord

data _≤_ : Ord → Ord → Set where
  ↑s≤↑s : ∀ {r s} → r ≤ s → ↑ r ≤ ↑ s
  s≤⊔f  : ∀ {A} {s} f (a : A) → s ≤ f a → s ≤ ⊔ f
  ⊔f≤s  : ∀ {A} {s} f → (∀ (a : A) → f a ≤ s) → ⊔ f ≤ s

-- Reflexivity of ≤
s≤s : ∀ {s : Ord} → s ≤ s
s≤s {s = ↑ s} = ↑s≤↑s s≤s
s≤s {s = ⊔ f} = ⊔f≤s f (λ a → s≤⊔f f a s≤s)

-- Transitivity of ≤
s≤s≤s : ∀ {r s t : Ord} → r ≤ s → s ≤ t → r ≤ t
s≤s≤s (↑s≤↑s r≤s)     (↑s≤↑s s≤t)     = ↑s≤↑s (s≤s≤s r≤s s≤t)
s≤s≤s r≤s             (s≤⊔f f a s≤fa) = s≤⊔f f a (s≤s≤s r≤s s≤fa)
s≤s≤s (⊔f≤s f fa≤s)   s≤t             = ⊔f≤s f (λ a → s≤s≤s (fa≤s a) s≤t)
s≤s≤s (s≤⊔f f a s≤fa) (⊔f≤s f fa≤t)   = s≤s≤s s≤fa (fa≤t a)

-- Strict order
_<_ : Ord → Ord → Set
r < s = ↑ r ≤ s

-- The "infinite" ordinal
∞ : Ord
∞ = ⊔ (λ s → s)

-- ∞ is strictly larger than itself
∞<∞ : ∞ < ∞
∞<∞ = s≤⊔f (λ s → s) (↑ ∞) s≤s

{- Well-founded induction for Ords via an
   accessibility predicate based on strict order -}

record Acc (s : Ord) : Set where
  inductive
  pattern
  constructor acc
  field
    acc< : (∀ r → r < s → Acc r)

open Acc

-- All ordinals are accessible...
accessible : ∀ (s : Ord) → Acc s
accessible (↑ s) = acc (λ { r (↑s≤↑s r≤s) → acc (λ t t<r → (accessible s).acc< t (s≤s≤s t<r r≤s)) })
accessible (⊔ f) = acc (λ { r (s≤⊔f f a r<fa) → (accessible (f a)).acc< r r<fa })

-- ...except the infinity size
¬accessible∞ : Acc ∞ → ⊥
¬accessible∞ (acc p) = ¬accessible∞ (p ∞ ∞<∞)

ng : ⊥
ng = ¬accessible∞ (accessible ∞)