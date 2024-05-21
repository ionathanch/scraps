open import Data.Bool
open import Data.Nat
open import Data.List hiding (filter)

filter : ∀ {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with (p x)
... | true = x ∷ filter p xs
... | false = filter p xs

{-
  An accessibility predicate on lists (of naturals)
  based on the recursive calls of quicksort.
-}
data Accqs : List ℕ → Set where
  accnil : Accqs []
  acccons : ∀ (x : ℕ) (xs : List ℕ) →
    Accqs (filter (_<ᵇ x) xs) →
    Accqs (filter (x ≤ᵇ_) xs) →
    Accqs (x ∷ xs)

{- Wellfoundedness: All lists are accessible according to Accqs. -}
accqs : ∀ (xs : List ℕ) → Accqs xs
accqs [] = accnil
accqs (x ∷ xs) with (accqs xs)
... | accnil = acccons x [] accnil accnil
... | acccons y ys acc<ᵇ acc≤ᵇ = acccons x (y ∷ ys) {!   !} {!   !}

{- Quicksort by structural induction on Accqs. -}
quicksort : (xs : List ℕ) → Accqs xs → List ℕ
quicksort [] accnil = []
quicksort .(x ∷ xs) (acccons x xs acc<ᵇ acc≤ᵇ) =
  (quicksort (filter (_<ᵇ x) xs) acc<ᵇ) ++
  (quicksort (filter (x ≤ᵇ_) xs) acc≤ᵇ)

quicksorted : List ℕ → List ℕ
quicksorted xs = quicksort xs (accqs xs)
