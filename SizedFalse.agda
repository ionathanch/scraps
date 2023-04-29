{-# OPTIONS --sized-types --without-K #-}

module SizedFalse where

open import Agda.Builtin.Size
open import Data.Empty

module < where
  data _<_ : Size → Size → Set where
    lt : ∀ s → (r : Size< s) → r < s
  
  data Acc (s : Size) : Set where
    acc : (∀ {r} → r < s → Acc r) → Acc s

  wf : ∀ s → Acc s
  wf s = acc (λ {(lt .s r) → wf r})

  ¬wf∞ : Acc ∞ → ⊥
  ¬wf∞ (acc p) = ¬wf∞ (p (lt ∞ ∞))

  false : ⊥
  false = ¬wf∞ (wf ∞)

module ≡ where
  data _≡_ : Size → Size → Set where
    refl : ∀ {i} → i ≡ i
  
  data Up! : Size → Set where
    huh : ∀ {i} → Up! i
    up! : ∀ {i} → {j : Size< i} → Up! j → Up! i
  
  {-# NON_TERMINATING #-}
  hup! : ∀ i → i ≡ (↑ ∞) → Up! i → ⊥
  hup! .∞ refl u = hup! ∞ refl (up! u)
  
  false : ⊥
  false = hup! ∞ refl huh