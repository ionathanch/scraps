{-# OPTIONS --type-in-type #-}

open import Data.Product

data ⊥ : Set where

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set where
  refl : a ≡ a

subst : ∀ {ℓ ℓ′} {A : Set ℓ} {a b : A} → (P : A → Set ℓ′) → (p : a ≡ b) → P a → P b
subst _ refl pa = pa

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

℘ : ∀ {ℓ} → Set ℓ → Set _
℘ {ℓ} S = S → Set

{-# NO_POSITIVITY_CHECK #-}
record Bad : Set₁ where
  constructor mkBad
  field bad : ℘ (℘ Bad)

f : ℘ Bad → Bad
f p = mkBad (_≡ p)

fInj : ∀ {p q} → f p ≡ f q → p ≡ q
fInj {p} fp≡fq = subst (λ p≡ → p≡ p) (badInj fp≡fq) refl
  where
  badInj : ∀ {a b} → mkBad a ≡ mkBad b → a ≡ b
  badInj refl = refl

P₀ : ℘ Bad
P₀ x = Σ[ P ∈ ℘ Bad ] x ≡ f P × ¬ (P x)

x₀ : Bad
x₀ = f P₀

P₀x₀→¬P₀x₀ : P₀ x₀ → ¬ P₀ x₀
P₀x₀→¬P₀x₀ (P , x₀≡fP , ¬Px₀) P₀x₀ = ¬Px₀ (subst (λ P → P x₀) (fInj x₀≡fP) P₀x₀)

¬P₀x₀→P₀x₀ : ¬ P₀ x₀ → P₀ x₀
¬P₀x₀→P₀x₀ ¬P₀x₀ = P₀ , refl , ¬P₀x₀

¬P₀x₀ : ¬ P₀ x₀
¬P₀x₀ P₀x₀ = P₀x₀→¬P₀x₀ P₀x₀ P₀x₀

false : ⊥
false = ¬P₀x₀ (¬P₀x₀→P₀x₀ ¬P₀x₀)
