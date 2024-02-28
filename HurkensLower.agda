{-# OPTIONS --rewriting #-}

{-
{-# OPTIONS --type-in-type #-}

record Lower (A : Set₁) : Set where
  constructor lower
  field raise : A

open Lower
-}

postulate
  _≡_ : ∀ {A : Set₁} → A → A → Set
  Lower : (A : Set₁) → Set
  lower : ∀ {A} → A → Lower A
  raise : ∀ {A} → Lower A → A
  beta : ∀ {A} {a : A} → raise (lower a) ≡ a

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE beta #-}

data ⊥ : Set where

℘ : ∀ {ℓ} → Set ℓ → Set _
℘ {ℓ} S = S → Set

U : Set
U = Lower (∀ (X : Set) → (℘ (℘ X) → X) → ℘ (℘ X))

τ : ℘ (℘ U) → U
τ t = lower (λ X f p → t (λ x → p (f (raise x X f))))

σ : U → ℘ (℘ U)
σ s = raise s U τ

Δ : ℘ U
Δ y = Lower (∀ p → σ y p → p (τ (σ y))) → ⊥

Ω : U 
Ω = τ (λ p → (∀ x → σ x p → p x))

R : ∀ p → (∀ x → σ x p → p x) → p Ω
R _ 𝟙 = 𝟙 Ω (λ x → 𝟙 (τ (σ x)))

M : ∀ x → σ x Δ → Δ x
M _ 𝟚 𝟛 =
  let 𝟛 = raise 𝟛
  in 𝟛 Δ 𝟚 (lower (λ p → 𝟛 (λ y → p (τ (σ y)))))

L : (∀ p → (∀ x → σ x p → p x) → p Ω) → ⊥
L 𝟘 = 𝟘 Δ M (lower (λ p → 𝟘 (λ y → p (τ (σ y)))))

false : ⊥
false = L R
