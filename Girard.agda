{-# OPTIONS --rewriting #-}
-- {-# OPTIONS --type-in-type #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

{-
record Lower {ℓ'} ℓ (A : Set (ℓ' ⊔ ℓ)) : Set ℓ where
  constructor lower
  field raise : A

open Lower
-}

postulate
  Lower : ∀ {ℓ'} ℓ → (A : Set (ℓ' ⊔ ℓ)) → Set ℓ
  lower : ∀ {ℓ'} {ℓ} {A} → A → Lower {ℓ'} ℓ A
  raise : ∀ {ℓ'} {ℓ} {A} → Lower {ℓ'} ℓ A → A
  beta : ∀ {ℓ'} {ℓ} {A} {a : A} → raise (lower {ℓ'} {ℓ} a) ≡ a

{-# REWRITE beta #-}

⊥ : Set _
⊥ = ∀ (p : Set) → p

℘ : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
℘ {ℓ} S = S → Set ℓ

U : ∀ {ℓ} → Set ℓ
U {ℓ} = Lower ℓ (∀ (X : Set ℓ) → (℘ (℘ X) → X) → ℘ (℘ X))

τ : ∀ {ℓ} → ℘ (℘ (U {ℓ})) → U {ℓ}
τ {ℓ} t = lower (λ X f p → t (λ x → p (f (raise x X f))))

σ : ∀ {ℓ} → U {ℓ} → ℘ (℘ (U {ℓ}))
σ s = (raise s) U τ

Δ : ℘ (U {lsuc lzero})
Δ y = Lower lzero (∀ p → σ y p → p (τ (σ y))) → ∀ (p : Set) → p

Ω : U {lsuc lzero}
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
