open import Agda.Primitive

data _≡_ {ℓ} : ∀ {A : Set ℓ} → A → A → Set (lsuc ℓ) where
  refl : ∀ {A} {a : A} → a ≡ a
  funext : ∀ {A : Set ℓ} {B : A → Set ℓ} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g

sym : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
sym refl = refl
sym (funext h) = funext (λ x → sym (h x))

trans : ∀ {ℓ} {A : Set ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl
trans refl (funext h) = funext h
trans (funext h) refl = funext h
trans (funext fg) (funext gh) = funext (λ x → trans (fg x) (gh x))
