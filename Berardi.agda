{-# OPTIONS --type-in-type #-}

open import Data.Empty
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; id)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; cong; sym)

record _◁_ {ℓ} (A B : Set ℓ) : Set ℓ where
  constructor _,_,_
  field
    ϕ : A → B
    ψ : B → A
    retract : ψ ∘ ϕ ≡ id
open _◁_

record _◁′_ {ℓ} (A B : Set ℓ) : Set ℓ where
  constructor _,_,_
  field
    ϕ : A → B
    ψ : B → A
    retract : A ◁ B → ψ ∘ ϕ ≡ id
open _◁′_

postulate
  EM : ∀ {ℓ} (A : Set ℓ) → A ⊎ (¬ A)

℘ : ∀ {ℓ} → Set ℓ → Set _
℘ X = X → Set

t : ∀ {ℓ} (A B : Set ℓ) → ℘ A ◁′ ℘ B
t A B with EM (℘ A ◁ ℘ B)
... | inj₁  ℘A◁℘B =
      let ϕ , ψ , retract = ℘A◁℘B
      in ϕ , ψ , λ _ → retract
... | inj₂ ¬℘A◁℘B =
      (λ _ _ → ⊥) , (λ _ _ → ⊥) , λ ℘A◁℘B → ⊥-elim (¬℘A◁℘B ℘A◁℘B)

-- type-in-type allows U to be put into Set...
U : Set
U = ∀ X → ℘ X

-- ...so that u: U can be applied to U itself
projᵤ : U → ℘ U
projᵤ u = u U

injᵤ : ℘ U → U
injᵤ f X =
  let _ , ψ , _ = t X U
      ϕ , _ , _ = t U U
  in ψ (ϕ f)

projᵤ∘injᵤ : projᵤ ∘ injᵤ ≡ id
projᵤ∘injᵤ = retract (t U U) (id , id , refl)

_∈_ : U → U → Set
u ∈ v = projᵤ u v

Russell : ℘ U
Russell u = ¬ u ∈ u

r : U
r = injᵤ Russell

-- up to here EM + impredicativity is enough,
-- as long as _≡_ itself is in the impredicative universe,
-- but to go further, large elimination (via subst) is required
r∈r≡r∉r : r ∈ r ≡ (¬ r ∈ r)
r∈r≡r∉r = cong (λ f → f Russell r) projᵤ∘injᵤ

r∉r : ¬ r ∈ r
r∉r r∈r = subst id r∈r≡r∉r r∈r r∈r

false : ⊥
false = r∉r (subst id (sym r∈r≡r∉r) r∉r)
