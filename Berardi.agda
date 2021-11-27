{-# OPTIONS --type-in-type #-}

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; id)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; sym; cong-app)

record _◁_ (A B : Set) : Set where
  field
    ϕ : A → B
    ψ : B → A
    retract : ψ ∘ ϕ ≡ id

record _◁′_ (A B : Set) : Set where
  constructor _,_,_
  field
    ϕ : A → B
    ψ : B → A
    retract : A ◁ B → ψ ∘ ϕ ≡ id
open _◁′_

-- Applying the axiom of choice on A ◁ B → A ◁ B (proven by identity),
-- which is equivalent to A ◁ B → Σ[ g ∈ A → B ] Σ[ h ∈ B → A ] h ∘ g ≡ id,
-- yields Σ[ g ∈ A → B ] Σ[ h ∈ B → A ] A ◁ B → h ∘ g ≡ id,
-- which is A ◁′ B above.
-- Excluded middle implies that A ≡ ¬ A is a contradiction.
postulate
  t : ∀ A B → A ◁′ B
  EM : ∀ (A : Set) → A ⊎ (¬ A)

A≢¬A : ∀ (A : Set) → A ≡ (¬ A) → ⊥
A≢¬A A p with EM A
... | inj₁ a = subst id p a a
... | inj₂ ¬a = ¬a (subst id (sym p) ¬a)

℘ : Set → Set
℘ X = X → Set

U : Set
U = ∀ X → ℘ X

projᵤ : U → ℘ U
projᵤ u = u U

injᵤ : ℘ U → U
injᵤ f X =
  let _ , ψ , _ = t (℘ X) (℘ U)
      ϕ , _ , _ = t (℘ U) (℘ U)
  in ψ (ϕ f)

projᵤ∘injᵤ : projᵤ ∘ injᵤ ≡ id
projᵤ∘injᵤ =
  retract (t (℘ U) (℘ U)) record { ϕ = id; ψ = id; retract = refl }

_∈_ : U → U → Set
u ∈ v = projᵤ u v

Russell : ℘ U
Russell u = ¬ u ∈ u

r : U
r = injᵤ Russell

false : ⊥
false = A≢¬A (r ∈ r) (cong-app (cong-app projᵤ∘injᵤ Russell) r)
