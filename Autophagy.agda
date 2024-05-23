module Autophagy (Level : Set) (_<_ : Level → Level → Set) where

data Ctxt : Set
data _≡ᶜ_ : Ctxt → Ctxt → Set
data Type (Γ : Ctxt) : Set
data _≡ᵀ_ : ∀ {Γ Γ'} → Type Γ → Type Γ' → Set
data _⇒_ : Ctxt → Ctxt → Set
data _∋_ : ∀ Γ → Type Γ → Set
data Term : ∀ Γ → Type Γ → Set
data _≡ᵗ_ : ∀ {Γ Γ' A A'} → Term Γ A → Term Γ' A' → Set

infixl 30 _∷_
data Ctxt where
  ∙ : Ctxt
  _∷_ : (Γ : Ctxt) → Type Γ → Ctxt

data _≡ᶜ_ where
  ∙≡ : ∙ ≡ᶜ ∙
  ∷≡ : ∀ {Γ Γ' A A'} → Γ ≡ᶜ Γ' → A ≡ᵀ A' → Γ ∷ A ≡ᶜ Γ' ∷ A'

infixl 40 _[_]ᵀ
data Type Γ where
  coeᵀ : ∀ {Γ'} → Γ' ≡ᶜ Γ → Type Γ' → Type Γ
  U : Level → Type Γ
  el : ∀ k → Term Γ (U k) → Type Γ
  Π : (A : Type Γ) → Type (Γ ∷ A) → Type Γ
  _[_]ᵀ : ∀ {Δ} → Type Δ → Γ ⇒ Δ → Type Γ

infixr 10 _:+_
infixl 20 _∘_
data _⇒_ where
  coeˢ : ∀ {Γ Γ' Δ Δ'} → Γ ≡ᶜ Γ' → Δ ≡ᶜ Δ' → Γ ⇒ Δ → Γ' ⇒ Δ'
  id : ∀ {Γ} → Γ ⇒ Γ
  wk : ∀ {Γ} → (A : Type Γ) → Γ ∷ A ⇒ Γ
  _:+_ : ∀ {Γ Δ A} → (σ : Γ ⇒ Δ) → Term Γ (A [ σ ]ᵀ) → Γ ⇒ Δ ∷ A
  _∘_ : ∀ {Γ Δ Ξ} → Δ ⇒ Ξ → Γ ⇒ Δ → Γ ⇒ Ξ

infixl 40 _⦅_⦆ᵀ
_⦅_⦆ᵀ : ∀ {Γ A} → Type (Γ ∷ A) → Term Γ A → Type Γ
_↑_ : ∀ {Γ Δ} (σ : Γ ⇒ Δ) → (A : Type Δ) → Γ ∷ A [ σ ]ᵀ ⇒ Δ ∷ A

infix 10 _∋_
data _∋_ where
  here : ∀ {Γ A} → Γ ∷ A ∋ A [ wk A ]ᵀ
  there : ∀ {Γ A B} → Γ ∋ A → Γ ∷ B ∋ A [ wk B ]ᵀ

infixl 40 _[_]ᵗ
data Term where
  coeᵗ : ∀ {Γ Γ' A A'} → A ≡ᵀ A' → Term Γ A → Term Γ' A'
  var′ : ∀ {Γ} (A : Type Γ) → Γ ∋ A → Term Γ A
  var : ∀ {Γ A} → Term (Γ ∷ A) (A [ wk A ]ᵀ)
  abs : ∀ {Γ A B} → Term (Γ ∷ A) B → Term Γ (Π A B)
  app : ∀ {Γ A B} → Term Γ (Π A B) → (a : Term Γ A) → Term Γ (B ⦅ a ⦆ᵀ)
  Uᵗ : ∀ {Γ} j k → j < k → Term Γ (U k)
  Πᵗ : ∀ {Γ k} (a : Term Γ (U k)) → Term (Γ ∷ el k a) (U k) → Term Γ (U k)
  _[_]ᵗ : ∀ {Γ Δ A} → Term Δ A → (σ : Γ ⇒ Δ) → Term Γ (A [ σ ]ᵀ)

data _≡ᵀ_ where
  -- equivalence
  reflᵀ : ∀ {Γ} {A : Type Γ} → A ≡ᵀ A
  symᵀ : ∀ {Γ Γ'} {A : Type Γ} {B : Type Γ'} → A ≡ᵀ B → B ≡ᵀ A
  transᵀ : ∀ {Γ Γ' Γ''} {A : Type Γ} {B : Type Γ'} {C : Type Γ''} →
    A ≡ᵀ B → B ≡ᵀ C → A ≡ᵀ C
  -- coherence
  cohᵀ : ∀ {Γ Γ' A} (p : Γ' ≡ᶜ Γ) → coeᵀ p A ≡ᵀ A
  -- computation
  elU : ∀ {Γ Γ' j k lt} → el {Γ} k (Uᵗ j k lt) ≡ᵀ U {Γ'} j
  elΠ : ∀ {Γ k a b} → el {Γ} k (Πᵗ a b) ≡ᵀ Π (el k a) (el k b)
  -- congruence
  U≡ : ∀ {Γ Γ' k} → Γ ≡ᶜ Γ' → U {Γ} k ≡ᵀ U {Γ'} k
  el≡ : ∀ {Γ Γ' k a b} → a ≡ᵗ b → el {Γ} k a ≡ᵀ el {Γ'} k b
  Π≡ : ∀ {Γ Γ' A A' B B'} → A ≡ᵀ A' → B ≡ᵀ B' → Π {Γ} A B ≡ᵀ Π {Γ'} A' B'
  []≡ : ∀ {Γ Δ} {A B : Type Δ} {σ : Γ ⇒ Δ} → A ≡ᵀ B → A [ σ ]ᵀ ≡ᵀ B [ σ ]ᵀ
  -- subst laws
  idᵀ : ∀ {Γ A} → A [ id {Γ} ]ᵀ ≡ᵀ A
  ∘ᵀ : ∀ {Γ Δ Ξ A} {σ : Δ ⇒ Ξ} {τ : Γ ⇒ Δ} → A [ σ ]ᵀ [ τ ]ᵀ ≡ᵀ A [ σ ∘ τ ]ᵀ
  -- substitution
  U[] : ∀ {Γ Δ k} {σ : Γ ⇒ Δ} → U k [ σ ]ᵀ ≡ᵀ U {Γ} k
  el[] : ∀ {Γ Δ k a} {σ : Γ ⇒ Δ} → el k a [ σ ]ᵀ ≡ᵀ el k (coeᵗ U[] (a [ σ ]ᵗ))
  Π[] : ∀ {Γ Δ A B} {σ : Γ ⇒ Δ} → (Π A B) [ σ ]ᵀ ≡ᵀ Π (A [ σ ]ᵀ) (B [ σ ↑ A ]ᵀ)

A ⦅ a ⦆ᵀ = A [ id :+ coeᵗ (symᵀ idᵀ) a ]ᵀ
σ ↑ A = σ ∘ wk _ :+ coeᵗ ∘ᵀ var

infixl 40 _⦅_⦆ᵗ
_⦅_⦆ᵗ : ∀ {Γ A B} → Term (Γ ∷ A) B → (a : Term Γ A) → Term Γ (B ⦅ a ⦆ᵀ)
b ⦅ a ⦆ᵗ = b [ id :+ coeᵗ (symᵀ idᵀ) a ]ᵗ

reflᶜ : ∀ {Γ} → Γ ≡ᶜ Γ
reflᶜ {∙} = ∙≡
reflᶜ {Γ ∷ A} = ∷≡ reflᶜ reflᵀ

symᶜ : ∀ {Γ Γ'} → Γ ≡ᶜ Γ' → Γ' ≡ᶜ Γ
symᶜ ∙≡ = ∙≡
symᶜ (∷≡ p q) = ∷≡ (symᶜ p) (symᵀ q)

transᶜ : ∀ {Γ Γ' Γ''} → Γ ≡ᶜ Γ' → Γ' ≡ᶜ Γ'' → Γ ≡ᶜ Γ''
transᶜ ∙≡ ∙≡ = ∙≡
transᶜ (∷≡ p q) (∷≡ p' q') = ∷≡ (transᶜ p p') (transᵀ q q')

data _≡ᵗ_ where
  -- equivalence
  reflᵗ : ∀ {Γ A} {a : Term Γ A} → a ≡ᵗ a
  symᵗ : ∀ {Γ Γ' A B} {a : Term Γ A} {b : Term Γ' B} → a ≡ᵗ b → b ≡ᵗ a
  transᵗ : ∀ {Γ Γ' Γ'' A B C} {a : Term Γ A} {b : Term Γ' B} {c : Term Γ'' C} →
    a ≡ᵗ b → b ≡ᵗ c → a ≡ᵗ c
  -- coherence
  cohᵗ : ∀ {Γ Γ'} {A : Type Γ} {A' : Type Γ'} {a} (p : A ≡ᵀ A') → coeᵗ p a ≡ᵗ a
  -- computation (don't I need to weaken b in η...?)
  β : ∀ {Γ A B a b} → app {Γ} {A} {B} (abs b) a ≡ᵗ b ⦅ a ⦆ᵗ
  η : ∀ {Γ A B b} → abs {Γ} {A} (app {B = B} b var) ≡ᵗ b
  -- congruence
  var≡ : ∀ {Γ Γ' A A'} → A ≡ᵀ A' → var {Γ} {A} ≡ᵗ var {Γ'} {A'}
  abs≡ : ∀ {Γ Γ' A A' B B'} {b : Term (Γ ∷ A) B} {b' : Term (Γ' ∷ A') B'} →
    A ≡ᵀ A' → b ≡ᵗ b' → abs b ≡ᵗ abs b'
  app : ∀ {Γ Γ' A A' B B'} {b : Term Γ (Π A B)} {b' : Term Γ' (Π A' B')} {a a'} →
    b ≡ᵗ b' → a ≡ᵗ a' → app b a ≡ᵗ app b' a'
  Uᵗ≡ : ∀ {Γ Γ' j k lt lt'} → Γ ≡ᶜ Γ' → Uᵗ {Γ} j k lt ≡ᵗ Uᵗ {Γ'} j k lt'
  Πᵗ≡ : ∀ {Γ Γ' k} {a : Term Γ (U k)} {a' : Term Γ' (U k)} {b b'} →
    a ≡ᵗ a' → b ≡ᵗ b → Πᵗ a b ≡ᵗ Πᵗ a' b'
  -- subst laws
  idᵗ : ∀ {Γ A} {a : Term Γ A} → a [ id {Γ} ]ᵗ ≡ᵗ a
  ∘ᵗ : ∀ {Γ Δ Ξ A} {σ : Δ ⇒ Ξ} {τ : Γ ⇒ Δ} {a : Term Ξ A} → a [ σ ]ᵗ [ τ ]ᵗ ≡ᵗ a [ σ ∘ τ ]ᵗ
  -- substitution
  var[] : ∀ {Γ Δ A} {σ : Γ ⇒ Δ} {a : Term Γ (A [ σ ]ᵀ)} → var [ σ :+ a ]ᵗ ≡ᵗ a
  abs[] : ∀ {Γ Δ A B b} {σ : Γ ⇒ Δ} → abs {B = B} b [ σ ]ᵗ ≡ᵗ abs (b [ σ ↑ A ]ᵗ)
  app[] : ∀ {Γ Δ A B b a} {σ : Γ ⇒ Δ} →
    app {A = A} {B = B} b a [ σ ]ᵗ ≡ᵗ app (coeᵗ Π[] (b [ σ ]ᵗ)) (a [ σ ]ᵗ)
  U[] : ∀ {Γ Δ j k lt} {σ : Γ ⇒ Δ} → Uᵗ j k lt [ σ ]ᵗ ≡ᵗ Uᵗ {Δ} j k lt
  Π[] : ∀ {Γ Δ k a b} {σ : Γ ⇒ Δ} →
    Πᵗ {k = k} a b [ σ ]ᵗ ≡ᵗ Πᵗ (coeᵗ U[] (a [ σ ]ᵗ)) (coeᵗ U[] (b [ coeˢ (∷≡ reflᶜ el[]) reflᶜ (σ ↑ el _ a) ]ᵗ))