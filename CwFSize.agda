-- term contexts
open import Agda.Builtin.Unit

𝒞 : Set₁
𝒞 = Set

_⇒_ : 𝒞 → 𝒞 → Set
Δ ⇒ Γ = Δ → Γ

id : ∀ {Γ} → Γ ⇒ Γ
id x = x

_∘_ : ∀ {Ξ Δ Γ} → (Δ ⇒ Γ) → (Ξ ⇒ Δ) → (Ξ ⇒ Γ)
(γ ∘ δ) x = γ (δ x)

∙ : 𝒞
∙ = ⊤

⟨⟩ : ∀ {Γ} → Γ ⇒ ∙
⟨⟩ _ = tt

-- Ty are types that depend on a context

Ty : 𝒞 → Set₁
Ty Γ = Γ → Set

infixl 40 _[_]
_[_] : ∀ {Δ Γ} → Ty Γ → (Δ ⇒ Γ) → Ty Δ
(A [ γ ]) x = A (γ x)

-- Tm are terms of Ty

Tm : ∀ Γ → Ty Γ → Set
Tm Γ A = (x : Γ) → A x

infixl 40 _⟮_⟯
_⟮_⟯ : ∀ {Δ Γ} {A : Ty Γ} → Tm Γ A → (γ : Δ ⇒ Γ) → Tm Δ (A [ γ ])
(a ⟮ γ ⟯) x = a (γ x)

-- Contexts are lists of types

infixl 30 _▷_
record _▷_ (Γ : 𝒞) (A : Ty Γ) : 𝒞 where
  constructor _∷_
  field
    p : Γ
    q : A p
open _▷_

⟨_,_⟩ : ∀ {Δ Γ} {A : Ty Γ} → (γ : Δ ⇒ Γ) → Tm Δ (A [ γ ]) → (Δ ⇒ Γ ▷ A)
⟨ γ , a ⟩ x = γ x ∷ a x

_↑_ : ∀ {Δ Γ : 𝒞} → (γ : Δ ⇒ Γ) → (A : Ty Γ) → (Δ ▷ A [ γ ] ⇒ Γ ▷ A)
γ ↑ A = ⟨ γ ∘ p , q ⟩

-- ⊥-structure
open import Data.Empty renaming (⊥ to ⊥′)

⊥ : ∀ {Γ} → Ty Γ
⊥ _ = ⊥′

abs : ∀ {Γ} → (A : Ty Γ) → Tm Γ ⊥ → Tm Γ A
abs _ b x = ⊥-elim (b x)

-- Π-structure

Π : ∀ {Γ} → (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
Π A B x = (a : A x) → B (x ∷ a)

lam : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
      Tm (Γ ▷ A) B → Tm Γ (Π A B)
lam b x a = b (x ∷ a)

app : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
      Tm Γ (Π A B) → Tm (Γ ▷ A) B
app b (x ∷ a) = b x a

-- 𝒰-structure

data 𝒰′ : Set
el′ : 𝒰′ → Set

data 𝒰′ where
  ⊥ᶜ′ : 𝒰′
  Πᶜ′ : (A : 𝒰′) → (el′ A → 𝒰′) → 𝒰′

el′ ⊥ᶜ′ = ⊥′
el′ (Πᶜ′ A B) = (a : el′ A) → el′ (B a)

𝒰 : ∀ {Γ} → Ty Γ
𝒰 _ = 𝒰′

el : ∀ {Γ} → Tm Γ 𝒰 → Ty Γ
el t x = el′ (t x)

⊥ᶜ : ∀ {Γ} → Tm Γ 𝒰
⊥ᶜ _ = ⊥ᶜ′

Πᶜ : ∀ {Γ} → (A : Tm Γ 𝒰) → Tm (Γ ▷ el A) 𝒰 → Tm Γ 𝒰
Πᶜ A B x = Πᶜ′ (A x) (λ a → B (x ∷ a))

absurd : ∀ {ℓ} {A : Set ℓ} → Tm ∙ ⊥ → A
absurd b = ⊥-elim (b tt)

-- Size-structure

data Size : Set where
  suc : Size → Size
  lim : {A : 𝒰′} → (el′ A → Size) → Size

postulate
  _<′_ : Size → Size → Set
  _≤′_ : Size → Size → Set

base : Size
base = lim {⊥ᶜ′} ⊥-elim

Sz : 𝒞 → Set
Sz Γ = Γ → Size

_<_ : ∀ {Γ} → Sz Γ → Sz Γ → Set
(r < s) = ∀ {x} → r x <′ s x

_≤_ : ∀ {Γ} → Sz Γ → Sz Γ → Set
(r ≤ s) = ∀ {x} → r x ≤′ s x

infixl 40 _⦅_⦆
_⦅_⦆ : ∀ {Δ Γ} → Sz Γ → (Δ ⇒ Γ) → Sz Δ
(s ⦅ γ ⦆) x = s (γ x)

infixl 30 _+
record _+ (Γ : 𝒞) : 𝒞 where
  constructor _∷_
  field
    p : Γ
    q : Size
open _+

⟪_,_⟫ : ∀ {Δ Γ} {A : Ty Γ} → (γ : Δ ⇒ Γ) → Sz Δ → (Δ ⇒ Γ +)
⟪ γ , s ⟫ x = γ x ∷ s x

infixl 30 _+<_
record _+<_ (Γ : 𝒞) (s : Sz Γ) : 𝒞 where
  constructor _*_*_
  field
    p : Γ
    q : Size
    r : q <′ s p
open _+<_

⟪_,_,_⟫ : ∀ {Δ Γ} {A : Ty Γ} {s : Sz Γ} → (γ : Δ ⇒ Γ) → (r : Sz Δ) → (r < s ⦅ γ ⦆) → (Δ ⇒ Γ +< s)
⟪ γ , r , p ⟫ x = γ x * r x * p

--v0 : ∀ {Γ} → Sz (Γ +)
--v0 (x ∷ s) = s x

--v1 : ∀ {Γ s} → Sz ((Γ +) +< s)
--v1 ((x ∷ s) * r * p) = s x

rename : ∀ {Γ s} → ((Γ +) +< s) → ((Γ +) +< s)
rename ((x ∷ s) * r * p) = ((x ∷ {!   !}) * r * p)

⊙ : ∀ {Γ} → Sz Γ
⊙ _ = base

↑_ : ∀ {Γ} → Sz Γ → Sz Γ
(↑ s) x = suc (s x)

all : ∀ {Γ} → (s : Sz Γ) → Ty (Γ +< s) → Ty Γ
all {Γ} s A x = (r : Sz Γ) → (p : r < s) → A (x * r x * p {x})

slam : ∀ {Γ} → (s : Sz Γ) → (A : Ty (Γ +< s)) → Tm (Γ +< s) A → Tm Γ (all s A)
slam s A e x r p = e (x * r x * p)

sapp : ∀ {Γ} → (s : Sz Γ) → (A : Ty (Γ +< s)) → Tm Γ (all s A) → Tm (Γ +< s) A
-- sapp s A e (x * r * p) = e x (λ _ → r) (λ {_} → p)

-- Γ, α, f : ∀ β < α. τ[β ↦ α] ⊢ e : τ
---------------------------------------
-- Γ ⊢ fix f [α] : τ ≔ e : ∀ α. τ
--fix : ∀ {Γ} → (A : Ty (Γ +)) → Tm ((Γ +) ▷ all v0 (A [ p ])) {!   !} → {!   !}

{- Equations as definitional equalities -}
open import Relation.Binary.PropositionalEquality.Core

-- Category laws and terminality

ass : ∀ {Θ Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {ε : Θ ⇒ Ξ} →
      (γ ∘ δ) ∘ ε ≡ γ ∘ (δ ∘ ε)
ass = refl

idl : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → id ∘ γ ≡ γ
idl = refl

idr : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → γ ∘ id ≡ γ
idr = refl

⟨⟩η : ∀ {Γ} {γ : Γ ⇒ ∙} → γ ≡ ⟨⟩
⟨⟩η = refl

-- Ty and Tm functor laws

[id] : ∀ {Γ} {A : Ty Γ} → A [ id ] ≡ A
[id] = refl

[∘] : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} →
      A [ γ ] [ δ ] ≡ A [ γ ∘ δ ]
[∘] = refl

⟮id⟯ : ∀ {Γ} {A : Ty Γ} {a : Tm Γ A} → a ⟮ id ⟯ ≡ a
⟮id⟯ = refl

⟮∘⟯ : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} {a : Tm Γ A} →
      a ⟮ γ ∘ δ ⟯ ≡ a ⟮ γ ⟯ ⟮ δ ⟯
⟮∘⟯ = refl

-- Context comprehension laws

infix 40 _∋⟨_,_⟩
_∋⟨_,_⟩ : ∀ {Δ Γ} → (A : Ty Γ) → (γ : Δ ⇒ Γ) → Tm Δ (A [ γ ]) → (Δ ⇒ Γ ▷ A)
_ ∋⟨ γ , a ⟩ = ⟨ γ , a ⟩

pβ : ∀ {Δ Γ} {A : Ty Γ} {γ : Δ ⇒ Γ} {a : Tm Δ (A [ γ ])} →
     p {Γ} {A} ∘ ⟨ γ , a ⟩ ≡ γ
pβ = refl

qβ : ∀ {Δ Γ} {A : Ty Γ} {γ : Δ ⇒ Γ} {a : Tm Δ (A [ γ ])} →
     q {Γ} {A} ⟮ ⟨ γ , a ⟩ ⟯ ≡ a
qβ = refl

⟨pq⟩ : ∀ {Γ} {A : Ty Γ} → ⟨ p , q ⟩ ≡ id {Γ ▷ A}
⟨pq⟩ = refl

⟨⟩∘ : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} {a : Tm Δ (A [ γ ])} →
      A ∋⟨ γ , a ⟩ ∘ δ ≡ ⟨ γ ∘ δ , a ⟮ δ ⟯ ⟩
⟨⟩∘ = refl

-- ⊥-stucture substitution laws

⊥[] : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → ⊥ [ γ ] ≡ ⊥
⊥[] = refl

abs⟮⟯ : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → {A : Ty Γ} → {a : Tm Γ ⊥} →
        (abs A a) ⟮ γ ⟯ ≡ abs (A [ γ ]) (a ⟮ γ ⟯)
abs⟮⟯ = refl

-- Π-structure computation, uniqueness, and substitution laws

Πβ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} {b : Tm (Γ ▷ A) B} →
     app (lam b) ≡ b
Πβ = refl

Πη : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} {a : Tm Γ (Π A B)} →
     lam (app a) ≡ a
Πη = refl

Π[] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} {γ : Δ ⇒ Γ} →
      (Π A B) [ γ ] ≡ Π (A [ γ ]) (B [ γ ↑ A ])
Π[] = refl

lam⟮⟯ : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} {γ : Δ ⇒ Γ} {b : Tm (Γ ▷ A) B} →
        (lam b) ⟮ γ ⟯ ≡ lam (b ⟮ γ ↑ A ⟯)
lam⟮⟯ = refl

app⟮⟯ : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} {γ : Δ ⇒ Γ} {a : Tm Γ (Π A B)} →
        (app a) ⟮ γ ↑ A ⟯ ≡ app (a ⟮ γ ⟯)
app⟮⟯ = refl

-- 𝒰-structure computation and substitution laws

⊥ᶜβ : ∀ {Γ} → el {Γ} ⊥ᶜ ≡ ⊥
⊥ᶜβ = refl

Πᶜβ : ∀ {Γ} {A : Tm Γ 𝒰} {B : Tm (Γ ▷ el A) 𝒰} →
      el (Πᶜ A B) ≡ Π (el A) (el B)
Πᶜβ = refl

𝒰[] : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → 𝒰 [ γ ] ≡ 𝒰
𝒰[] = refl

el[] : ∀ {Δ Γ} {γ : Δ ⇒ Γ} {a : Tm Γ 𝒰} → (el a) [ γ ] ≡ el (a ⟮ γ ⟯)
el[] = refl

⊥ᶜ⟮⟯ : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → (⊥ᶜ ⟮ γ ⟯) ≡ ⊥ᶜ
⊥ᶜ⟮⟯ = refl

Πᶜ⟮⟯ : ∀ {Δ Γ} {γ : Δ ⇒ Γ} {A : Tm Γ 𝒰} {B : Tm (Γ ▷ el A) 𝒰} →
       (Πᶜ A B) ⟮ γ ⟯ ≡ Πᶜ (A ⟮ γ ⟯) (B ⟮ γ ↑ el A ⟯)
Πᶜ⟮⟯ = refl