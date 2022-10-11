open import Level
-- open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.HeterogeneousEquality
  using (subst) renaming (_≅_ to _≡_)

record CwF {ℓ} : Set (suc ℓ) where
  infixl 30 _▷_
  infixl 40 _[_]
  field
    -- Category with terminal element
    𝒞   : Set ℓ
    _⇒_ : 𝒞 → 𝒞 → Set ℓ
    id  : ∀ {Γ} → Γ ⇒ Γ
    _∘_ : ∀ {Ξ Δ Γ} → (Δ ⇒ Γ) → (Ξ ⇒ Δ) → (Ξ ⇒ Γ)
    ∙   : 𝒞
    ⟨⟩  : ∀ {Γ} → Γ ⇒ ∙

    -- Category laws and terminality
    ass : ∀ {Θ Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {ε : Θ ⇒ Ξ} →
            (γ ∘ δ) ∘ ε ≡ γ ∘ (δ ∘ ε)
    idl : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → id ∘ γ ≡ γ
    idr : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → γ ∘ id ≡ γ
    ⟨⟩η : ∀ {Γ} {γ : Γ ⇒ ∙} → γ ≡ ⟨⟩ {Γ}

    -- Type functor and functor laws
    Ty   : 𝒞 → Set ℓ
    _[_] : ∀ {Δ Γ} → Ty Γ → (Δ ⇒ Γ) → Ty Δ
    [id] : ∀ {Γ} {A : Ty Γ} → A [ id ] ≡ A
    [∘]  : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} →
           A [ γ ] [ δ ] ≡ A [ γ ∘ δ ]

    -- Term functor and functor laws
    Tm   : ∀ Γ → Ty Γ → Set ℓ
    _⟮_⟯ : ∀ {Δ Γ} {A : Ty Γ} → Tm Γ A → (γ : Δ ⇒ Γ) → Tm Δ (A [ γ ])
    ⟮id⟯ : ∀ {Γ} {A : Ty Γ} {a : Tm Γ A} → a ⟮ id ⟯ ≡ a
    ⟮∘⟯  : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} {a : Tm Γ A} →
           a ⟮ γ ∘ δ ⟯ ≡ a ⟮ γ ⟯ ⟮ δ ⟯
    -- The last two don't type check with homogeneous equality:
    -- a ⟮ id ⟯ : A [ id ] but a : A, requiring [id]
    -- a ⟮ γ ∘ δ ⟯ : A [ γ ∘ δ ] but a ⟮ γ ⟯ ⟮ δ ⟯ : A [ γ ] [ δ ], requiring [∘]

    -- Context comprehension
    _▷_   : ∀ Γ → Ty Γ → 𝒞
    ⟨_,_⟩ : ∀ {Δ Γ} {A : Ty Γ} → (γ : Δ ⇒ Γ) → Tm Δ (A [ γ ]) → (Δ ⇒ Γ ▷ A)
    p     : ∀ {Γ} {A : Ty Γ} → (Γ ▷ A ⇒ Γ)
    q     : ∀ {Γ} {A : Ty Γ} → Tm (Γ ▷ A) (A [ p ])

    -- Context comprehension laws
    pβ   : ∀ {Δ Γ} {A : Ty Γ} {γ : Δ ⇒ Γ} {a : Tm Δ (A [ γ ])} →
           p ∘ ⟨ γ , a ⟩ ≡ γ
    qβ   : ∀ {Δ Γ} {A : Ty Γ} {γ : Δ ⇒ Γ} {a : Tm Δ (A [ γ ])} →
           q ⟮ ⟨ γ , a ⟩ ⟯ ≡ a
    ⟨pq⟩ : ∀ {Γ} {A : Ty Γ} → ⟨ p {Γ} {A} , q {Γ} {A} ⟩ ≡ id {Γ ▷ A}
    ⟨⟩∘  : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} {a : Tm Δ (A [ γ ])} →
           ⟨ γ , a ⟩ ∘ δ ≡ ⟨ γ ∘ δ , subst (Tm Ξ) [∘] (a ⟮ δ ⟯) ⟩
    -- The second doesn't type check with homogeneous equality:
    -- q ⟮ ⟨ γ , a ⟩ ⟯ : Tm Δ (A [ p ] [ ⟨ γ , a ⟩ ]) but a : Tm Δ (A [ γ ]), requiring [∘] and pβ
    -- The fourth doesn't type check without an explicit coercion:
    -- ⟨ γ ∘ δ , ? ⟩ needs Tm Ξ (A [ γ ∘ δ ]) but a ⟮ δ ⟯ : Tm Ξ (A [ γ ] [ δ ]), requiring [∘]

open CwF {{...}}

_↑_ : ∀ {ℓ} {{cwf : CwF {ℓ}}} {Δ Γ : 𝒞} → (γ : Δ ⇒ Γ) → (A : Ty Γ) → (Δ ▷ A [ γ ] ⇒ Γ ▷ A)
γ ↑ A = ⟨ γ ∘ p , subst (Tm _) [∘] q ⟩

record Structures {ℓ} : Set (suc ℓ) where
  field
    {{cwf}} : CwF {ℓ}

    -- ⊤-structure
    ⊤    : ∀ {Γ : 𝒞} → Ty Γ
    ∗    : ∀ {Γ : 𝒞} → Tm Γ ⊤
    ⊤η   : ∀ {Γ : 𝒞} {a : Tm Γ ⊤} → a ≡ ∗ {Γ}
    ⊤[]  : ∀ {Δ Γ : 𝒞} {γ : Δ ⇒ Γ} → ⊤ [ γ ] ≡ ⊤ {Δ}
    ∗⟮⟯  : ∀ {Δ Γ : 𝒞} {γ : Δ ⇒ Γ} → ∗ ⟮ γ ⟯ ≡ ∗ {Δ}
    -- The last one doesn't type check with homogeneous equality:
    -- ∗ ⟮ γ ⟯ : ⊤ [ γ ] but ∗ : ⊤, requiring ⊤[]

    -- Π-structure
    Π     : ∀ {Γ : 𝒞} → (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
    lam   : ∀ {Γ : 𝒞} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
            Tm (Γ ▷ A) B → Tm Γ (Π A B)
    app   : ∀ {Γ : 𝒞} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
            Tm Γ (Π A B) → Tm (Γ ▷ A) B
    Πβ    : ∀ {Γ : 𝒞} {A : Ty Γ} {B : Ty (Γ ▷ A)} {b : Tm (Γ ▷ A) B} →
            app (lam b) ≡ b
    Πη    : ∀ {Γ : 𝒞} {A : Ty Γ} {B : Ty (Γ ▷ A)} {a : Tm Γ (Π A B)} →
            lam (app a) ≡ a
    Π[]   : ∀ {Δ Γ : 𝒞} {A : Ty Γ} {B : Ty (Γ ▷ A)} {γ : Δ ⇒ Γ} →
            (Π A B) [ γ ] ≡ Π (A [ γ ]) (B [ γ ↑ A ])
    lam⟮⟯ : ∀ {Δ Γ : 𝒞} {A : Ty Γ} {B : Ty (Γ ▷ A)} {γ : Δ ⇒ Γ} {b : Tm (Γ ▷ A) B} →
            (lam b) ⟮ γ ⟯ ≡ lam (b ⟮ γ ↑ A ⟯)
    app⟮⟯ : ∀ {Δ Γ : 𝒞} {A : Ty Γ} {B : Ty (Γ ▷ A)} {γ : Δ ⇒ Γ} {a : Tm Γ (Π A B)} →
            (app a) ⟮ γ ↑ A ⟯ ≡ app (subst (Tm Δ) Π[] (a ⟮ γ ⟯))
    -- The penultimate doesn't type check with homogeneous equality:
    -- (lam b) ⟮ γ ⟯ : Tm Δ ((Π A B) [ γ ]) but lam (b ⟮ γ ↑ A ⟯) : Tm Δ (Π (A [ γ ]) (B [ γ ↑ A ])), requiring Π[]
    -- The last one doesn't type check without an explicit coercion:
    -- (app a) ⟮ γ ↑ A ⟯ ≡ app ? needs Tm Δ (Π (A [ γ ]) (B [ γ ↑ A ]))
    -- but a ⟮ γ ⟯ : Tm Δ ((Π A B) [ γ ]), requiring Π[]

    -- 𝒰-structure
    𝒰      : ∀ {Γ : 𝒞} → Ty Γ
    code   : ∀ {Γ : 𝒞} → Ty Γ → Tm Γ 𝒰
    el     : ∀ {Γ : 𝒞} → Tm Γ 𝒰 → Ty Γ
    𝒰β     : ∀ {Γ : 𝒞} {A : Ty Γ} → el (code A) ≡ A
    𝒰η     : ∀ {Γ : 𝒞} {a : Tm Γ 𝒰} → code (el a) ≡ a
    𝒰[]    : ∀ {Δ Γ : 𝒞} {γ : Δ ⇒ Γ} → 𝒰 [ γ ] ≡ 𝒰 {Δ}
    code⟮⟯ : ∀ {Δ Γ : 𝒞} {γ : Δ ⇒ Γ} {A : Ty Γ} →
             (code A) ⟮ γ ⟯ ≡ code (A [ γ ])
    el[]   : ∀ {Δ Γ : 𝒞} {γ : Δ ⇒ Γ} {a : Tm Γ 𝒰} →
             (el a) [ γ ] ≡ el (subst (Tm Δ) 𝒰[] (a ⟮ γ ⟯))
    -- The penultimate doesn't type check with homogeneous equality:
    -- (code A) ⟮ γ ⟯ : Tm Δ (𝒰 [ γ ]) but code (A [ γ ]) : Tm Δ 𝒰, requiring 𝒰[]
    -- The last one doesn't type check without an explicit coercion:
    -- (el a) [ γ ] ≡ el ? needs Tm Δ 𝒰 but a ⟮ γ ⟯ : Tm Δ (𝒰 [ γ ]), requiring 𝒰[]