--open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.HeterogeneousEquality
  renaming (_≅_ to _≡_; [_] to reveal)

record CwF : Set₁ where
  infixl 30 _▷_
  field
    -- Category with terminal element
    𝒞   : Set
    _⇒_ : 𝒞 → 𝒞 → Set
    id  : ∀ {Γ} → Γ ⇒ Γ
    _∘_ : ∀ {Ξ Δ Γ} → (Δ ⇒ Γ) → (Ξ ⇒ Δ) → (Ξ ⇒ Γ)
    ∙   : 𝒞
    ⟨⟩  : ∀ {Γ} → Γ ⇒ ∙

    -- Category laws and terminality
    assoc : ∀ {Θ Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {ε : Θ ⇒ Ξ} →
            (γ ∘ δ) ∘ ε ≡ γ ∘ (δ ∘ ε)
    idl : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → id ∘ γ ≡ γ
    idr : ∀ {Δ Γ} {γ : Δ ⇒ Γ} → γ ∘ id ≡ γ
    ⟨⟩η : ∀ {Γ} {γ : Γ ⇒ ∙} → γ ≡ ⟨⟩ {Γ}

    -- Type functor and functor laws
    Ty : 𝒞 → Set
    _[_] : ∀ {Δ Γ} → Ty Γ → (Δ ⇒ Γ) → Ty Δ
    [id] : ∀ {Γ} {A : Ty Γ} → A [ id ] ≡ A
    [∘]  : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} →
           A [ γ ∘ δ ] ≡ A [ γ ] [ δ ]

    -- Term functor and functor laws
    Tm   : ∀ Γ → Ty Γ → Set
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
    pβ   : ∀ {Δ Γ} {A : Ty Γ} {γ : Δ ⇒ Γ} {a : Tm Δ (A [ γ ])} → p ∘ ⟨ γ , a ⟩ ≡ γ
    qβ   : ∀ {Δ Γ} {A : Ty Γ} {γ : Δ ⇒ Γ} {a : Tm Δ (A [ γ ])} → q ⟮ ⟨ γ , a ⟩ ⟯ ≡ a
    ⟨pq⟩ : ∀ {Γ} {A : Ty Γ} → ⟨ p {Γ} {A} , q {Γ} {A} ⟩ ≡ id {Γ ▷ A}
    ⟨⟩∘  : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} {a : Tm Δ (A [ γ ])} →
           ⟨ γ , a ⟩ ∘ δ ≡ ⟨ γ ∘ δ , subst (Tm Ξ) (sym [∘]) (a ⟮ δ ⟯) ⟩
    -- The second doesn't type check with homogeneous equality:
    -- q ⟮ ⟨ γ , a ⟩ ⟯ : Tm Δ (A [ p ] [ ⟨ γ , a ⟩ ]) but a : Tm Δ (A [ γ ]), requiring [∘] and pβ
    -- The fourth doesn't type check without an explicit coercion:
    -- ⟨ γ ∘ δ , ? ⟩ needs Tm Ξ (A [ γ ∘ δ ]) but a ⟮ δ ⟯ : Tm Ξ (A [ γ ] [ δ ]), requiring [∘]