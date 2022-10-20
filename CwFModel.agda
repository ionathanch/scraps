{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality.Core
open import Agda.Builtin.Equality.Rewrite

infixl 30 _▷_
infixl 40 _[_]
data Ctxt : Set
data _⇒_ : Ctxt → Ctxt → Set
data Ty (Γ : Ctxt) : Set
data Tm : (Γ : Ctxt) → Ty Γ → Set
_[_] : ∀ {Δ Γ} → Ty Γ → (Δ ⇒ Γ) → Ty Δ
_⟮_⟯ : ∀ {Δ Γ} {A : Ty Γ} → Tm Γ A → (γ : Δ ⇒ Γ) → Tm Δ (A [ γ ])
_∘_ : ∀ {Ξ Δ Γ} → (Δ ⇒ Γ) → (Ξ ⇒ Δ) → (Ξ ⇒ Γ)

data Ctxt where
  ∙ : Ctxt
  _▷_ : ∀ Γ → Ty Γ → Ctxt

{-
data Tys (Γ : Ctxt) : Set
splay : ∀ {Γ} → Tys Γ → Ctxt

data Tys Γ where
  [] : Tys Γ
  _∷_ : (As : Tys Γ) → (A : Ty (splay As)) → Tys Γ

splay {Γ} [] = Γ
splay (As ∷ A) = (splay As) ▷ A
-}

data _⇒_ where
  id : ∀ {Γ} → Γ ⇒ Γ
  ⟨⟩ : ∀ {Γ} → Γ ⇒ ∙
  ⟨_,_⟩ : ∀ {Δ Γ} {A : Ty Γ} → (γ : Δ ⇒ Γ) → Tm Δ (A [ γ ]) → Δ ⇒ Γ ▷ A
  -- p : ∀ {Γ} → (As : Tys Γ) → (splay As) ⇒ Γ


data Ty Γ where
  ⊥ : Ty Γ
  --Π : (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ

data Tm where
  --q : ∀ {Γ} {A} → Tm (Γ ▷ A) (A [ p ([] ∷ A) ])
  absurd : ∀ {Γ} {A} → Tm Γ ⊥ → Tm Γ A

-- _↑_ : ∀ {Δ Γ} → (γ : Δ ⇒ Γ) → (A : Ty Γ) → (Δ ▷ A [ γ ] ⇒ Γ ▷ A)
-- γ ↑ A = ⟨ γ ∘ p ([] ∷ A) , q ⟩

⊥ [ γ ] = ⊥
--(Π A B) [ γ ] = Π (A [ γ ]) (B [ γ ↑ A ])

absurd b ⟮ γ ⟯ = absurd (b ⟮ γ ⟯)

[id] : ∀ {Γ} → (A : Ty Γ) → A [ id ] ≡ A
[id] ⊥ = refl

[∘] : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} → (A : Ty Γ) → A [ γ ∘ δ ] ≡ A [ γ ] [ δ ]
[∘] ⊥ = refl

{-# REWRITE [id] [∘] #-}

⟮id⟯ : ∀ {Γ} {A : Ty Γ} → (a : Tm Γ A) → a ⟮ id ⟯ ≡ a
⟮id⟯ (absurd b) = cong absurd (⟮id⟯ b)

⟮∘⟯ : ∀ {Ξ Δ Γ} {γ : Δ ⇒ Γ} {δ : Ξ ⇒ Δ} {A : Ty Γ} → (a : Tm Γ A) → a ⟮ γ ∘ δ ⟯ ≡ a ⟮ γ ⟯ ⟮ δ ⟯
⟮∘⟯ (absurd b) = cong absurd (⟮∘⟯ b)

{-# REWRITE ⟮id⟯ ⟮∘⟯ #-}

id ∘ γ = γ
γ ∘ id = γ
⟨⟩ ∘ γ = ⟨⟩
⟨ γ , a ⟩ ∘ δ = ⟨ γ ∘ δ , a ⟮ δ ⟯ ⟩