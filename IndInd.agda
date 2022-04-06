module IndInd where

module CT where
  data Ctxt : Set
  data Type : Ctxt → Set

  data Ctxt where
    · : Ctxt
    _∷_ : ∀ Γ → Type Γ → Ctxt
  
  data Type where
    U : ∀ Γ → Type Γ
    Var : ∀ Γ → Type (Γ ∷ U Γ)
    Pi : ∀ Γ → (A : Type Γ) → Type (Γ ∷ A) → Type Γ

  module Elim
    (C : Ctxt → Set)
    (T : ∀ {Γ} → C Γ → Type Γ → Set)
    (·ᶜ : C ·)
    (_∷ᶜ_ : ∀ {Γ A} → (Γᶜ : C Γ) → T Γᶜ A → C (Γ ∷ A))
    (Uᵀ : ∀ {Γ} → (Γᶜ : C Γ) → T Γᶜ (U Γ))
    (Varᵀ : ∀ {Γ} → (Γᶜ : C Γ) → T (Γᶜ ∷ᶜ Uᵀ Γᶜ) (Var Γ))
    (Piᵀ : ∀ {Γ A} {B : Type (Γ ∷ A)} → (Γᶜ : C Γ) → (Aᵀ : T Γᶜ A) → T (Γᶜ ∷ᶜ Aᵀ) B → T Γᶜ (Pi Γ A B))
    where

    elim-Ctxt : ∀ Γ → C Γ
    elim-Type : ∀ {Γ} → (A : Type Γ) → T (elim-Ctxt Γ) A

    elim-Ctxt · = ·ᶜ
    elim-Ctxt (Γ ∷ A) = (elim-Ctxt Γ) ∷ᶜ (elim-Type A)

    elim-Type (U Γ) = Uᵀ (elim-Ctxt Γ)
    elim-Type (Var Γ) = Varᵀ (elim-Ctxt Γ)
    elim-Type (Pi Γ A B) = Piᵀ (elim-Ctxt Γ) (elim-Type A) (elim-Type B)

module CT' where
  data Ctxt' : Set
  data Type' : Set

  data Ctxt' where
    ·' : Ctxt'
    _∷'_ : Ctxt' → Type' → Ctxt'
  
  data Type' where
    U' : Ctxt' → Type'
    Var' : Ctxt' → Type'
    Pi' : Ctxt' → Type' → Type' → Type'

  data Ctxt-wf : Ctxt' → Set
  data Type-wf : Ctxt' → Type' → Set

  data Ctxt-wf where
    ·-wf : Ctxt-wf ·'
    ∷-wf : ∀ {Γ} {A} → Ctxt-wf Γ → Type-wf Γ A → Ctxt-wf (Γ ∷' A)
  
  data Type-wf where
    U-wf : ∀ {Γ} → Ctxt-wf Γ → Type-wf Γ (U' Γ)
    Var-wf : ∀ {Γ} → Ctxt-wf Γ → Type-wf (Γ ∷' U' Γ) (Var' Γ)
    Pi-wf : ∀ {Γ} {A B} → Ctxt-wf Γ → Type-wf Γ A → Type-wf (Γ ∷' A) B → Type-wf Γ (Pi' Γ A B)

  open import Data.Product

  Ctxt : Set
  Ctxt = Σ[ Γ ∈ Ctxt' ] Ctxt-wf Γ

  Type : Ctxt → Set
  Type (Γ , _) = Σ[ A ∈ Type' ] Type-wf Γ A
  -- TODO: This lack of usage of (Ctxt-wf Γ) (_ above) is suspicious...

  · : Ctxt
  · = ·' , ·-wf

  _∷_ : ∀ Γ → Type Γ → Ctxt
  (Γ , Γ-wf) ∷ (A , A-wf) = Γ ∷' A , ∷-wf Γ-wf A-wf

  U : ∀ Γ → Type Γ
  U (Γ , Γ-wf) = U' Γ , U-wf Γ-wf

  Var : ∀ Γ → Type (Γ ∷ U Γ)
  Var (Γ , Γ-wf) = Var' Γ , Var-wf Γ-wf

  Pi : ∀ Γ → (A : Type Γ) → Type (Γ ∷ A) → Type Γ
  Pi (Γ , Γ-wf) (A , A-wf) (B , B-wf) = Pi' Γ A B , Pi-wf Γ-wf A-wf B-wf

  module Elim
    (C : Ctxt → Set)
    (T : ∀ {Γ} → C Γ → Type Γ → Set)
    (·ᶜ : C ·)
    (_∷ᶜ_ : ∀ {Γ A} → (Γᶜ : C Γ) → T Γᶜ A → C (Γ ∷ A))
    (Uᵀ : ∀ {Γ} → (Γᶜ : C Γ) → T Γᶜ (U Γ))
    (Varᵀ : ∀ {Γ} → (Γᶜ : C Γ) → T (Γᶜ ∷ᶜ Uᵀ Γᶜ) (Var Γ))
    (Piᵀ : ∀ {Γ A} {B : Type (Γ ∷ A)} → (Γᶜ : C Γ) → (Aᵀ : T Γᶜ A) → T (Γᶜ ∷ᶜ Aᵀ) B → T Γᶜ (Pi Γ A B))
    where

    elim-Ctxt : ∀ Γ → C Γ
    elim-Type : ∀ {Γ} → (A : Type Γ) → T (elim-Ctxt Γ) A

    elim-Ctxt (·' , ·-wf) = ·ᶜ
    elim-Ctxt (Γ ∷' A , ∷-wf Γ-wf A-wf) = (elim-Ctxt (Γ , Γ-wf)) ∷ᶜ (elim-Type (A , A-wf))

    elim-Type (U' Γ , U-wf Γ-wf) = {!  !}
    elim-Type (Var' Γ , Var-wf Γ-wf) = {!   !}
    elim-Type (Pi' Γ A B , Pi-wf Γ-wf A-wf B-wf) = {!   !}
