open import Data.Empty
open import Data.Unit renaming (tt to TT)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Builtin.Equality renaming (refl to Refl)
open import Function.Base using (_∘_)

{- Preliminaries -}

-- J is for J-eliminator
J : ∀ {A : Set} {x y : A} →
  (P : (y : A) → x ≡ y → Set) →
  P x Refl → (p : x ≡ y) → P y p
J _ d Refl = d

-- K is for Konstant
ᴷ_ : ∀ {A B : Set} → B → (A → B)
ᴷ b = (λ _ → b)

-- U is for Uncurry
ᵁ_ : ∀ {A : Set} {B : A → Set} {C : (a : A) → B a → Set} →
  ((a : A) → (b : B a) → C a b) →
  (p : Σ A B) → C (proj₁ p) (proj₂ p)
ᵁ f = λ p → f (proj₁ p) (proj₂ p)

{- Universe encoding and decoding -}

data U : Set
El : U → Set

data U where
  bot   : U
  top   : U
  pi    : (a : U) → (El a → U) → U
  sigma : (a : U) → (El a → U) → U
  sum   : (a b : U) → U
  eq    : ∀ {a : U} → (x y : El a) → U

El bot = ⊥
El top = ⊤
El (pi a b) = (x : El a) → El (b x)
El (sigma a b) = Σ[ x ∈ El a ] El (b x)
El (sum a b) = El a ⊎ El b
El (eq x y) = x ≡ y

{- Contexts
The representation is a cons list of functions
from context interpretations to encoded universes;
The interpretation is a dependent tuple of types.
The "head" of the context is the most recent entry;
the "tail" of the context is the rest of the entries.
-}

data Ctxt : Set
⟦_⟧ᶜ : Ctxt → Set

infixl 10 _,_
data Ctxt where
  ∙ : Ctxt
  _,_ : (Γ : Ctxt) → (⟦ Γ ⟧ᶜ → U) → Ctxt

cons : (Γ : Ctxt) → (⟦ Γ ⟧ᶜ → U) → Ctxt
cons Γ T = Γ , T
syntax cons Γ (λ γ → T) = Γ % γ , T

⟦ ∙ ⟧ᶜ = ⊤
⟦ Γ , T ⟧ᶜ = Σ[ γ ∈ ⟦ Γ ⟧ᶜ ] El (T γ)

hd = proj₂
tl = proj₁

{- Context membership
The representation is a standard cons list membership type;
The interpretation returns the interpreted type from the interpreted context.
-}

infix 8 _∋_
data _∋_ : (Γ : Ctxt) → (⟦ Γ ⟧ᶜ → U) → Set where
  top : ∀ {Γ T} → Γ , T ∋ T ∘ tl
  pop : ∀ {Γ S T} → Γ ∋ T → Γ , S ∋ T ∘ tl

⟦_⟧³ : ∀ {Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧ᶜ) → El (T γ)
⟦ top ⟧³ ⟨ γ , t ⟩ = t
⟦ pop i ⟧³ ⟨ γ , s ⟩ = ⟦ i ⟧³ γ

{- Typing judgements
The judgement Γ * T represents formation rules:

---------- Bot
Γ ⊢ ⊥ type

---------- Top
Γ ⊢ ⊤ type

Γ ⊢ A type  Γ, A ⊢ B type
------------------------- Pi
Γ ⊢ Π A B type

Γ ⊢ A type  Γ, A ⊢ B type
------------------------- Sigma
Γ ⊢ Σ A B type

Γ ⊢ A type  Γ ⊢ B type
---------------------- Sum
Γ ⊢ A ⊎ B type

Γ ⊢ A type  Γ ⊢ x : A  Γ ⊢ y : A
-------------------------------- Eq
Γ ⊢ x ≡ y type

The judgement Γ ⊢ T represents introduction and elimination forms
as intrinsically well-typed term representations:

A ∈ Γ
-----------
Γ ⊢ var : A

Γ ⊢ A type  Γ ⊢ b : ⊥
---------------------
Γ ⊢ absurd b : A

----------
Γ ⊢ tt : ⊤

Γ, A ⊢ b : B
---------------
Γ ⊢ λ b : Π A B

Γ ⊢ a : A  Γ ⊢ f : Π A B
------------------------
Γ ⊢ f a : B a

Γ ⊢ a : A  Γ, A ⊢ b : B
-----------------------
Γ ⊢ ⟨ a , b ⟩ : Σ A B

Γ ⊢ p : Σ A B
-------------
Γ ⊢ fst p : A

Γ ⊢ p : Σ A B
---------------------
Γ ⊢ snd p : B (fst p)

Γ ⊢ B type  Γ ⊢ a : A
---------------------
Γ ⊢ inl a : A ⊎ B

Γ ⊢ A type  Γ ⊢ b : B
---------------------
Γ ⊢ inr b : A ⊎ B

Γ, A ⊎ B ⊢ P type  Γ ⊢ s : A ⊎ B
Γ, A ⊢ l : P[inl var]  Γ, B ⊢ r : P[inl var]
----------------------------------------------
Γ ⊢ case s l r : P[s]

Γ ⊢ a : A
------------------
Γ ⊢ refl a : a ≡ a

Γ ⊢ x : A  Γ ⊢ y : A
Γ, A, x ≡ var ⊢ P type
Γ ⊢ d : P[x][refl x]
Γ ⊢ p : x ≡ y
----------------------
Γ ⊢ J d p : P[y][p]

The interpretation of a judgement Γ ⊢ T wrt an interpreted context is a term.
-}

infix 8 _*_
infix 8 _⊢_
data _*_ (Γ : Ctxt) : (⟦ Γ ⟧ᶜ → U) → Set
data _⊢_ (Γ : Ctxt) : (⟦ Γ ⟧ᶜ → U) → Set

Type : (Γ : Ctxt) → (⟦ Γ ⟧ᶜ → U) → Set
Type Γ T = Γ * T
syntax Type Γ (λ γ → T) = Γ % γ * T

type : (Γ : Ctxt) → (⟦ Γ ⟧ᶜ → U) → Set
type Γ T = Γ ⊢ T
syntax type Γ (λ γ → T) = Γ % γ ⊢ T

⟦_⟧ : ∀ {Γ T} → Γ ⊢ T → (γ : ⟦ Γ ⟧ᶜ) → El (T γ)

data _*_ Γ where
  Bot   : Γ * ᴷ bot
  Top   : Γ * ᴷ top
  Pi    : ∀ {S T} → Γ * S → Γ , S * T →
          ------------------------------------
          Γ % γ * pi (S γ) (λ s → T ⟨ γ , s ⟩)
  Sigma : ∀ {S T} → Γ * S → Γ , S * T →
          ---------------------------------------
          Γ % γ * sigma (S γ) (λ s → T ⟨ γ , s ⟩)
  Sum   : ∀ {S T} → Γ * S → Γ * T →
          -----------------------
          Γ % γ * sum (S γ) (T γ)
  Eq    : ∀ {T} → Γ * T → (x y : Γ ⊢ T) →
          ------------------------------
          Γ % γ * eq (⟦ x ⟧ γ) (⟦ y ⟧ γ)

data _⊢_ Γ where
  var : ∀ {T} → Γ ∋ T →
        ---------------
        Γ ⊢ T
  absurd : ∀ {T} → Γ * T → Γ ⊢ ᴷ bot →
        ------------------------------
        Γ ⊢ T
  tt  : Γ ⊢ ᴷ top
  lam : ∀ {S} {T : (γ : ⟦ Γ ⟧ᶜ) → El (S γ) → U} →
        (Γ , S) % γ ⊢ T (tl γ) (hd γ) →
        -----------------------------------------
        Γ % γ ⊢ pi (S γ) (T γ)
  app : ∀ {S} {T : (γ : ⟦ Γ ⟧ᶜ) → El (S γ) → U} →
        Γ % γ ⊢ pi (S γ) (T γ) → (s : Γ ⊢ S) →
        -----------------------------------------
        Γ % γ ⊢ T γ (⟦ s ⟧ γ)
  _&_ : ∀ {S} {T : (γ : ⟦ Γ ⟧ᶜ) → El (S γ) → U} →
        (s : Γ ⊢ S) → Γ % γ ⊢ T γ (⟦ s ⟧ γ) →
        -----------------------------------------
        Γ % γ ⊢ sigma (S γ) (T γ)
  fst : ∀ {S} {T : (γ : ⟦ Γ ⟧ᶜ) → El (S γ) → U} →
        Γ % γ ⊢ sigma (S γ) (T γ) →
        -----------------------------------------
        Γ ⊢ S
  snd : ∀ {S : ⟦ Γ ⟧ᶜ → U} →
        ∀ {T : (γ : ⟦ Γ ⟧ᶜ) → El (S γ) → U} →
        (p : Γ % γ ⊢ sigma (S γ) (T γ)) →
        -------------------------------------
        Γ % γ ⊢ T γ (proj₁ (⟦ p ⟧ γ))
  inl : ∀ {S T : ⟦ Γ ⟧ᶜ → U} → Γ * T → Γ ⊢ S →
        --------------------------------------
        Γ % γ ⊢ sum (S γ) (T γ)
  inr : ∀ {S T : ⟦ Γ ⟧ᶜ → U} → Γ * S → Γ ⊢ T →
        --------------------------------------
        Γ % γ ⊢ sum (S γ) (T γ)
  case : ∀ {S T : ⟦ Γ ⟧ᶜ → U} {P} →
        Γ % γ , sum (S γ) (T γ) * ᵁ P →
        (s : Γ % γ ⊢ sum (S γ) (T γ)) →
        (Γ , S) % γ ⊢ P (tl γ) (inj₁ (hd γ)) →
        (Γ , T) % γ ⊢ P (tl γ) (inj₂ (hd γ)) →
        --------------------------------------
        Γ % γ ⊢ P γ (⟦ s ⟧ γ)
  refl : ∀ {T} → (x : Γ ⊢ T) →
        ------------------------------
        Γ % γ ⊢ eq (⟦ x ⟧ γ) (⟦ x ⟧ γ)
  j   : ∀ {T} {x y : Γ ⊢ T} {P} →
        (Γ , T) % γ , eq (⟦ x ⟧ (tl γ)) (hd γ) * ᵁ ᵁ P →
        Γ % γ ⊢ P γ (⟦ x ⟧ γ) Refl →
        (p : Γ % γ ⊢ eq (⟦ x ⟧ γ) (⟦ y ⟧ γ)) →
        ------------------------------------------------
        Γ % γ ⊢ P γ (⟦ y ⟧ γ) (⟦ p ⟧ γ)

⟦ var i ⟧        γ = ⟦ i ⟧³ γ
⟦ tt ⟧           γ = TT
⟦ absurd _ b ⟧   γ = ⊥-elim (⟦ b ⟧ γ)
⟦ lam f ⟧        γ = λ x → ⟦ f ⟧ ⟨ γ , x ⟩
⟦ app f x ⟧      γ = (⟦ f ⟧ γ) (⟦ x ⟧ γ)
⟦ a & b ⟧        γ = ⟨ ⟦ a ⟧ γ , ⟦ b ⟧ γ ⟩
⟦ fst p ⟧        γ = proj₁ (⟦ p ⟧ γ)
⟦ snd p ⟧        γ = proj₂ (⟦ p ⟧ γ)
⟦ inl _ a ⟧      γ = inj₁ (⟦ a ⟧ γ)
⟦ inr _ b ⟧      γ = inj₂ (⟦ b ⟧ γ)
⟦ case _ s l r ⟧ γ with ⟦ s ⟧ γ
... | inj₁ a = ⟦ l ⟧ ⟨ γ , a ⟩
... | inj₂ b = ⟦ r ⟧ ⟨ γ , b ⟩
⟦ refl x ⟧       γ = Refl {x = ⟦ x ⟧ γ}
⟦ j {x = x} {y = y} {P = P} _ d p ⟧ γ =
  J {x = ⟦ x ⟧ γ} {y = ⟦ y ⟧ γ} (λ y p → El (P γ y p)) (⟦ d ⟧ γ) (⟦ p ⟧ γ)
