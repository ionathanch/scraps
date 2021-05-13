open import Agda.Primitive
open import Function.Base
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality.Core

variable
  ℓ : Level
  A : Set ℓ
  B : A → Set ℓ

infix 30 ↑_
infix 30 ⊔_

{- Preliminaries
  Some helpers while we don't yet have `... with ... in ...`
-}

data Singleton {A : Set ℓ} (a : A) : Set ℓ where
  _with≡_ : (b : A) → a ≡ b → Singleton a

inspect : ∀ {A : Set ℓ} (a : A) → Singleton a
inspect a = a with≡ refl

{- Sizes
  Defining sizes as a generalized form of Brouwer ordinals,
  with an order (see https://arxiv.org/abs/2104.02549)
-}

data Size {ℓ} : Set (lsuc ℓ) where
  ◯  : Size
  ↑_ : Size {ℓ} → Size
  ⊔_ : {A : Set ℓ} → (A → Size {ℓ}) → Size

data _≤_ {ℓ} : Size {ℓ} → Size {ℓ} → Set (lsuc ℓ) where
  ◯≤s   : ∀ {s} → ◯ ≤ s
  ↑s≤↑s : ∀ {r s} → r ≤ s → ↑ r ≤ ↑ s
  s≤s≤s : ∀ {r s t} → r ≤ s → s ≤ t → r ≤ t
  s≤⊔s  : ∀ {A} {s} f (a : A) → s ≤ f a → s ≤ ⊔ f
  ⊔s≤s  : ∀ {A} {s} f → (∀ (a : A) → f a ≤ s) → ⊔ f ≤ s

_<_ : Size {ℓ} → Size {ℓ} → Set (lsuc ℓ)
r < s = ↑ r ≤ s

s≤s : ∀ {s : Size {ℓ}} → s ≤ s
s≤s {_} {◯}   = ◯≤s
s≤s {_} {↑ s} = ↑s≤↑s s≤s
s≤s {_} {⊔ f} = ⊔s≤s f (λ a → s≤⊔s f a s≤s)

s≡s→s≤s : ∀ {r s : Size {ℓ}} → r ≡ s → r ≤ s
s≡s→s≤s refl = s≤s

{- W types
  W∞ is the "infinite" form, where there are no sizes;
  W is the "sized" form, indexed by some Size
-}

data W∞ (A : Set ℓ) (B : A → Set ℓ) : Set (lsuc ℓ) where
  sup∞ : ∀ a → (B a → W∞ A B) → W∞ A B

data W (s : Size {ℓ}) (A : Set ℓ) (B : A → Set ℓ) : Set (lsuc ℓ) where
  sup : ∀ r → r < s → (a : A) → (B a → W r A B) → W s A B

-- We can raise the size of the Ws returned by f up to the limit of
-- *all* the sizes of the Ws returned by f
raise : ∀ {C} → (f : C → ∃[ s ] W s A B) → C → W (⊔ (proj₁ ∘ f)) A B
raise f c with inspect (f c)
... | (s , sup r r<s a b) with≡ p = sup r (s≤s≤s r<s (s≤⊔s (proj₁ ∘ f) c (s≡s→s≤s (cong proj₁ (sym p))))) a b

-- Transforming the "infinite" W∞ form to a size-paired "sized" W form
finW : W∞ {ℓ} A B → ∃[ s ] W s A B
finW (sup∞ a f) =
  let s : Size
      s = ⊔ (proj₁ ∘ finW ∘ f)
  in ↑ s , sup s s≤s a (raise (finW ∘ f))

{- Other -}

-- Transfinite induction:
-- If P holds on every smaller size, then P holds on this size
postulate ind : ∀ (P : Size {ℓ} → Set ℓ) → (∀ s → (∀ r → r < s → P r) → P s) → ∀ s → P s

-- Uh oh! There exists a size provably smaller than *every* size
⊥⊔ : ∀ (s : Size) (f : ⊥ → Size) → ⊔ f ≤ s
⊥⊔ s f = ⊔s≤s f λ ()
