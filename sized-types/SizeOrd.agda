open import Agda.Primitive
open import Function.Base
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality.Core

variable
  ℓ : Level
  A : Set ℓ
  B : A → Set ℓ

{- Sizes
  Defining sizes as a generalized form of Brouwer ordinals,
  with an order (see https://arxiv.org/abs/2104.02549)
-}

infix 30 ↑_
infix 30 ⊔_

data Size {ℓ} : Set (lsuc ℓ) where
  ↑_ : Size {ℓ} → Size
  ⊔_ : {A : Set ℓ} → (A → Size {ℓ}) → Size

data _≤_ {ℓ} : Size {ℓ} → Size {ℓ} → Set (lsuc ℓ) where
  ↑s≤↑s : ∀ {r s} → r ≤ s → ↑ r ≤ ↑ s
  s≤s≤s : ∀ {r s t} → r ≤ s → s ≤ t → r ≤ t
  s≤⊔f  : ∀ {A} {s} f (a : A) → s ≤ f a → s ≤ ⊔ f
  ⊔f≤s  : ∀ {A} {s} f → (∀ (a : A) → f a ≤ s) → ⊔ f ≤ s

-- A possible definition of the smallest size
◯ : Size
◯ = ⊔ ⊥-elim

◯≤s : ∀ {s : Size} → ◯ ≤ s
◯≤s = ⊔f≤s ⊥-elim λ ()

-- Reflexivity of ≤
s≤s : ∀ {s : Size {ℓ}} → s ≤ s
s≤s {_} {↑ s} = ↑s≤↑s s≤s
s≤s {_} {⊔ f} = ⊔f≤s f (λ a → s≤⊔f f a s≤s)

-- Strict order
_<_ : Size {ℓ} → Size {ℓ} → Set (lsuc ℓ)
r < s = ↑ r ≤ s

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
raise f c with proj₂ (f c)
... | sup r r<s a b = sup r (s≤s≤s r<s (s≤⊔f (proj₁ ∘ f) c s≤s)) a b

-- Transforming the "infinite" W∞ form to a size-paired "sized" W form
finW : W∞ {ℓ} A B → ∃[ s ] W s A B
finW (sup∞ a f) =
  let s = ⊔ (proj₁ ∘ finW ∘ f)
  in ↑ s , sup s s≤s a (raise (finW ∘ f))

{- Well-founded induction for Sizes
  https://nicolaikraus.github.io/docs/html-ordinals/BrouwerTree.Code.Results.html
  https://agda.github.io/agda-stdlib/Induction.WellFounded.html
-}

record Acc (s : Size {ℓ}) : Set (lsuc ℓ) where
  inductive
  constructor acc
  field
    rs : (∀ {r} → r < s → Acc r)

open Acc

≤-accessible : ∀ {r s : Size {ℓ}} → r ≤ s → Acc s → Acc r
≤-accessible r≤s (acc f) = acc (λ t<r → f (s≤s≤s t<r r≤s))

postulate
  ↑s≤↑s⁻¹ : ∀ {r s : Size {ℓ}} → ↑ r ≤ ↑ s → r ≤ s
  s≤⊔f⁻¹ : ∀ {A : Set ℓ} {s : Size {ℓ}} {f : A → Size} → s ≤ ⊔ f → ∃[ a ] s ≤ f a

accessible : ∀ (s : Size {ℓ}) → Acc s
accessible (↑ s) = acc (λ ↑r≤↑s → ≤-accessible (↑s≤↑s⁻¹ ↑r≤↑s) (accessible s))
accessible (⊔ f) = acc accr
  where
  accr : ∀ {r} → r < ⊔ f → Acc r
  accr r<⊔f with s≤⊔f⁻¹ r<⊔f
  ... | a , r<fa = rs (accessible (f a)) r<fa

-- Well-founded induction:
-- If P holds on every smaller size, then P holds on this size
postulate wfind : ∀ (P : Size {ℓ} → Set ℓ) → (∀ s → (∀ r → r < s → P r) → P s) → ∀ s → P s
