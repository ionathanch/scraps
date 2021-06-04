open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Relation.Nullary using (Dec; yes; no)
open import Function.Base using (_∘_)
open import Data.Product using (∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)

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
raise : ∀ {C} → (f : C → ∃[ s ] W s A B) → C → W (⊔ (fst ∘ f)) A B
raise f c with snd (f c)
... | sup r r<s a b = sup r (s≤s≤s r<s (s≤⊔f (fst ∘ f) c s≤s)) a b

-- Transforming the "infinite" W∞ form to a size-paired "sized" W form
finW : W∞ {ℓ} A B → ∃[ s ] W s A B
finW (sup∞ a f) =
  let s = ⊔ (fst ∘ finW ∘ f)
  in ↑ s , sup s s≤s a (raise (finW ∘ f))

{- Well-founded induction for Sizes via an accessbility predicate based on strict order
  https://nicolaikraus.github.io/docs/html-ordinals/BrouwerTree.Code.Results.html
  https://agda.github.io/agda-stdlib/Induction.WellFounded.html
-}

record Acc (s : Size {ℓ}) : Set (lsuc ℓ) where
  inductive
  constructor acc
  field
    acc< : (∀ {r} → r < s → Acc r)

open Acc

postulate
  -- The law of excluded middle: this must be an axiom.
  lem : ∀ (A : Set ℓ) → Dec A
  -- These two should hold: these are inversion lemmas on ≤.
  ↑s≤↑s⁻¹ : ∀ {r s : Size {ℓ}} → ↑ r ≤ ↑ s → r ≤ s
  s≤⊔f⁻¹ : ∀ {A : Set ℓ} {s} {f : A → Size} → (a : A) → s ≤ ⊔ f → s ≤ f a
  -- This asserts that if A is uninhabited, then the existence of a size smaller than ⊔ f is a contradiction.
  ¬s≤⊔⊥ : ∀ {A : Set ℓ} {s} {f : A → Size} → (A → ⊥) → s ≤ ⊔ f → ⊥

-- A size smaller or equal to an accessible size is still accessible
≤-accessible : ∀ {r s : Size {ℓ}} → r ≤ s → Acc s → Acc r
≤-accessible r≤s (acc p) = acc (λ t<r → p (s≤s≤s t<r r≤s))

-- If a size is bounded by a limit, then it is bounded by some particular size
≤-limit : ∀ {A : Set ℓ} {r : Size {ℓ}} {f : A → Size} → r ≤ ⊔ f → ∃[ a ] r ≤ f a
≤-limit {_} {A} r≤⊔f with lem A
... | yes a = a , s≤⊔f⁻¹ a r≤⊔f
... | no ¬a = ⊥-elim (¬s≤⊔⊥ ¬a r≤⊔f)

-- All sizes are accessible
accessible : ∀ (s : Size {ℓ}) → Acc s
accessible (↑ s) = acc (λ ↑r≤↑s → ≤-accessible (↑s≤↑s⁻¹ ↑r≤↑s) (accessible s))
accessible (⊔ f) = acc accr
  where
  accr : ∀ {r} → r < ⊔ f → Acc r
  accr r<⊔f with ≤-limit r<⊔f
  ... | a , r<fa = (accessible (f a)).acc< r<fa

-- Well-founded induction:
-- If P holds on every smaller size, then P holds on this size
-- Recursion occurs structurally on the accessbility of sizes
wfind : ∀ (P : Size {ℓ} → Set ℓ) → (∀ s → (∀ r → r < s → P r) → P s) → ∀ s → P s
wfind P f s = wfind-acc s (accessible s)
  where
  wfind-acc : ∀ s → Acc s → P s
  wfind-acc s (acc p) = f s (λ r r<s → wfind-acc r (p r<s))
