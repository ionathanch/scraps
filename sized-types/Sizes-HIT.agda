{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  ℓ ℓ' : Level
  A : Set ℓ
  B : Set ℓ'
  x y z : A

sym : x ≡ y → y ≡ x
sym refl = refl

_∙_ : x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

leftId : (p : x ≡ y) → refl ∙ p ≡ p
leftId refl = refl

rightId : (p : x ≡ y) → p ∙ refl ≡ p
rightId refl = refl

transport : (P : A → Set ℓ') → x ≡ y → P x → P y
transport _ refl px = px

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap _ refl = refl

apd : (P : A → Set ℓ') → (f : (a : A) → P a) → (p : x ≡ y) → transport P p (f x) ≡ f y
apd _ _ refl = refl

postulate
  Size : Set
  base : Size
  next : Size → Size
  inf : Size
  lim : next inf ≡ inf

postulate
  elim : (P : Size → Set ℓ) →
    (pb : P base) →
    (pn : (s : Size) → P s → P (next s)) →
    (pi : P inf) →
    -- (elim P pb pn pi pl (next inf)) = (elim P pb pn pi pl inf)
    (pl : transport P lim (pn inf pi) ≡ pi) →
    (s : Size) → P s
  elim-base : (P : Size → Set ℓ) →
    (pb : P base) →
    (pn : (s : Size) → P s → P (next s)) →
    (pi : P inf) →
    (pl : transport P lim (pn inf pi) ≡ pi) →
    elim P pb pn pi pl base ≡ pb
  elim-next : (P : Size → Set ℓ) →
    (pb : P base) →
    (pn : (s : Size) → P s → P (next s)) →
    (pi : P inf) →
    (pl : transport P lim (pn inf pi) ≡ pi) →
    (s : Size) →
    elim P pb pn pi pl (next s) ≡ pn s (elim P pb pn pi pl s)
  elim-inf : (P : Size → Set ℓ) →
    (pb : P base) →
    (pn : (s : Size) → P s → P (next s)) →
    (pi : P inf) →
    (pl : transport P lim (pn inf pi) ≡ pi) →
    elim P pb pn pi pl inf ≡ pi

{-# REWRITE elim-base elim-next elim-inf #-}

postulate
  elim-lim : (P : Size → Set ℓ) →
    (pb : P base) →
    (pn : (s : Size) → P s → P (next s)) →
    (pi : P inf) →
    (pl : transport P lim (pn inf pi) ≡ pi) →
    apd P (elim P pb pn pi pl) lim ≡ pl

{-# REWRITE elim-lim #-}

-- postulate lim-refl : transport (λ s → s ≡ inf) lim lim ≡ refl

absurd : ∀ {A s} → base ≡ next s → A
absurd {A} p =
  let discr : Size → Set
      discr = elim (λ _ → Set) Size (λ _ _ → A) A (apd (λ _ → Set) (λ _ → A) lim)
  in transport discr p base

inj : ∀ {s t} → next s ≡ next t → s ≡ t
inj {s} {t} p =
  let pred : Size → Size
      pred = elim (λ _ → Size) base (λ s _ → s) inf (apd (λ _ → Size) (λ s → inf) lim)
  in ap pred p

data Nat : Size → Set where
  zero : (s : Size) → Nat (next s)
  succ : (s : Size) → Nat s → Nat (next s)

prev : (P : Size → Set ℓ') → P (next inf) → P inf
prev P pni = transport P lim pni

double' : ∀ s → Nat s → Nat inf
double' _ (zero _) = prev Nat (zero inf)
double' _ (succ s n) = prev Nat (succ inf (prev Nat (succ inf (double' s n))))

-- pn inf pi ≡ pi
-- zero: zero = ?pi
-- next: succ _ (succ _ ?pi) = ?pi
{-

-}
double : ∀ s → Nat s → Nat inf
double = elim (λ s → Nat s → Nat inf) {!   !} {!   !} {!   !} {!   !}
