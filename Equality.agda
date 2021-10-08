{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality renaming (refl to Refl)
open import Agda.Builtin.Equality.Rewrite
open import Data.Product

variable
  ℓ ℓ' : Level

postulate
  {- Formation and introduction rules for equality. -}
  _≅_ : ∀ {A : Set ℓ} → A → A → Set ℓ
  refl : ∀ {A : Set ℓ} → (a : A) → a ≅ a

  {- Eliminators:
    Coercion: If types A and B are provably equal then a proof of A is a proof of B;
    Congruence: If a and b are provably equal then applying f to both sides is also equal;
    Contractibility of singletons: If every inhabitant a : A is provably equal to some b,
      then together they are equal to (a, refl a).
  -}
  coe : ∀ {A B : Set ℓ} → (p : A ≅ B) → A → B
  cong : ∀ {A : Set ℓ} {B : Set ℓ'} {a b : A} → (f : A → B) → (p : a ≅ b) → f a ≅ f b
  cos : ∀ {A : Set ℓ} {a : A} → (p : Σ[ b ∈ A ] a ≅ b) → (a , refl a) ≅ p

  {- Reduction rules for eliminators implemented as rewrite rules in Agda. -}
  elim-coe : ∀ {A : Set ℓ} → {p : A ≅ A} → {a : A} → coe p a ≡ a
  elim-cong : ∀ {A : Set ℓ} {B : Set ℓ'} {a : A} → {f : A → B} → cong f (refl a) ≡ refl (f a)
  elim-cos : ∀ {A : Set ℓ} {a : A} → cos (a , refl a) ≅ refl (a , refl a)

  {- 
    Coercion above satisfies regularity, so it reduces on loop paths that aren't necessarily refl;
    we could instead have congruence satisfy regularity, and still be able to recover the J eliminator.
  -}
  -- elim-coe : ∀ {A : Set ℓ} → {a : A} → coe (refl A) a ≡ a
  -- elim-cong : ∀ {A : Set ℓ} {B : Set ℓ'} {a : A} → {f : A → B} → {p : a ≅ a} → cong f p ≡ refl (f a)

-- Interestingly, c.o.s. doesn't need to definitionally reduce to recover J, nor does congruence when coercion does.
-- On the other hand, only congruence reducing doesn't do anything since coe is on the outside in subst.
-- Best to still rewrite them both for canonicity of closed proofs of equality though.
{-# REWRITE elim-coe #-}
-- {-# elim-cong elim-cos #-}

{- Now we can implement substitution and the J eliminator. -}

subst : ∀ {A : Set ℓ} {a b : A} → (P : A → Set ℓ') → (p : a ≅ b) → P a → P b
subst P p = coe (cong P p)

elim-subst : ∀ {A : Set ℓ} {a : A} {P : A → Set ℓ'} → {pa : P a} → subst P (refl a) pa ≡ pa
elim-subst = Refl

reg-subst : ∀ {A : Set ℓ} {a : A} {P : A → Set ℓ'} → {p : a ≅ a} → {pa : P a} → subst P p pa ≡ pa
reg-subst = Refl

{-
  Given p : a ≅ b, we want to show that if P a (refl a), then P b p.
  By substitution over p, we have that if ∀ q, P a q, then ∀ q, P b q.
  By c.o.s., ∀ q, (a, refl a) ≅ (a, q),
  and by substitution over that path, if P a (refl a), then P a q,
  so the antecedent holds by applying the proof of P a (refl a).
  Finally, we apply p to the consequent.
-}
J : ∀ {A : Set ℓ} {a b : A} → (P : ∀ (y : A) → a ≅ y → Set ℓ') → P a (refl a) → (p : a ≅ b) → P b p
J {a = a} P d p = subst (λ y → (q : a ≅ y) → P y q) p e p
  where
  e : ∀ (p : a ≅ a) → P a p
  e p = subst (λ yp → P (proj₁ yp) (proj₂ yp)) (cos (a , p)) d

elim-J : ∀ {A : Set ℓ} {a : A} → {P : ∀ (y : A) → a ≅ y → Set ℓ'} → {d : P a (refl a)} → J P d (refl a) ≡ d
elim-J = Refl

{- Equality is an equivalence, satisfying symmetry and transitivity. -}

sym : ∀ {A : Set ℓ} {a b : A} → (p : a ≅ b) → b ≅ a
sym {a = a} p = subst (λ y → y ≅ a) p (refl a)

trans : ∀ {A : Set ℓ} {a b c : A} → (p : a ≅ b) → (q : b ≅ c) → a ≅ c
trans {a = a} p q = subst (λ y → a ≅ y) q p

{-
  Proving that all proofs of a ≅ a are equal to refl a by projecting out both sides of c.o.s. doesn't work,
  since congruence expects a nondependent function while the second projection depends on the first;
  it must be postulated.
-}
-- uip : ∀ {A : Set ℓ} {a : A} → (p : a ≅ a) → refl a ≅ p
-- uip {a = a} p = cong proj₂ (cos (a , p))

postulate
  uip : ∀ {A : Set ℓ} {a : A} → (p : a ≅ a) → refl a ≅ p
  elim-uip : ∀ {A : Set ℓ} {a : A} → uip (refl a) ≡ refl (refl a)

{-# REWRITE elim-uip #-}

K : ∀ {A : Set ℓ} {a : A} → (P : a ≅ a → Set ℓ') → P (refl a) → (p : a ≅ a) → P p
K P d p = subst P (uip p) d

elim-K : ∀ {A : Set ℓ} {a : A} → {P : a ≅ a → Set ℓ'} → {d : P (refl a)} → K P d (refl a) ≡ d
elim-K = Refl
