{-# OPTIONS --prop #-}

open import Agda.Primitive

variable
  ℓ : Level
  A B : Set ℓ

infix 10 _≡_
data _≡_ {A : Set ℓ} (a : A) : A → Prop ℓ where
  refl : a ≡ a

postulate
  transp : ∀ {a b : A} (P : ∀ x → a ≡ x → Prop ℓ) → P a refl → ∀ p → P b p
  subst : ∀ {a b} (P : A → Prop ℓ) → a ≡ b → P a → P b
  cast : A ≡ B → A → B
  castrefl : ∀ (a : A) (p : A ≡ A) → a ≡ cast p a
-- normally can be proven by pattern-matching
-- transp P d refl = d
-- subst P refl pa = pa
-- cast refl a = a
-- castrefl a refl = refl

-- transport can be proven from only subst
-- normally (λ _ → d) wouldn't be a proof of ∀ (p : a ≡ a) → P a p,
-- but proof irrelevance of equality easily provides p ≡ refl definitionally
transport : ∀ {A : Set ℓ} {a b} (P : ∀ (x : A) → a ≡ x → Prop ℓ) → P a refl → ∀ p → P b p
transport {ℓ} {A} {a} {b} P d p = subst (λ x → ∀ (p : a ≡ x) → P x p) p (λ _ → d) p

-- equality is a congruent equivalence relation

-- symmetry/inverse
infix 30 _⁻¹
_⁻¹ : ∀ {a b : A} → a ≡ b → b ≡ a
_⁻¹ {a = a} {b = b} p = subst (λ x → x ≡ a) p refl

-- transitivity/composition
infix 20 _·_
_·_ : ∀ {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_·_ {a = a} {b = b} {c = c} p q = subst (λ x → a ≡ x) q p

-- congruence/ap
ap : ∀ {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
ap {a = a} {b = b} f p = subst (λ x → f a ≡ f x) p refl

-- equality is a groupoid wrt inverse and composition
-- these don't type check because _≡_ isn't polymorphic over relevance,
-- but they hold trivially because they're proof irrelevant and well typed
-- they can also be proven using transp but why would you do that?
-- associativity : ∀ {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) → p · (q · r) ≡ (p · q) · r
-- identity-left : ∀ {a b : A} (p : a ≡ b) → refl · p ≡ p
-- identity-right : ∀ {a b : A} (p : a ≡ b) → p · refl ≡ p
-- inverse-left : ∀ {a b : A} (p : a ≡ b) → p ⁻¹ · p ≡ refl
-- inverse-right : ∀ {a b : A} (p : a ≡ b) → p · p ⁻¹ ≡ refl

-- J eliminator (proof-relevant transport) for MLTT identity type
-- this gets stuck on J P d refl if P is neutral bc cast matches on P a
J : ∀ {a b : A} (P : ∀ x → a ≡ x → Set ℓ) → P a refl → ∀ p → P b p
J {a = a} {b = b} P d p = cast (transp (λ x q → P a refl ≡ P x q) refl p) d

-- likewise, proof-relevant substitution suffers from the same problem:
-- it'll get stuck on substitution P refl pa if P is neutral
substitution : ∀ {a b} (P : A → Set ℓ) → a ≡ b → P a → P b
substitution {a = a} P p pa = cast (transp (λ x _ → P a ≡ P x) refl p) pa

-- bonus: contractibility of singletons from subst,
-- using the same proof irrelevance trick as for transport

data DPair (A : Set ℓ) (B : A → Prop ℓ) : Set ℓ where
  dpair : ∀ a → B a → DPair A B

syntax DPair A (λ x → B) = Σ[ x ∈ A ] B
syntax dpair a b = ⟨ a , b ⟩

contrasing : ∀ {a} (p : Σ[ x ∈ A ] (a ≡ x)) → ⟨ a , refl ⟩ ≡ p
contrasing {a = a} ⟨ b , p ⟩ = subst (λ x → ∀ (p : a ≡ x) → ⟨ a , refl ⟩ ≡ ⟨ x , p ⟩) p (λ _ → refl) p