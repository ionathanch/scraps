{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; module ≡-Reasoning)
  renaming (isPropositional to isProp; sym to _⁻¹; trans to infixr 9 _∘_;
    subst to transport; cong to ap {- ; dcong to apd-})
open ≡-Reasoning
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Function.Base using (_$_)

variable
  ℓ ℓ' : Level
  A X : Set ℓ
  B C : A → Set ℓ
  a b c x y : A

{- Some properties of equality -}

-- dependent ap (should be `dcong` in Properties)
apd : (f : (x : A) → B x) → (p : a ≡ b) → transport B p (f a) ≡ f b
apd _ refl = refl

-- left inverse on the left
p⁻¹∘p≡refl : (p : a ≡ b) → p ⁻¹ ∘ p ≡ refl
p⁻¹∘p≡refl refl = refl

-- right identity on the left
p∘refl≡p : (p : a ≡ b) → p ∘ refl ≡ p
p∘refl≡p refl = refl

-- left identity on the right
q≡refl∘q : (q : a ≡ b) → q ≡ refl ∘ q
q≡refl∘q refl = refl

-- left whisker
infixr 9 _◁_
_◁_ : ∀ {p q : b ≡ c} → (r : a ≡ b) → p ≡ q → r ∘ p ≡ r ∘ q
_ ◁ refl = refl

-- negations are mere propositions up to function extensionality
isProp¬P : isProp (¬ A)
isProp¬P ¬P _ = funext (λ p → ⊥-elim (¬P p))
  where postulate
  funext : ∀ {f g : A → X} → (∀ a → f a ≡ g a) → f ≡ g

{- Lemma 2.9.6
If f ≡ g across p:
             p
  B x → C x ═══ B y → C y
Then ∀ b, f b ≡ g b across p:
             f
        B x ┄──╼ C x
         ┊        ┊
      p  │        │ p
         ╽        ╽
        B y ┄──╼ C y
             g
-}
lem2·9·6 : (p : x ≡ y) → (f : B x → C x) → (g : B y → C y) →
  transport (λ y → B y → C y) p f ≡ g →
  ∀ b → transport C p (f b) ≡ g (transport B p b)
lem2·9·6 refl _ _ refl _ = refl

{- Specialization of lem2·9·6:
Given an identity path p : x ≡ x,
applying f first then transporting across p is equal to
transporting across p first then applying f.
        f x
    B x ┄──╼ C x
     ┊        ┊
  p  │        │ p
     ╽        ╽
    B x ┄──╼ C x
        f x
Note that this can't be proven directly by pattern-matching on p to refl
because that would require axiom K.
-}
lem2·9·6' : ∀ x → (p : x ≡ x) → (f : ∀ x → B x → C x) →
  ∀ b → transport C p (f x b) ≡ f x (transport B p b)
lem2·9·6' x p f = lem2·9·6 p (f x) (f x) (apd f p)

{- Hedberg's theorem (Theorem 7.2.2)
If there is some relation R on elements of X where
* R is a mere relation;
* R is reflexive; and
* R implies equality,
then identities on elements of X are equal to refl.
(Consequently, equalities on elements of X satisfy UIP.)
-}

hedberg : ∀ (R : X → X → Set ℓ) →
  (rel : ∀ {x y} → isProp (R x y)) →
  (ρ : ∀ {x} → R x x) →
  (f : ∀ x y → R x y → x ≡ y) →
  ∀ (x : X) → (p : x ≡ x) → p ≡ refl
hedberg R rel ρ f x p = p∘q≡p→q≡refl _ _ $
  begin f x x ρ ∘ p 
    ≡⟨ q∘p≡p*q p (f x x ρ) ⟩ transport _ p (f x x ρ)
    ≡⟨ lem2·9·6' x p (f x) ρ ⟩ f x x (transport (R x) p ρ)
    ≡⟨ ap (f x x) (rel (transport (R x) p ρ) ρ) ⟩ f x x ρ ∎
  where
  q∘p≡p*q : (p : a ≡ b) → (q : a ≡ a) → q ∘ p ≡ transport (λ y → a ≡ y) p q
  q∘p≡p*q refl q = p∘refl≡p q
  p∘q≡p→q≡refl : (p : a ≡ b) → (q : b ≡ b) → p ∘ q ≡ p → q ≡ refl
  p∘q≡p→q≡refl refl q refl∘q≡refl = (q≡refl∘q q) ∘ refl∘q≡refl

-- If X is discrete (i.e. has decidable equality), then all identities of X are equal to refl.
-- This instantiates Hedberg's theorem with the reflexive mere relation of irrefutability of equality;
-- discreteness implies separability (i.e. has stable equality, i.e. where irrefutability implies inhabitance).
hedbergDiscrete : (∀ (x y : X) → Dec (x ≡ y)) → ∀ (x : X) → (p : x ≡ x) → p ≡ refl
hedbergDiscrete {X = X} dec = hedberg (λ x y → ¬ ¬ x ≡ y) isProp¬P (λ ¬x≡x → ¬x≡x refl) dne
  where
  dne : ∀ (x y : X) → ¬ ¬ x ≡ y → x ≡ y
  dne x y ¬¬x≡y with dec x y
  ... | yes x≡y = x≡y
  ... | no ¬x≡y = ⊥-elim (¬¬x≡y ¬x≡y)

{- Hedberg's theorem (https://www.cs.bham.ac.uk/~mhe/GeneralizedHedberg/html/GeneralizedHedberg.html)
If X is path-collapsible, i.e. for elements x, y of X
there is a constant endofunction x ≡ y → x ≡ y,
then identities on elements of X are equal to refl.
(Consequently, equalities on elements of X satisfy UIP.)
-}

hedberg' : (∀ (x y : X) → Σ[ f ∈ (x ≡ y → x ≡ y) ] ∀ p q → f p ≡ f q) →
  ∀ (x : X) → (p : x ≡ x) → p ≡ refl
hedberg' pathColl x p =
  begin p
  ≡⟨ p≡frefl⁻¹∘fp p ⟩ (f refl)⁻¹ ∘ f p
  ≡⟨ (f refl)⁻¹ ◁ h p refl ⟩ (f refl)⁻¹ ∘ f refl
  ≡⟨ p⁻¹∘p≡refl (f refl) ⟩ refl ∎
  where
  f = λ {y} → proj₁ (pathColl x y)
  h = λ {y} → proj₂ (pathColl x y)
  p≡frefl⁻¹∘fp : (p : x ≡ y) → p ≡ (f refl)⁻¹ ∘ f p
  p≡frefl⁻¹∘fp refl = (p⁻¹∘p≡refl (f refl))⁻¹

-- If X is discrete (i.e. has decidable equality), then all identities of X are equal to refl.
-- This uses the fact that if X is discrete then X is path-collapsible.
-- Curiously, this method does not rely on function extensionality,
-- where it was previously needed to show that irrefutability is a mere relation.
hedbergDiscrete' : (∀ (x y : X) → Dec (x ≡ y)) → ∀ (x : X) → (p : x ≡ x) → p ≡ refl
hedbergDiscrete' {X = X} dec = hedberg' pathColl
  where
  pathColl : ∀ (x y : X) → Σ[ f ∈ (x ≡ y → x ≡ y) ] ∀ p q → f p ≡ f q
  pathColl x y with dec x y
  ... | yes x≡y = (λ _ → x≡y) , (λ _ _ → refl)
  ... | no ¬x≡y = (λ x≡y → ⊥-elim (¬x≡y x≡y)) , (λ p q → ⊥-elim (¬x≡y p))
