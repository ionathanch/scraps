{-# OPTIONS --rewriting #-}

open import Data.Empty
open import Data.Product
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality.Core

{-------------------------------------------------------------
  This model is modelled after Conor McBride's
    Outrageous but Meaningful Coincidences (2010),
  https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf.
  It wasn't designed for modelling via CwFs,
  but it fits and I think is more nicely structured.

  Some assumptions:
  * We have a well-founded set of levels,
    i.e. with a strict transitive order
    s.t. all levels are accessible.
  * Function extensionality.
  From funext we can show that accessibility predicates
  are mere propositions (all propositionally equal),
  and for convenience mere propness computes to refl
  on definitionally equal proofs of accessibility.
-------------------------------------------------------------}

module StraTT (Level : Set)
             (_<_ : Level → Level → Set)
             (trans< : ∀ {i j k} → i < j → j < k → i < k) where

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl A = A

record Acc (k : Level) : Set where
  pattern
  inductive
  constructor acc<
  field acc : ∀ j → j < k → Acc j
open Acc

data _≤_ j k : Set where
  lt : j < k → j ≤ k
  eq : j ≡ k → j ≤ k

postulate
  funext' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    (f g : ∀ {x} → B x) → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    (f g : ∀ x → B x) → (∀ x → f x ≡ g x) → f ≡ g

funeq : ∀ {A₁ A₂ : Set} {B : A₂ → Set} (p : A₁ ≡ A₂) →
  ((a : A₂) → B a) ≡ ((a : A₁) → B (coe p a))
funeq refl = refl

accProp : ∀ {k} (p q : Acc k) → p ≡ q
accProp (acc< f) (acc< g) = cong acc< (funext _ _ (λ j → funext _ _ (λ j<k → accProp (f j j<k) (g j j<k))))

accPropRefl : ∀ {k} (p : Acc k) → accProp p p ≡ refl
accPropRefl p with accProp p p
... | refl = refl

{-# REWRITE accPropRefl #-}

{-----------------------------------------------------------
  A universe of codes U' at level k, and
  an interpretation el' of codes into Agda types,
  parametrized over U, el at strictly smaller levels.
  U<, el< then instantiate the parameters of U', el'
  with themselves inductively over accessibility.
-----------------------------------------------------------}

data U' k (U< : ∀ j → j < k → Set) (el< : ∀ j (j<k : j < k) → U< j j<k → Set) : Set where
  Û : ∀ j → j ≤ k → U' k U< el<
  ⊥̂ : U' k U< el<
  →̂ : U' k U< el< → U' k U< el< → U' k U< el<
  Π̂ : ∀ j → (j<k : j < k) → (A : U< j j<k) → (el< j j<k A → U' k U< el<) → U' k U< el<

el' : ∀ k (U< : ∀ j → j < k → Set) (el< : ∀ j (j<k : j < k) → U< j j<k → Set) → U' k U< el< → Set
el' k U< el< (Û k (eq refl)) = U' k U< el<
el' k U< el< (Û j (lt j<k))  = U' j (λ i i<j → U< i (trans< i<j j<k)) (λ i i<j → el< i (trans< i<j j<k))
el' k U< el< ⊥̂  = ⊥
el' k U< el< (→̂ A B) = el' k U< el< A → el' k U< el< B
el' k U< el< (Π̂ j j<k A B) = (a : el< j j<k A) → el' k U< el< (B a)

U<  : ∀ {k} → Acc k → ∀ j → j < k → Set
el< : ∀ {k} (p : Acc k) j (j<k : j < k) → U< p j j<k → Set

U<  (acc< f) j j<k = U'  j (U< (f j j<k)) (el< (f j j<k))
el< (acc< f) j j<k = el' j (U< (f j j<k)) (el< (f j j<k))

{-----------------------------------------------------------
  Universes are cumulative:
  a code in universe j can be lifted into a universe k > j
  such that the interpretation is preserved.
  We prove this in general for U' and el' over arbitrary
  proofs of accessibility of levels,
  then instantiate to the proof by well-foundedness.
  The parameters of U', el' involve accessibility proofs,
  requiring many aps on and coercions across equalities,
  especially since funext and accProp don't compute away.
-----------------------------------------------------------}

el'≡1 : ∀ {k} {acc₁ acc₂ : Acc k} (A : U' k (U< acc₁) (el< acc₁)) →
  let A' = subst (λ a → U' k (U< a) (el< a)) (accProp acc₁ acc₂) A
  in el' k (U< acc₂) (el< acc₂) A' ≡ el' k (U< acc₁) (el< acc₁) A
el'≡1 {k} {acc₁} {acc₂} A =
  cong (λ a → el' k (U< a) (el< a)
                  (subst (λ a → U' k (U< a) (el< a))
                         (accProp acc₁ a) A))
       (accProp acc₂ acc₁)

el'→1 : ∀ {k} {acc₁ acc₂ : Acc k} (A : U' k (U< acc₁) (el< acc₁)) →
  let A' = subst (λ a → U' k (U< a) (el< a)) (accProp acc₁ acc₂) A
  in el' k (U< acc₂) (el< acc₂) A' → el' k (U< acc₁) (el< acc₁) A
el'→1 A = coe (el'≡1 A)

lift' : ∀ {j k} (accj : Acc j) (acck : Acc k) → j < k → U' j (U< accj) (el< accj) → U' k (U< acck) (el< acck)
lift' _ _ j<k (Û j (eq refl)) = Û j (lt j<k)
lift' _ _ j<k (Û i (lt i<j)) = Û i (lt (trans< i<j j<k))
lift' _ _ _ ⊥̂  = ⊥̂
lift' accj acck j<k (→̂  A B) = →̂  (lift' accj acck j<k A) (lift' accj acck j<k B)
lift' {j} {k} (acc< f) (acc< g) j<k (Π̂ i i<j A B) =
  Π̂ i (trans< i<j j<k) _ (λ a → lift' (acc< f) (acc< g) j<k (B (el'→1 {i} {f i i<j} {g i (trans< i<j j<k)} A a)))

U'≡1 : ∀ {k} (f g : ∀ j → j < k → Acc j) →
  U' k (U< (acc< f)) (el< (acc< f)) ≡ U' k (U< (acc< g)) (el< (acc< g))
U'≡1 {k} f g =
  cong (λ fg → U' k (U< (acc< fg)) (el< (acc< fg)))
        (funext _ _ (λ j → funext _ _ (λ j<k → accProp (f j j<k) (g j j<k))))

el'≡ : ∀ {j k} (accj : Acc j) (acck : Acc k) (j<k : j < k) (u : U' j (U< accj) (el< accj)) →
  el' j (U< accj) (el< accj) u ≡ el' k (U< acck) (el< acck) (lift' accj acck j<k u)
el'≡ (acc< f) (acc< g) j<k (Û j (eq refl)) =
  U'≡1 f (λ i i<j → g i (trans< i<j j<k))
el'≡ (acc< f) (acc< g) j<k (Û i (lt i<j)) =
  U'≡1 (λ h h<i → f h (trans< h<i i<j))
       (λ h h<i → g h (trans< h<i (trans< i<j j<k)))
el'≡ _ _ _ ⊥̂  = refl
el'≡ accj acck j<k (→̂  A B)
  rewrite el'≡ accj acck j<k A
  rewrite el'≡ accj acck j<k B = refl
el'≡ {j} {k} (acc< f) (acc< g) j<k (Π̂ i i<j A B) = trans p q where
  p : (∀ a → el' j _ _ (B a)) ≡ (∀ a → el' k _ _ (lift' _ _ j<k (B a)))
  p = cong (λ f → ∀ a → f a) (funext _ _ (λ a → el'≡ _ _ j<k (B a)))
  q : (∀ a → el' k _ _ (lift' _ _ j<k (B a))) ≡
      (∀ a → el' k _ _ (lift' _ _ j<k (B (el'→1 A a))))
  q = funeq (el'≡1 A)

module _ (wf : ∀ k → Acc k) where

  {-----------------------------------------------------------
    Universes, their interpretations, and cumulativity,
    instantiated over well-foundedness of levels.
  -----------------------------------------------------------}

  U : ∀ k → Set
  U k = U' k (U< (wf k)) (el< (wf k))

  el : ∀ k → U k → Set
  el k = el' k (U< (wf k)) (el< (wf k))

  lift : ∀ {j k} → j < k → U j → U k
  lift = lift' (wf _) (wf _)

  el≡ : ∀ {j k} → (j<k : j < k) → ∀ u → el j u ≡ el k (lift j<k u)
  el≡ = el'≡ (wf _) (wf _)

  {-----------------------------------------------------------
    Inductively-defined contexts and their interpretations
    as nested dependent pairs, or "dependent lists".
    The types of semantic types and terms Ty, Tm are defined
    mutually but they don't have to be; they can come after.
  -----------------------------------------------------------}
  
  data C : Set
  em : C → Set

  Ty : Level → C → Set
  Ty k Γ = em Γ → U k

  Tm : ∀ k → (Γ : C) → Ty k Γ → Set
  Tm k Γ A = (γ : em Γ) → el k (A γ)

  infixl 30 _▷_
  data C where
    ∙ : C
    _▷_ : ∀ {k} → (Γ : C) → Ty k Γ → C

  em ∙ = ⊤
  em (Γ ▷ A) = Σ[ γ ∈ em Γ ] el _ (A γ)

  {-----------------------------------------------------------
    Cumulativity tells us that we are allowed to lift types
    from lower levels to higher ones,
    as well as terms to ones typed at higher levels.
    I believe terms are in fact equal to their lifts,
    but the equality types are tricky to transport,
    and we don't need that fact anyway.
  -----------------------------------------------------------}

  liftTy : ∀ {j k Γ} → j < k → Ty j Γ → Ty k Γ
  liftTy j<k ty γ = lift j<k (ty γ)

  liftTm : ∀ {j k Γ A} → (j<k : j < k) → Tm j Γ A → Tm k Γ (liftTy j<k A)
  liftTm {A = A} j<k tm γ rewrite sym (el≡ j<k (A γ)) = tm γ

  {-----------------------------------------------------------
    Contexts C is a category with a terminal element,
    where morphisms (substitutions) are functions from
    (the interpretations of) one context to another.
    Ty and Tm are Fam-valued presheaves over C,
    whose actions on substitutions are actually applying
    the substitutions to the type or term.
  -----------------------------------------------------------}

  _⇒_ : C → C → Set
  Δ ⇒ Γ = em Δ → em Γ

  ⟨⟩ : ∀ {Γ} → Γ ⇒ ∙
  ⟨⟩ {Γ} _ = tt

  ⟨⟩η : ∀ {Γ} → (σ : Γ ⇒ ∙) → σ ≡ ⟨⟩
  ⟨⟩η _ = refl

  infix 30 _[_]ᵀ
  _[_]ᵀ : ∀ {k Δ Γ} → Ty k Γ → Δ ⇒ Γ → Ty k Δ
  (A [ σ ]ᵀ) δ = A (σ δ)

  infix 30 _[_]ᵗ
  _[_]ᵗ : ∀ {k Δ Γ} {A : Ty k Γ} → Tm k Γ A → (σ : Δ ⇒ Γ) → Tm k Δ (A [ σ ]ᵀ)
  (a [ σ ]ᵗ) δ = a (σ δ)

  {-----------------------------------------------------------
    Context comprehensions conventionally come with
    substitution extension and their projections,
    but since our contexts are inductively constructed,
    these are straightforward and rather redundant.
  -----------------------------------------------------------}

  ⟨_,_⟩ : ∀ {k Δ Γ} {A : Ty k Γ} → (σ : Δ ⇒ Γ) → Tm k Δ (A [ σ ]ᵀ) → Δ ⇒ (Γ ▷ A)
  ⟨ σ , a ⟩ δ = σ δ , a δ

  p : ∀ {k Γ} {A : Ty k Γ} → (Γ ▷ A) ⇒ Γ
  p (γ , a) = γ

  q : ∀ {k Γ} {A : Ty k Γ} → Tm k (Γ ▷ A) (A [ p ]ᵀ)
  q (γ , a) = a

  pqη : ∀ {k Γ} {A : Ty k Γ} → ⟨ p {k} {Γ} {A} , q {k} {Γ} {A} ⟩ ≡ λ γ → γ
  pqη = refl

  {-----------------------------------------------------------
    Modelling context membership and extracting a term.
    A more inductivey and expanded version of p/q I think.
  -----------------------------------------------------------}

  data _∋_ : ∀ {k} Γ → Ty k Γ → Set where
    here : ∀ {k Γ A} → Γ ▷ A ∋ A [ p {k} ]ᵀ
    there : ∀ {k Γ A B} → (_∋_ {k}) Γ A → Γ ▷ B ∋ A [ p {k} ]ᵀ

  en : ∀ {k Γ A} → Γ ∋ A → Tm k Γ A
  en here (γ , a) = a
  en (there where?) (γ , a) = en where? γ