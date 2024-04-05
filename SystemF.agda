{-# OPTIONS --rewriting --cumulativity #-}

open import Agda.Primitive using (Setω ; Level ; _⊔_ ; lzero ; lsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (subst to transp ; subst₂ to transp₂)
open import Data.Product
open ≡-Reasoning

{-# BUILTIN REWRITE _≡_ #-}

infixl 30 _∷_
infixl 30 _∷′_
infix 20 _∈_
infix 20 _∈′_
infix 30 ↑_

{--------------------------------
Some helpful standard definitions
--------------------------------}

id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

coe : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coe refl x = x

coe-β : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) x → coe (sym p) (coe p x) ≡ x
coe-β refl x = refl

_↔_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A ↔ B = (A → B) × (B → A)

{-----------------------------------------------
A separate equality type is needed to talk about
equalities between things in a Setω type.
-----------------------------------------------}

infix 4 _≡⁺_
data _≡⁺_ {A : Setω} (x : A) : A → Set where
  instance refl : x ≡⁺ x

≡→≡⁺ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ≡⁺ y
≡→≡⁺ refl = refl

cong⁺ : ∀ {ℓ} {A : Setω} {B : Set ℓ} (f : A → B) {x y} → x ≡⁺ y → f x ≡ f y
cong⁺ f refl = refl

{--------------------------------------------------------
Some function extensionality postulates:
one for finite universes, one for the limit universe,
and one for the limit universe with an implicit argument.
I use rewriting so that the postulates compute on
reflexive proofs of pointwise equality.
A corollary is that dependent function types are equal
when their domains and codomains are also equal.
--------------------------------------------------------}

postulate
  funext : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} →
    {f g : ∀ x → B x} → (∀ x → _≡_ {ℓ'} (f x) (g x)) → _≡_ {ℓ ⊔ ℓ'} f g
  ifunext⁺ : ∀ {ℓ} {A : Set ℓ} {B : A → Setω} →
    {f g : ∀ {x} → B x} → (∀ {x} → f {x} ≡⁺ g {x}) → (λ {x} → f {x}) ≡⁺ (λ {x} → g {x})
  funext⁺ : ∀ {ℓ} {A : Set ℓ} {B : A → Setω} →
    {f g : ∀ x → B x} → (∀ x → f x ≡⁺ g x) → f ≡⁺ g
  
funext-β : ∀ {ℓ ℓ' A B f} → _≡_ {ℓ ⊔ ℓ'} (funext {ℓ} {ℓ'} {A} {B} {f} (λ _ → refl)) refl
funext-β {ℓ} {ℓ'} {A} {B} {f} with refl ← funext {ℓ} {ℓ'} {A} {B} {f} (λ _ → refl) = refl

ifunext⁺-β : ∀ {ℓ} {A : Set ℓ} {B : A → Setω} {f : ∀ {x} → B x} →
  ifunext⁺ {B = B} {f = f} (λ {_} → refl) ≡ refl
ifunext⁺-β {ℓ} {A} {B} {f} with refl ← ifunext⁺ {ℓ} {A} {B} {f} (λ {_} → refl) = refl

funext⁺-β : ∀ {ℓ} {A : Set ℓ} {B : A → Setω} {f : ∀ x → B x} →
  funext⁺ {B = B} {f = f} (λ _ → refl) ≡ refl
funext⁺-β {ℓ} {A} {B} {f} with refl ← funext⁺ {ℓ} {A} {B} {f} (λ _ → refl) = refl

{-# REWRITE funext-β ifunext⁺-β funext⁺-β #-}

piext : ∀ {ℓ ℓ'} {A A' : Set ℓ} {B : A → Set ℓ'} {B' : A' → Set ℓ'} →
        (p : A ≡ A') → (∀ x → _≡_ {lsuc ℓ'} (B x) (B' (coe p x))) → _≡_ {lsuc (ℓ ⊔ ℓ')} (∀ x → B x) (∀ x → B' x)
piext {ℓ} {ℓ'} {B = B} {B' = B'} refl h =
  cong {lsuc (ℓ ⊔ ℓ')} (λ B → ∀ x → B x) {x = B} {y = B'} (funext {lsuc ℓ} {lsuc ℓ'} h)

{---------------------------------------------------
A (Δ : LCtx) is a context of universe levels
under which a Type is well formed.
(ℓ ∈′ Δ) asserts that ℓ is somewhere in the context.
Its constructors here and there can be thought of as
de Bruijn indices 0 and +1.

Types are one of:
* a type variable, whose level is in the context;
* a function type; or
* a quantification over Types of smaller levels.
---------------------------------------------------}

data LCtx : Set where
  ∙ : LCtx
  _∷_ : LCtx → Level → LCtx

data _∈′_ (ℓ : Level) : LCtx → Set where
  here : ∀ {Δ} → ℓ ∈′ Δ ∷ ℓ
  there : ∀ {Δ ℓ'} → ℓ ∈′ Δ → ℓ ∈′ Δ ∷ ℓ'

data Type (Δ : LCtx) : Level → Set where
  var : ∀ {ℓ} → ℓ ∈′ Δ → Type Δ ℓ
  _⇒_ : ∀ {ℓ ℓ'} → Type Δ ℓ → Type Δ ℓ' → Type Δ (ℓ ⊔ ℓ')
  ∀′ : ∀ ℓ {ℓ'} → Type (Δ ∷ ℓ) ℓ' → Type Δ (lsuc ℓ ⊔ ℓ')

{----------------------------------------------------------------
Substitution in Types is needed to define the typing rules.
A renaming (ξ : ∀ {ℓ} → ℓ ∈′ Δ → ℓ ∈′ Δ') transforms an assertion
that ℓ is in a context Δ to one in a context Δ'.
Lifting extends a renaming by an additional level.
The renaming ξ can be applied to a Type in context Δ
to obtain a Type in context Δ'.
Weakening is an instance of renaming which extends the context.
----------------------------------------------------------------}

Ren : LCtx → LCtx → Set
Ren Δ Δ' = ∀ {ℓ} → ℓ ∈′ Δ → ℓ ∈′ Δ'

lift : ∀ {Δ Δ' ℓ} → Ren Δ Δ' → Ren (Δ ∷ ℓ) (Δ' ∷ ℓ)
lift ξ here = here
lift ξ (there where?) = there (ξ where?)

rename : ∀ {Δ Δ' ℓ} → Ren Δ Δ' → Type Δ ℓ → Type Δ' ℓ
rename ξ (var where?) = var (ξ where?)
rename ξ (A ⇒ B) = rename ξ A ⇒ rename ξ B
rename ξ (∀′ ℓ B) = ∀′ ℓ (rename (lift ξ) B)

weaken : ∀ {Δ ℓ ℓ'} → Type Δ ℓ → Type (Δ ∷ ℓ') ℓ
weaken A = rename there A

{----------------------------------------------------------------
A substitution (σ : ∀ {ℓ} → ℓ ∈′ Δ → Type Δ' ℓ) maps an assertion
that ℓ is in a context Δ to a Type of that level
that is well formed in some other context Δ'.
They can also be lifted by extending with an additional level.
A substitution can be extended by a single Type,
and subsituting one Type in another corresponds to
applying the identity substitution var extended by
the Type to be substituted in.
----------------------------------------------------------------}

Subst : LCtx → LCtx → Set
Subst Δ Δ' = ∀ {ℓ} → ℓ ∈′ Δ → Type Δ' ℓ

↑_ : ∀ {Δ Δ' ℓ} → Subst Δ Δ' → Subst (Δ ∷ ℓ) (Δ' ∷ ℓ)
(↑ σ) here = var here
(↑ σ) (there where?) = rename there (σ where?)

subst : ∀ {Δ Δ' ℓ} → Subst Δ Δ' → Type Δ ℓ → Type Δ' ℓ
subst σ (var where?) = σ where?
subst σ (A ⇒ B) = subst σ A ⇒ subst σ B
subst σ (∀′ ℓ B) = ∀′ ℓ (subst (↑ σ) B)

consT : ∀ {Δ ℓ} → Subst Δ Δ → Type Δ ℓ → Subst (Δ ∷ ℓ) Δ
consT σ A here = A
consT σ A (there where?) = σ where?

subst₁ : ∀ {Δ ℓ ℓ'} → Type (Δ ∷ ℓ) ℓ' → Type Δ ℓ → Type Δ ℓ'
subst₁ B A = subst (consT var A) B

{--------------------------------------------------------------
A (Γ : Ctx) is a context of Types well formed in Δ
under which a Term is well typed.
It has a third constructor for extending the context of levels
without adding anything to the context of Types.
(A ∈ Γ) asserts that A is somewhere in the context;
it has constructors for skipping over other Types
and also for skipping over extensions by levels.

Terms are one of:
* a term variable, whose Type is in the context;
* a function abstraction; a function application;
* a Type abstraction; or an application of one to a Type.
Note the use of substitution in the Type for Type applications.
--------------------------------------------------------------}

data Ctx : LCtx → Set where
  ∙ : ∀ {Δ} → Ctx Δ
  _∷_ : ∀ {Δ ℓ} → Ctx Δ → Type Δ ℓ → Ctx Δ
  _∷′_ : ∀ {Δ} → Ctx Δ → ∀ ℓ → Ctx (Δ ∷ ℓ)

data _∈_ {ℓ} : ∀ {Δ} → Type Δ ℓ → Ctx Δ → Set where
  here : ∀ {Δ Γ} {A : Type Δ ℓ} → A ∈ Γ ∷ A
  there : ∀ {Δ Γ ℓ' A} {B : Type Δ ℓ'} → A ∈ Γ → A ∈ Γ ∷ B
  tskip : ∀ {Δ Γ} (A : Type Δ ℓ) → A ∈ Γ → (weaken A) ∈ Γ ∷′ ℓ

data Term (Δ : LCtx) (Γ : Ctx Δ) : ∀ {ℓ} → Type Δ ℓ → Set where
  var : ∀ {A} → A ∈ Γ → Term Δ Γ A
  λ′ : ∀ {A B} → Term Δ (Γ ∷ A) B → Term Δ Γ (A ⇒ B)
  $′ : ∀ {A B} → Term Δ Γ (A ⇒ B) → Term Δ Γ A → Term Δ Γ B
  Λ : ∀ {ℓ ℓ'} {B : Type (Δ ∷ ℓ) ℓ'} → Term (Δ ∷ ℓ) (Γ ∷′ ℓ) B → Term Δ Γ (∀′ ℓ B)
  $ : ∀ {ℓ ℓ'} {B : Type (Δ ∷ ℓ) ℓ'} → Term Δ Γ (∀′ ℓ B) → (A : Type Δ ℓ) → Term Δ Γ (subst₁ B A)

{---------------------------------------------------------------
Let's begin with an interpretation of Types as Agda types.
A (η : TEnv Δ) is an environment of types,
mapping a level ℓ in Δ to a type in Set ℓ.
They can be extended by a single type.
The interpretation of a well formed Type in context Δ at level ℓ
using a mapping η is a type in Set ℓ.

Some helpful lemmas are needed:
* ⟦ext⟧′ says the interpretations of a Type
  under pointwise equal environments are equal;
* ⟦ren⟧′ says the intepretation of a Type
  is the same as that of the same type renamed
  with the environment precomposed with that renaming;
* ⟦wk⟧′ says the interpretation of a Type
  is the same as that of the same type weakened;
* ⟦subst⟧′ says that interpretation commutes with substitution,
  so the interpretation of a substituted Type
  is the same as that of the original Type
  but with the environment substituted over instead; and
* ⟦subst₁⟧′ specializes it to single substitution.
---------------------------------------------------------------}

TEnv : LCtx → Setω
TEnv Δ = ∀ {ℓ} → ℓ ∈′ Δ → Set ℓ

cons : ∀ {Δ ℓ} → TEnv Δ → Set ℓ → TEnv (Δ ∷ ℓ)
cons η A here = A
cons η A (there where?) = η where?

⟦_⟧′ : ∀ {Δ ℓ} → Type Δ ℓ → TEnv Δ → Set ℓ
⟦ var where? ⟧′ η = η where?
⟦ A ⇒ B ⟧′ η = (⟦ A ⟧′ η) → (⟦ B ⟧′ η)
⟦ ∀′ ℓ B ⟧′ η = (A : Set ℓ) → (⟦ B ⟧′ (cons η A))

⟦ext⟧′ : ∀ {Δ ℓ} (η₁ η₂ : TEnv Δ) →
         (∀ {ℓ} (where? : ℓ ∈′ Δ) → _↔_ {ℓ} (η₁ where?) (η₂ where?)) →
         (A : Type Δ ℓ) → _↔_ {ℓ} (⟦ A ⟧′ η₁) (⟦ A ⟧′ η₂)
⟦ext⟧′ η₁ η₂ h (var where?) = h where?
⟦ext⟧′ η₁ η₂ h (A ⇒ B) =
  let la , ra = ⟦ext⟧′ η₁ η₂ h A
      lb , rb = ⟦ext⟧′ η₁ η₂ h B
  in (λ f a → lb (f (ra a))) , (λ f a → rb (f (la a)))
⟦ext⟧′ η₁ η₂ h (∀′ ℓ B) =
  (λ f A →
    let lA , rA = ⟦ext⟧′ (cons {ℓ = ℓ} η₁ A) (cons {ℓ = ℓ} η₂ A)
                         (λ { here → (λ a → a) , (λ a → a)
                            ; (there where?) → h where? }) B
    in lA (f A)) ,
  (λ f A →
    let lA , rA = ⟦ext⟧′ (cons {ℓ = ℓ} η₁ A) (cons {ℓ = ℓ} η₂ A)
                         (λ { here → (λ a → a) , (λ a → a)
                            ; (there where?) → h where? }) B
    in rA (f A))

⟦ren⟧′ : ∀ {Δ Δ' ℓ} (η₁ : TEnv Δ) (η₂ : TEnv Δ') (ξ : Ren Δ Δ')
         (h : ∀ {ℓ} → (where? : ℓ ∈′ Δ) → η₁ where? ≡ η₂ (ξ where?))
         (B : Type Δ ℓ) → ⟦ B ⟧′ η₁ ↔ ⟦ rename ξ B ⟧′ η₂
⟦ren⟧′ η₁ η₂ ξ h (var where?) = coe (h where?) , coe (sym (h where?))
⟦ren⟧′ η₁ η₂ ξ h (A ⇒ B) =
  let la , ra = ⟦ren⟧′ η₁ η₂ ξ h A
      lb , rb = ⟦ren⟧′ η₁ η₂ ξ h B
  in (λ f a → lb (f (ra a))) , (λ f a → rb (f (la a)))
⟦ren⟧′ η₁ η₂ ξ h (∀′ ℓ B) =
  (λ f A →
    let lA , rA = ⟦ren⟧′ (cons {ℓ = ℓ} η₁ A) (cons {ℓ = ℓ} η₂ A) (lift ξ)
                         (λ {here → refl ; (there where?) → h where?}) B
    in lA (f A)) ,
  (λ f A →
    let lA , rA = ⟦ren⟧′ (cons {ℓ = ℓ} η₁ A) (cons {ℓ = ℓ} η₂ A) (lift ξ)
                         (λ {here → refl ; (there where?) → h where?}) B
    in rA (f A))

⟦wk⟧′ : ∀ {Δ ℓ ℓ'} (η : TEnv Δ) (A : Set ℓ') (B : Type Δ ℓ) → ⟦ B ⟧′ η ↔ ⟦ weaken B ⟧′ (cons η A)
⟦wk⟧′ η A B = ⟦ren⟧′ η (cons η A) there (λ _ → refl) B

⟦subst⟧′ : ∀ {Δ Δ' ℓ} (η : TEnv Δ') (σ : Subst Δ Δ') (B : Type Δ ℓ) →
           ⟦ B ⟧′ (λ where? → ⟦ σ where? ⟧′ η) ↔ ⟦ subst σ B ⟧′ η
⟦subst⟧′ η σ (var where?) = id , id
⟦subst⟧′ η σ (A ⇒ B) =
  let la , ra = ⟦subst⟧′ η σ A
      lb , rb = ⟦subst⟧′ η σ B
  in (λ f a → lb (f (ra a))) , (λ f a → rb (f (la a)))
⟦subst⟧′ η σ (∀′ ℓ {ℓ'} B) =
  (λ f A →
    let lA , rA = ⟦subst⟧′ (cons {ℓ = ℓ} η A) (↑ σ) B
        lB , rB = ⟦ext⟧′ (cons {ℓ = ℓ} (λ where? → ⟦ σ where? ⟧′ η) A)
                         (λ where? → ⟦ (↑ σ) where? ⟧′ (cons {ℓ = ℓ} η A))
                         (λ { here → id , id
                            ; (there where?) → ⟦wk⟧′ η A (σ where?) }) B
    in lA (lB (f A))) ,
  (λ f A →
    let lA , rA = ⟦subst⟧′ (cons {ℓ = ℓ} η A) (↑ σ) B
        lB , rB = ⟦ext⟧′ (cons {ℓ = ℓ} (λ where? → ⟦ σ where? ⟧′ η) A)
                         (λ where? → ⟦ (↑ σ) where? ⟧′ (cons {ℓ = ℓ} η A))
                         (λ { here → id , id
                            ; (there where?) → ⟦wk⟧′ η A (σ where?) }) B
    in rB (rA (f A)))

⟦subst₁⟧′ : ∀ {Δ ℓ ℓ'} (η : TEnv Δ) (A : Type Δ ℓ) (B : Type (Δ ∷ ℓ) ℓ') →
            ⟦ B ⟧′ (cons η (⟦ A ⟧′ η)) ↔ ⟦ subst₁ B A ⟧′ η
⟦subst₁⟧′ {ℓ = ℓ} η A B =
  let lsubst₁ , rsubst₁ = ⟦subst⟧′ η (consT var A) B
      lb , rb = ⟦ext⟧′ (cons {ℓ = ℓ} η (⟦ A ⟧′ η))
                       (λ where? → ⟦ consT var A where? ⟧′ η)
                       (λ { here → id , id
                          ; (there where?) → id , id }) B
  in (λ b → lsubst₁ (lb b)) , (λ b → rb (rsubst₁ b))

{----------------------------------------------------------------------
Let's now consider the interpretation of Terms as Agda terms.
A (δ : Env Γ η) is an environment of terms,
mapping a Type A in the context Γ to a term
in the interpretation of A under an environment of types η.
They can be extended by a single Term,
as well as weakened by a type that is added to η.
Crucially, the interpretation relies on the lemmas ⟦wk⟧′ and ⟦subst₁⟧′.
----------------------------------------------------------------------}

Env : ∀ {Δ} → Ctx Δ → TEnv Δ → Setω
Env {Δ} Γ η = ∀ {ℓ} {A : Type Δ ℓ} → A ∈ Γ → ⟦ A ⟧′ η

extend : ∀ {Δ Γ ℓ} {A : Type Δ ℓ} {η : TEnv Δ} → Env Γ η → ⟦ A ⟧′ η → Env (Γ ∷ A) η
extend δ a here = a
extend δ a (there where?) = δ where?

extend′ : ∀ {Δ Γ ℓ} (η : TEnv Δ) → Env Γ η → (A : Set ℓ) → Env (Γ ∷′ ℓ) (cons η A)
extend′ η δ A (tskip B where?) = proj₁ (⟦wk⟧′ η A B) (δ where?)

⟦_⟧ : ∀ {Δ Γ ℓ A} → Term Δ Γ {ℓ} A → (η : TEnv Δ) → Env Γ η → ⟦ A ⟧′ η
⟦ var where? ⟧ η δ = δ where?
⟦ λ′ b ⟧ η δ = λ a → ⟦ b ⟧ η (extend δ a)
⟦ $′ b a ⟧ η δ = ⟦ b ⟧ η δ (⟦ a ⟧ η δ)
⟦ Λ {ℓ} b ⟧ η δ = λ A → ⟦ b ⟧ (cons η A) (extend′ {ℓ = ℓ} η δ A)
⟦ $ {B = B} b A ⟧ η δ = proj₁ (⟦subst₁⟧′ η A B) (⟦ b ⟧ η δ (⟦ A ⟧′ η))

{-----------------------------------------------------------------------
Now let's move on to a *relational* interpretation of Types.
A (ρ : RTEnv Δ η₁ η₂) is an environment of relations in Agda,
mapping a level ℓ to a relation in Set ℓ
between the corresponding types in η₁ and η₂.
ρ can also be thought of as a relation between type environments,
providing relations pointwise: ∀x, ρ(x) : Rel(η₁(x), η₂(x)).
They can be extended by a single relation between two new types.
Given a relational type environment ρ and a Type A,
(typerel η₁ η₂ ρ A) produces a relation between the interpretations of A
under type environments η₁ and η₂.
I may write this as ⟦A⟧ᴿ ρ in the notes.

I need weakening and single substitution lemmas wkᴿ and subst₁ᴿ,
which are more or less coherence lemmas for ⟦wk⟧′ and ⟦subst₁⟧′.
These look very gnarly to prove, so I leave them as holes for now.
-----------------------------------------------------------------------}

RTEnv : ∀ Δ → TEnv Δ → TEnv Δ → Setω
RTEnv Δ η₁ η₂ = ∀ {ℓ} → (where? : ℓ ∈′ Δ) → η₁ where? → η₂ where? → Set ℓ

consᴿ : ∀ {Δ ℓ} → {η₁ η₂ : TEnv Δ} {A₁ A₂ : Set ℓ} → RTEnv Δ η₁ η₂ → (A₁ → A₂ → Set ℓ) → RTEnv (Δ ∷ ℓ) (cons η₁ A₁) (cons η₂ A₂)
consᴿ ρ R here = R
consᴿ ρ R (there where?) = ρ where?

typerel : ∀ {Δ ℓ} (η₁ η₂ : TEnv Δ) (ρ : RTEnv Δ η₁ η₂) (A : Type Δ ℓ) → ⟦ A ⟧′ η₁ → ⟦ A ⟧′ η₂ → Set ℓ
typerel η₁ η₂ ρ (var where?) = ρ where?
typerel η₁ η₂ ρ (A ⇒ B) f₁ f₂ = ∀ a₁ a₂ → typerel η₁ η₂ ρ A a₁ a₂ → typerel η₁ η₂ ρ B (f₁ a₁) (f₂ a₂)
typerel η₁ η₂ ρ (∀′ ℓ B) f₁ f₂ = ∀ A₁ A₂ R → typerel (cons η₁ A₁) (cons η₂ A₂) (consᴿ ρ R) B (f₁ A₁) (f₂ A₂)

wkᴿ : ∀ {Δ ℓ ℓ'} {η₁ η₂ : TEnv Δ} {ρ : RTEnv Δ η₁ η₂} {A₁ A₂ : Set ℓ'} {R : A₁ → A₂ → Set ℓ'}
       (B : Type Δ ℓ) (a₁ : ⟦ B ⟧′ η₁) (a₂ : ⟦ B ⟧′ η₂) →
       typerel η₁ η₂ ρ B a₁ a₂ ≡
       typerel (cons {ℓ = ℓ'} η₁ A₁) (cons {ℓ = ℓ'} η₂ A₂) (consᴿ ρ R) (weaken B) (proj₁ (⟦wk⟧′ η₁ A₁ B) a₁) (proj₁ (⟦wk⟧′ η₂ A₂ B) a₂)
wkᴿ B a₁ a₂ = {!   !}

subst₁ᴿ : ∀ {Δ Γ ℓ ℓ'} (η₁ η₂ : TEnv Δ) (ρ : RTEnv Δ η₁ η₂) (δ₁ : Env Γ η₁) (δ₂ : Env Γ η₂)
            (A : Type Δ ℓ) (B : Type (Δ ∷ ℓ) ℓ') (b : Term Δ Γ (∀′ ℓ B)) →
          typerel (cons {ℓ = ℓ} η₁ (⟦ A ⟧′ η₁)) (cons {ℓ = ℓ} η₂ (⟦ A ⟧′ η₂)) (consᴿ ρ (typerel η₁ η₂ ρ A))
                  B (⟦ b ⟧ η₁ δ₁ (⟦ A ⟧′ η₁)) (⟦ b ⟧ η₂ δ₂ (⟦ A ⟧′ η₂)) ≡
          typerel η₁ η₂ ρ (subst₁ B A)
                  (proj₁ (⟦subst₁⟧′ η₁ A B) (⟦ b ⟧ η₁ δ₁ (⟦ A ⟧′ η₁)))
                  (proj₁ (⟦subst₁⟧′ η₂ A B) (⟦ b ⟧ η₂ δ₂ (⟦ A ⟧′ η₂)))
subst₁ᴿ η₁ η₂ ρ δ₁ δ₂ A B = {!   !}

{-------------------------------------------------------------------------
Finally, we have the relational interpretation of Terms.
A (ζ : REnv η₁ η₂ ρ δ₁ δ₂) is an environment of relations in Agda,
mapping a Type A to an assertion that the corresponding terms in δ₁ and δ₂
are related by the relational interpretation of A.
ζ can also be thought of as a pointwise assertion of relatedness
between δ₁ and δ₂: ∀x, ζ(x) : (δ₁(x), δ₂(x)) ∈ ⟦A⟧ᴿ ρ.
They can be extended by a proof of relatedness between two new terms.

Given a relational type environment ρ, a relational term environment ζ,
and a Term a of Type A, (termrel η₁ η₂ ρ δ₁ δ₂ A a ζ) asserts that
the interpretations of a under δ₁ and δ₂ are related
by the relational interpretation of A.
This is the fundamental Abstraction Theorem of parametricity.
Crucially, it relies on the lemmas wkᴿ and subst₁ᴿ.
-------------------------------------------------------------------------}

REnv : ∀ {Δ Γ} (η₁ η₂ : TEnv Δ) (ρ : RTEnv Δ η₁ η₂) (δ₁ : Env Γ η₁) (δ₂ : Env Γ η₂) → Setω
REnv {Δ} {Γ} η₁ η₂ ρ δ₁ δ₂ = ∀ {ℓ} {A : Type Δ ℓ} → (where? : A ∈ Γ) → typerel η₁ η₂ ρ A (δ₁ where?) (δ₂ where?)

extendᴿ : ∀ {Δ Γ ℓ} {η₁ η₂ : TEnv Δ} {ρ : RTEnv Δ η₁ η₂} {δ₁ : Env Γ η₁} {δ₂ : Env Γ η₂}
          {A : Type Δ ℓ} {a₁ : ⟦ A ⟧′ η₁} {a₂ : ⟦ A ⟧′ η₂} →
          REnv η₁ η₂ ρ δ₁ δ₂ → typerel η₁ η₂ ρ A a₁ a₂ →
          REnv η₁ η₂ ρ (extend {A = A} δ₁ a₁) (extend {A = A} δ₂ a₂)
extendᴿ ζ Ra here = Ra
extendᴿ ζ Ra (there where?) = ζ where?

extendᴿ′ : ∀ {Δ Γ ℓ} {η₁ η₂ : TEnv Δ} {ρ : RTEnv Δ η₁ η₂} {δ₁ : Env Γ η₁} {δ₂ : Env Γ η₂}
           {A₁ A₂ : Set ℓ} {R : A₁ → A₂ → Set ℓ} →
           REnv η₁ η₂ ρ δ₁ δ₂ →
           REnv (cons {ℓ = ℓ} η₁ A₁) (cons {ℓ = ℓ} η₂ A₂) (consᴿ ρ R) (extend′ η₁ δ₁ A₁) (extend′ η₂ δ₂ A₂)
extendᴿ′ {δ₁ = δ₁} {δ₂ = δ₂} ζ (tskip B where?) = coe (wkᴿ B (δ₁ where?) (δ₂ where?)) (ζ where?)

termrel : ∀ {Δ Γ ℓ} (η₁ η₂ : TEnv Δ) (ρ : RTEnv Δ η₁ η₂) (δ₁ : Env Γ η₁) (δ₂ : Env Γ η₂) →
          REnv η₁ η₂ ρ δ₁ δ₂ → ∀ {A : Type Δ ℓ} (a : Term Δ Γ A) →
          typerel η₁ η₂ ρ A (⟦ a ⟧ η₁ δ₁) (⟦ a ⟧ η₂ δ₂)
termrel η₁ η₂ ρ δ₁ δ₂ ζ (var where?) = ζ where?
termrel η₁ η₂ ρ δ₁ δ₂ ζ (λ′ b) a₁ a₂ Ra = termrel η₁ η₂ ρ (extend δ₁ a₁) (extend δ₂ a₂) (extendᴿ ζ Ra) b
termrel η₁ η₂ ρ δ₁ δ₂ ζ ($′ b a) = termrel η₁ η₂ ρ δ₁ δ₂ ζ b (⟦ a ⟧ η₁ δ₁) (⟦ a ⟧ η₂ δ₂) (termrel η₁ η₂ ρ δ₁ δ₂ ζ a)
termrel η₁ η₂ ρ δ₁ δ₂ ζ (Λ {ℓ} b) A₁ A₂ R =
  termrel (cons {ℓ = ℓ} η₁ A₁) (cons {ℓ = ℓ} η₂ A₂) (consᴿ ρ R) (extend′ η₁ δ₁ A₁) (extend′ η₂ δ₂ A₂) (extendᴿ′ ζ) b
termrel η₁ η₂ ρ δ₁ δ₂ ζ ($ b A) =
  let ⟦b⟧A = termrel η₁ η₂ ρ δ₁ δ₂ ζ b (⟦ A ⟧′ η₁) (⟦ A ⟧′ η₂) (typerel η₁ η₂ ρ A)
  in coe (subst₁ᴿ η₁ η₂ ρ δ₁ δ₂ A _ b) ⟦b⟧A

{-----------------------------------------------------
Example:
Let f be a Term of the identity function Type.
Then the interpretation of f is the identity function.
-----------------------------------------------------}

idparam : ∀ ℓ (f : Term ∙ ∙ (∀′ ℓ (var here ⇒ var here))) →
            ⟦ f ⟧ (λ ()) (λ ()) ≡ (λ A (x : A) → x)
idparam ℓ f =
  let h = termrel (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) f
  in funext {lsuc ℓ} {ℓ} (λ A →
     funext {ℓ} {ℓ} (λ x →
     h A A (λ x₁ x₂ → x₁ ≡ x) x x refl))