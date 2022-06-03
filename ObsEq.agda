{-# OPTIONS --prop --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data ⊥ : Prop where
record ⊤ : Prop where
  constructor tt
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
record Σ (A : Prop) (B : A → Prop) : Prop where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ
syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

data U : Set
data Ω : Set
el : U → Set
em : Ω → Prop

data U where
  Nat : U
  PiUU : (A : U) → (el A → U) → U
  PiΩU : (A : Ω) → (em A → U) → U

data Ω where
  Empty : Ω
  Unit : Ω
  PiUΩ : (A : U) → (el A → Ω) → Ω
  PiΩΩ : (A : Ω) → (em A → Ω) → Ω

el Nat = ℕ
el (PiUU A B) = (a : el A) → el (B a)
el (PiΩU A B) = (a : em A) → el (B a)

em Empty = ⊥
em Unit = ⊤
em (PiUΩ A B) = (a : el A) → em (B a)
em (PiΩΩ A B) = (a : em A) → em (B a)

EqU : U → U → Prop
EqΩ : Ω → Ω → Prop
CastU : (A B : U) → EqU A B → el A → el B
CastΩ : (A B : Ω) → EqΩ A B → em A → em B
symU : {A B : U} → EqU A B → EqU B A
symΩ : {A B : Ω} → EqΩ A B → EqΩ B A

EqU Nat Nat = ⊤
EqU (PiUU A B) (PiUU A' B') = Σ[ p ∈ EqU A A' ] (∀ (a' : el A') → EqU (B (CastU A' A (symU {A} p) a')) (B' a'))
EqU (PiΩU A B) (PiΩU A' B') = Σ[ p ∈ EqΩ A A' ] (∀ (a' : em A') → EqU (B (CastΩ A' A (symΩ p) a')) (B' a'))
EqU _ _ = ⊥

EqΩ Empty Empty = ⊤
EqΩ Unit Unit = ⊤
EqΩ (PiUΩ A B) (PiUΩ A' B') = Σ[ p ∈ EqU A A' ] (∀ (a' : el A') → EqΩ (B (CastU A' A (symU p) a')) (B' a'))
EqΩ (PiΩΩ A B) (PiΩΩ A' B') = Σ[ p ∈ EqΩ A A' ] (∀ (a' : em A') → EqΩ (B (CastΩ A' A (symΩ {A} p) a')) (B' a'))
EqΩ _ _ = ⊥

CastU Nat Nat p zero = zero
CastU Nat Nat p (succ n) = succ (CastU Nat Nat p n)
CastU (PiUU A B) (PiUU A' B') p f = λ a' →
  let a = CastU A' A (symU (fst p)) a'
  in CastU (B a) (B' a') (snd p a') (f a)
CastU (PiΩU A B) (PiΩU A' B') p f = λ a' →
  let a = CastΩ A' A (symΩ (fst p)) a'
  in CastU (B a) (B' a') (snd p a') (f a)

CastΩ Empty Empty p ()
CastΩ Unit Unit p tt = tt
CastΩ (PiUΩ A B) (PiUΩ A' B') p f = λ a' →
  let a = CastU A' A (symU (fst p)) a'
  in CastΩ (B a) (B' a') (snd p a') (f a)
CastΩ (PiΩΩ A B) (PiΩΩ A' B') p f = λ a' →
  let a = CastΩ A' A (symΩ (fst p)) a'
  in CastΩ (B a) (B' a') (snd p a') (f a)

postulate
  CastUU : ∀ {A : U} {p : EqU A A} (a : el A) → CastU A A p a ≡ a
  CastU2 : ∀ {A B : U} {p : EqU A B} {q : EqU B A} (a : el A) → CastU B A q (CastU A B p a) ≡ a

{-# REWRITE CastUU CastU2 #-}

symU {Nat} {Nat} tt = tt
symU {PiUU A B} {PiUU A' B'} (p , f) = symU p , λ a → symU (f (CastU A A' p a))
symU {PiΩU A B} {PiΩU A' B'} (p , f) = symΩ p , λ a → symU (f (CastΩ A A' p a))

symΩ {Empty} {Empty} tt = tt
symΩ {Unit} {Unit} tt = tt
symΩ {PiUΩ A B} {PiUΩ A' B'} (p , f) = symU p , λ a → symΩ (f (CastU A A' p a))
symΩ {PiΩΩ A B} {PiΩΩ A' B'} (p , f) = symΩ p , λ a → symΩ (f (CastΩ A A' p a))

reflU : {A : U} → EqU A A
reflΩ : {A : Ω} → EqΩ A A

reflU {Nat} = tt
reflU {PiUU A B} = reflU , λ a' → reflU
reflU {PiΩU A B} = reflΩ , λ a' → reflU

reflΩ {Empty} = tt
reflΩ {Unit} = tt
reflΩ {PiUΩ A B} = reflU , λ a' → reflΩ
reflΩ {PiΩΩ A B} = reflΩ , λ a' → reflΩ