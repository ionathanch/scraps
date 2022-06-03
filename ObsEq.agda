{-# OPTIONS --prop --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

{- Internal definitions -}

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
_∧_ : Prop → Prop → Prop
A ∧ B = Σ A (λ _ → B)

{- Universe codes and decoding -}

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

{- Equality of Ωs -}

EqΩ : Ω → Ω → Prop
EqΩ A B = (em A → em B) ∧ (em B → em A)

castΩ : (A B : Ω) → EqΩ A B → em A → em B
castΩ _ _ (to , from) x = to x

symΩ : {A B : Ω} → EqΩ A B → EqΩ B A
symΩ (to , from) = from , to

ReflΩ : {A : Ω} → EqΩ A A
ReflΩ = (λ a → a) , (λ a → a)

{- Equality of Us -}

EqU : U → U → Prop
castU : (A B : U) → EqU A B → el A → el B
symU : {A B : U} → EqU A B → EqU B A

EqU Nat Nat = ⊤
EqU (PiUU A B) (PiUU A' B') = Σ[ p ∈ EqU A A' ] (∀ (a' : el A') → EqU (B (castU A' A (symU {A} p) a')) (B' a'))
EqU (PiΩU A B) (PiΩU A' B') = Σ[ p ∈ EqΩ A A' ] (∀ (a' : em A') → EqU (B (castΩ A' A (symΩ p) a')) (B' a'))
EqU _ _ = ⊥

castU Nat Nat p zero = zero
castU Nat Nat p (succ n) = succ (castU Nat Nat p n)
castU (PiUU A B) (PiUU A' B') (aa' , bb') f = λ a' →
  let a = castU A' A (symU aa') a'
  in castU (B a) (B' a') (bb' a') (f a)
castU (PiΩU A B) (PiΩU A' B') (aa' , bb') f = λ a' →
  let a = castΩ A' A (symΩ aa') a'
  in castU (B a) (B' a') (bb' a') (f a)

postulate
  castUU : ∀ {A : U} {p : EqU A A} (a : el A) → castU A A p a ≡ a
  castU2 : ∀ {A B : U} {p : EqU A B} {q : EqU B A} (a : el A) → castU B A q (castU A B p a) ≡ a

{-# REWRITE castUU castU2 #-}

symU {Nat} {Nat} tt = tt
symU {PiUU A B} {PiUU A' B'} (p , f) = symU p , λ a → symU (f (castU A A' p a))
symU {PiΩU A B} {PiΩU A' B'} (p , f) = symΩ p , λ a → symU (f (castΩ A A' p a))

ReflU : {A : U} → EqU A A
ReflU {Nat} = tt
ReflU {PiUU A B} = ReflU , λ a' → ReflU
ReflU {PiΩU A B} = ReflΩ , λ a' → ReflU

{- Equality of terms in U types -}

eqU : (A : U) → (a b : el A) → Prop
eqU Nat zero zero = ⊤
eqU Nat (succ n) (succ m) = eqU Nat n m
eqU Nat _ _ = ⊥
eqU (PiUU A B) f g = (a : el A) → eqU (B a) (f a) (g a)
eqU (PiΩU A B) f g = (a : em A) → eqU (B a) (f a) (g a)

reflU : {A : U} → (a : el A) → eqU A a a
reflU {Nat} zero = tt
reflU {Nat} (succ n) = reflU n
reflU {PiUU A B} f = λ a → reflU {B a} (f a)
reflU {PiΩU A B} f = λ a → reflU {B a} (f a)

transp : (A : U) → (t : el A) → (P : (x : el A) → eqU A t x → Ω) → em (P t (reflU t)) → (t' : el A) → (p : eqU A t t') → em (P t' p)
transp Nat zero P d zero tt = d
transp Nat (succ n) P d (succ m) p = transp Nat n (λ x p → P (succ x) p) d m p
transp (PiUU A B) f P d g p = {!   !}
transp (PiΩU A B) f P d g p = {!   !}