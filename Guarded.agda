{-# OPTIONS --guarded --rewriting #-}

open import Agda.Primitive
open import Data.Product hiding (map ; zip)
open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}

{-- GUARDED TYPE THEORY PRIMITIVES --}
-- https://github.com/agda/guarded/blob/forcing-ticks/src/Guarded/Later.agda

primitive primLockUniv : Set₁
postulate Tick : primLockUniv
variable
  ℓ : Level
  A B C : Set ℓ

▹_ : ∀ {ℓ} → Set ℓ → Set ℓ
▹ A = (@tick x : Tick) → A

▸_ : ▹ Set → Set
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next a _ = a

ap : ▹ (A → B) → ▹ A → ▹ B
ap f a t = f t (a t)

ap2 : ▹ (A → B → C) → ▹ A → ▹ B → ▹ C
ap2 f a b t = f t (a t) (b t)

map : (f : A → B) → ▹ A → ▹ B
map f a t = f (a t)

map2 : (f : A → B → C) → ▹ A → ▹ B → ▹ C
map2 f a b t = f (a t) (b t)

postulate
  dfix : (▹ A → A) → ▹ A
  pfix : (f : ▹ A → A) → dfix f ≡ next (f (dfix f))
  tickext : (a b : ▹ A) → ▸ (λ t → a t ≡ b t) → a ≡ b

fix : (▹ A → A) → A
fix f = f (dfix f)

pfix' : (f : ▹ A → A) → fix f ≡ f (next (fix f))
pfix' f rewrite sym (pfix f) = refl

pfix'' : (f : ▹ A → A) → ▸ (λ t → dfix f t ≡ f (dfix f))
pfix'' f _ rewrite pfix f = cong f (pfix f)

-- {-# REWRITE pfix #-}

{-- GUARDED STREAMS --}

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ▹ Stream A
open Stream
{-# ETA Stream #-}

zip : (A → A → A) → Stream A → Stream A → Stream A
zip _+_ = fix (λ { _    s t .hd → s .hd + t .hd
                 ; ▹zip s t .tl → ap2 ▹zip (s .tl) (t .tl) })

shuffle : (A → A → A) → (A → A → A) → Stream A → Stream A → Stream A
shuffle _*_ _+_ = fix (λ { _        s t .hd → s .hd * t .hd
                         ; ▹shuffle s t .tl → map2 (zip _+_) (ap2 ▹shuffle (s .tl) (next t))
                                                             (ap2 ▹shuffle (next s) (t .tl)) })

caseStream : (P : Stream A → Set) → (∀ x xs → ▸ map P xs → P (x ∷ xs)) → ∀ s → P s
caseStream P ih = fix (λ ▹case s → ih (s .hd) (s .tl) (λ t → ▹case t (s .tl t)))

{-- NATIVE GUARDED STREAMS --}

Str : ∀ A → Set
Str A = fix (λ ▹Str → A × ▸ ▹Str)

cons : A → ▹ Str A → Str A
cons a s = a , subst ▸_ (sym (pfix _)) s

head : Str A → A
head (a , _) = a

tail : Str A → ▹ Str A
tail (_ , s) = subst ▸_ (pfix _) s

lemma : (P : A → Set) {x y : A} (p : x ≡ y) (s : P x) →
        subst P (sym p) (subst P p s) ≡ s
lemma P refl s = refl

eta : ∀ s → cons {A} (head s) (tail s) ≡ s
eta (a , s) = cong (a ,_) (lemma ▸_ (pfix _) s)

caseStr : (P : Str A → Set) → (∀ x xs → ▸ map P xs → P (cons x xs)) → ∀ s → P s
caseStr P ih = fix (λ ▹case (a , s) →
  let s' = subst ▸_ (pfix _) s
      Ps = ih a s' (λ t → ▹case t (s' t))
  in subst P (eta (a , s)) Ps)

{-- NATURALS --}

data Nat : Set where
  zero : Nat
  succ : ▹ Nat → Nat

succ' : Nat → Nat
succ' n = succ (next n)

indNat : (P : Nat → Set) → P zero → (∀ (n : ▹ Nat) → ▸ map P n → P (succ n)) → ∀ n → P n
indNat P pzero psucc = fix (λ { ▹indNat zero     → pzero
                              ; ▹indNat (succ n) → psucc n (λ t → ▹indNat t (n t)) })

_+_ : Nat → Nat → Nat
n + m = fix addFix n where
  addFix : ▹ (Nat → Nat) → Nat → Nat
  addFix ▹add zero     = m
  addFix ▹add (succ n) = succ (ap ▹add n)

-- requires turning on rewriting by pfix, which will loop infinitely later on
-- 3+2 : (succ' (succ' (succ' zero))) + (succ' (succ' zero)) ≡ (succ' (succ' (succ' (succ' (succ' zero)))))
-- 3+2 = refl

_∸_ : Nat → Nat → Nat
n ∸ m = fix monusFix n m where
  monusFix : ▹ (Nat → Nat → Nat) → Nat → Nat → Nat
  monusFix ▹monus zero     m        = zero
  monusFix ▹monus n        zero     = n
  monusFix ▹monus (succ n) (succ m) = {! ap2 ▹monus n m !} -- ▹Nat

{-- WELLFOUNDEDNESS? PRODUCTIVITY? --}

data ⊥ : Set where

data WF : Nat → Set where
  wfzero : WF zero
  wfsucc : ∀ n → ▸ (map WF n) → WF (succ n)

wf : ∀ n → WF n
wf zero = wfzero
wf (succ n) = wfsucc n (λ t → wf (n t))

-- bad and illegal!!
postulate join : ▹ ▹ A → ▹ A

conat : Nat
conat = fix succ

nwf : WF conat → ▹ ⊥
nwf (wfsucc _ wfconat) rewrite pfix succ = join (λ t → nwf (wfconat t))

▹false : ▹ ⊥
▹false = nwf (wf conat)

{-- COFIXPOINTS OF F ∘ ▸ --}

_∘▸_ : (Set → Set) → ▹ Set → Set
F ∘▸ X = F (▸ X)

ν_ : (Set → Set) → Set
ν F = fix (F ∘▸_)

variable F : Set → Set
postulate fmap : (A → B) → F A → F B

inF : F (▹ ν F) → ν F
inF {F} f = subst (F ∘▸_) (sym (pfix (F ∘▸_))) f

outF : ν F → F (▹ ν F)
outF {F} f = subst (F ∘▸_) (pfix (F ∘▸_)) f

inoutF : ∀ x → inF {F} (outF {F} x) ≡ x
inoutF {F} x = subst-sym-subst {P = F ∘▸_} (pfix (F ∘▸_)) {p = x}

outinF : ∀ x → outF {F} (inF {F} x) ≡ x
outinF {F} x = subst-subst-sym {P = F ∘▸_} (pfix (F ∘▸_)) {p = x}

coit : (A → F (▹ A)) → A → ν F
coit {A} {F} f = fix (λ ▹coit a → inF {F} (fmap {F = F} (ap ▹coit) (f a)))

case : (P : ν F → Set) → (∀ t → P (inF {F} t)) → ∀ x → P x
case {F} P p x = subst P (inoutF {F} x) (p (outF {F} x))

{-- COFIXPOINTS OF POLYNOMIAL FUNCTORS --}

-- Given container A ▹ Q, ℙ A Q is a polynomial functor
record ℙ (A : Set) (Q : A → Set) (X : Set) : Set where
  constructor _⟫_
  field
    shape : A
    position : Q shape → X
open ℙ

variable Q : A → Set

fmapP : (B → C) → ℙ A Q B → ℙ A Q C
fmapP f p .shape = p .shape
fmapP f p .position q = f (p .position q)

inP : ℙ A Q (▹ ν (ℙ A Q)) → ν (ℙ A Q)
inP (a ⟫ p) .shape = a
inP (a ⟫ p) .position q = subst ▸_ (sym (pfix (ℙ _ _ ∘▸_))) (p q)

outP : ν (ℙ A Q) → ℙ A Q (▹ ν (ℙ A Q))
outP (a ⟫ p) .shape = a
outP (a ⟫ p) .position q = subst ▸_ (pfix (ℙ _ _ ∘▸_)) (p q)

inoutP : (p : ν (ℙ A Q)) → inP (outP p) ≡ p
inoutP {A} {Q} (a ⟫ p) = {!   !}

outinP : (p : ℙ A Q (▹ ν (ℙ A Q))) → outP (inP p) ≡ p
outinP (a ⟫ p) = {!   !}

coitP : (B → ℙ A Q (▹ B)) → B → ν (ℙ A Q)
coitP f = fix (λ ▹coit b → inP (fmapP (ap ▹coit) (f b)))

caseP : (P : ν (ℙ A Q) → Set) → (∀ p → P (inP p)) → ∀ p → P p
caseP P pin p = subst P (inoutP p) (pin (outP p))