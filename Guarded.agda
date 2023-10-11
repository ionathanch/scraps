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

_>0 : ∀ ℓ → Level
ℓ >0 = lsuc lzero ⊔ ℓ

▹_ : Set ℓ → Set ℓ
▹ A = (@tick t : Tick) → A

▸_ : ▹ (Set ℓ) → Set ℓ
▸ A = (@tick t : Tick) → A t

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

{-- COFIXPOINTS OF F ∘ ▸ --

(νF, inF) is a final coälgebra for F ∘ ▹,
not for F itself:

         coit f
      A -------> νF
      |          Λ
    f |          | inF
      V          |
     F ▹A ----> F ▹νF
    fmap ∘ ap (coit f)

Instead, given an arbitrary functor F,
we would like to find its cofixpoint.
------------------------------------------}

_∘▸_ : (Set ℓ → Set ℓ) → ▹ Set ℓ → Set ℓ
F ∘▸ X = F (▸ X)

ν′_ : (Set ℓ → Set ℓ) → Set ℓ
ν′ F = fix (F ∘▸_)

module grec (F : Set ℓ → Set ℓ)
            (fmap : ∀ {A B} → (A → B) → F A → F B) where

  inF : F (▹ ν′ F) → ν′ F
  inF f = subst (F ∘▸_) (sym (pfix (F ∘▸_))) f

  outF : ν′ F → F (▹ ν′ F)
  outF f = subst (F ∘▸_) (pfix (F ∘▸_)) f

  inoutF : ∀ x → inF (outF x) ≡ x
  inoutF x = subst-sym-subst {P = F ∘▸_} (pfix (F ∘▸_)) {p = x}

  outinF : ∀ x → outF (inF x) ≡ x
  outinF x = subst-subst-sym {P = F ∘▸_} (pfix (F ∘▸_)) {p = x}

  coit : (A → F (▹ A)) → A → ν′ F
  coit f = fix (λ ▹coit a → inF (fmap (ap ▹coit) (f a)))

  case : (P : ν′ F → Set) → (∀ t → P (inF t)) → ∀ x → P x
  case P p x = subst P (inoutF x) (p (outF x))

{-- MORE GUARDED PRIMITIVES --}

▹[_] : primLockUniv → Set ℓ → Set ℓ
▹[ κ ] A = (@tick t : κ) → A

▸[_] : (κ : primLockUniv) → ▹[ κ ] (Set ℓ) → Set ℓ
▸[ κ ] A = (@tick t : κ) → A t

nextκ : ∀ κ → A → ▹[ κ ] A
nextκ _ a _ = a

apκ : ∀ κ → ▹[ κ ] (A → B) → ▹[ κ ] A → ▹[ κ ] B
apκ _ f a t = f t (a t)

postulate
  -- An unused tick can be forced away
  force : {A : primLockUniv → Set ℓ} → (∀ κ → ▹[ κ ] (A κ)) → (∀ κ → A κ)
  -- The usual guarded fixpoint and its unfolding
  dfixκ : ∀ κ → (▹[ κ ] A → A) → ▹[ κ ] A
  pfixκ : ∀ κ → (f : ▹[ κ ] A → A) → dfixκ κ f ≡ nextκ κ (f (dfixκ κ f))

fixκ : ∀ κ → (▹[ κ ] A → A) → A
fixκ κ f = f (dfixκ κ f)

{-- COÏNDUCTION --}

_∘▸[_]_ : (Set ℓ → Set ℓ) → ∀ κ → ▹[ κ ] (Set ℓ) → Set ℓ
F ∘▸[ κ ] X = F (▸[ κ ] X)

ν[_]_ : ∀ κ → (Set ℓ → Set ℓ) → Set ℓ
ν[ κ ] F = fixκ κ (F ∘▸[ κ ]_)

module coïn (ℓ : Level)
            (F : Set (ℓ >0) → Set (ℓ >0))
            (fmap : ∀ {A B} → (A → B) → F A → F B)
            (fcomm : {A : primLockUniv → Set (ℓ >0)} → (∀ κ → F (A κ)) → F (∀ κ → A κ)) where

  ν : (Set (ℓ >0) → Set (ℓ >0)) → Set (ℓ >0)
  ν F = ∀ κ → ν[ κ ] F

  inFκ : ∀ {κ} → F (▹[ κ ] (ν[ κ ] F)) → ν[ κ ] F
  inFκ {κ} f = subst (F ∘▸[ κ ]_) (sym (pfixκ κ (F ∘▸[ κ ]_))) f

  outFκ : ∀ {κ} → ν[ κ ] F → F (▹[ κ ] (ν[ κ ] F))
  outFκ {κ} f = subst (F ∘▸[ κ ]_) (pfixκ κ (F ∘▸[ κ ]_)) f

  inF : F (ν F) → ν F
  inF f κ = inFκ (fmap (λ g → nextκ κ (g κ)) f)

  outF : ν F → F (ν F)
  outF f = fmap force (fcomm (λ κ → outFκ (f κ)))

  -- Absolutely no hope of proving this one with fmap, force, comm in the way
  postulate inoutF : ∀ x → inF (outF x) ≡ x

  coit : (A → F A) → A → ν F
  coit f a κ = fixκ κ (λ ▹coit a →
    inFκ (fmap (λ x → apκ κ ▹coit (nextκ κ x)) (f a))) a

  case : (P : ν F → Set) → (∀ t → P (inF t)) → ∀ x → P x
  case P p x = subst P (inoutF x) (p (outF x))

{-- COFIXPOINTS OF GUARDED POLYNOMIAL FUNCTORS --
 -- Banished to the bottom of the file because it was distracting --

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

inP : ℙ A Q (▹ ν′ (ℙ A Q)) → ν′ (ℙ A Q)
inP (a ⟫ p) .shape = a
inP (a ⟫ p) .position q = subst ▸_ (sym (pfix (ℙ _ _ ∘▸_))) (p q)

outP : ν′ (ℙ A Q) → ℙ A Q (▹ ν′ (ℙ A Q))
outP (a ⟫ p) .shape = a
outP (a ⟫ p) .position q = subst ▸_ (pfix (ℙ _ _ ∘▸_)) (p q)

inoutP : (p : ν′ (ℙ A Q)) → inP (outP p) ≡ p
inoutP {A} {Q} (a ⟫ p) = {!   !}

outinP : (p : ℙ A Q (▹ ν′ (ℙ A Q))) → outP (inP p) ≡ p
outinP (a ⟫ p) = {!   !}

coitP : (B → ℙ A Q (▹ B)) → B → ν′ (ℙ A Q)
coitP f = fix (λ ▹coit b → inP (fmapP (ap ▹coit) (f b)))

caseP : (P : ν′ (ℙ A Q) → Set) → (∀ p → P (inP p)) → ∀ p → P p
caseP P pin p = subst P (inoutP p) (pin (outP p))
--}