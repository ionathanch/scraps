{-# OPTIONS --guarded --rewriting --confluence-check #-}

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

{-# BUILTIN REWRITE _≡_ #-}

primitive primLockUniv : Set₁

variable
  ℓ ℓ′ : Level
  A B : Set ℓ
  C : A → Set ℓ′

postulate
  tickext : {κ : primLockUniv} {Q : κ → Set ℓ} {f g : (@tick t : κ) → Q t} →
            ((@tick t : κ) → f t ≡ g t) → f ≡ g
  funext : {f g : (x : A) → C x} → (∀ x → f x ≡ g x) → f ≡ g
  funextRefl : {f : (x : A) → C x} → funext {f = f} {g = f} (λ x → refl) ≡ refl
  {-# REWRITE funextRefl #-}

_>0 : Level → Level
ℓ >0 = lsuc lzero ⊔ ℓ

▹[_] : primLockUniv → Set ℓ → Set ℓ
▹[ κ ] A = (@tick t : κ) → A

▸[_] : (κ : primLockUniv) → ▹[ κ ] (Set ℓ) → Set ℓ
▸[ κ ] A = (@tick t : κ) → A t

next : ∀ κ → A → ▹[ κ ] A
next _ a _ = a

ap : ∀ κ {A : (@tick t : κ) → Set ℓ} {B : (@tick t : κ) → A t → Set ℓ′} →
     ((@tick t : κ) → (x : A t) → B t x) → (a : ▸[ κ ] A) → (@tick t : κ) → B t (a t)
ap _ f a t = f t (a t)

postulate
  -- @tick ⋄ : {κ : primLockUniv} → κ
  dfix : ∀ κ → (▹[ κ ] A → A) → ▹[ κ ] A
  pfix : ∀ κ f → (@tick t : κ) → dfix {ℓ} {A} κ f t ≡ f (dfix κ f)
  -- dfix⋄ : ∀ κ f → dfix {ℓ} {A} κ f ⋄ ≡ f (dfix κ f)
  -- {-# REWRITE dfix⋄ #-}
  -- pfix⋄ : ∀ κ f → pfix {ℓ} {A} κ f ⋄ ≡ refl
  -- {-# REWRITE pfix⋄ #-}
  unfold : ∀ κ → (F : ▹[ κ ] (Set ℓ) → Set ℓ) → (@tick t : κ) → dfix κ F t → F (dfix κ F)
  -- unfold κ F t = subst (λ x → x) (pfix κ F t)
  fold : ∀ κ → (F : ▹[ κ ] (Set ℓ) → Set ℓ) → (@tick t : κ) → F (dfix κ F) → dfix κ F t
  -- fold κ F t = subst (λ x → x) (sym (pfix κ F t))
  foldunfold : ∀ {κ} {F : ▹[ κ ] (Set ℓ) → Set ℓ} (@tick t : κ) x → fold κ F t (unfold κ F t x) ≡ x
  -- foldunfold {_} {κ} {F} t x = subst-sym-subst (pfix κ F t)
  unfoldfold : ∀ {κ} {F : ▹[ κ ] (Set ℓ) → Set ℓ} (@tick t : κ) x → unfold κ F t (fold κ F t x) ≡ x
  -- unfoldfold {_} {κ} {F} t x = subst-subst-sym (pfix κ F t)
  {-# REWRITE unfoldfold foldunfold #-}

fix : ∀ κ → (▹[ κ ] A → A) → A
fix κ f = f (dfix κ f)

force : ∀ {P : primLockUniv → Set ℓ} → (∀ κ → ▹[ κ ] (P κ)) → (∀ κ → P κ)
force f κ = f κ {!   !} -- ⋄

_∘▸[_]_ : (Set ℓ → Set ℓ) → ∀ κ → ▹[ κ ] (Set ℓ) → Set ℓ
F ∘▸[ κ ] X = F (▸[ κ ] X)

ν[_]_ : ∀ κ → (Set ℓ → Set ℓ) → Set ℓ
ν[ κ ] F = fix κ (F ∘▸[ κ ]_)

module coïn
  (ℓ : Level)
  (F : Set (ℓ >0) → Set (ℓ >0))
  -- F is a functor and follows functor laws
  (fmap : ∀ {A B} → (A → B) → F A → F B)
  (fid : ∀ {A} (x : F A) → fmap (λ x → x) x ≡ x)
  (fcomp : ∀ {A B C} (g : B → C) (f : A → B) a → fmap g (fmap f a) ≡ fmap (λ a → g (f a)) a)
  -- F commutes with clock quantification and with fmap
  (fcomm : {P : primLockUniv → Set (ℓ >0)} → (∀ κ → F (P κ)) → F (∀ κ → P κ))
  (fmapfcomm : ∀ {P} κ f → fmap (λ g → g κ) (fcomm {P} f) ≡ f κ)
  (fcommfmap : ∀ {P} x → fcomm {P} (λ κ → fmap (λ f → f κ) x) ≡ x)
  (fcommute : ∀ {P Q} (f : ∀ κ → P κ → Q κ) x → fcomm {Q} (λ κ → fmap (f κ) (x κ)) ≡ fmap (λ g κ → f κ (g κ)) (fcomm {P} x))
  where

  ν : (Set (ℓ >0) → Set (ℓ >0)) → Set (ℓ >0)
  ν F = ∀ κ → ν[ κ ] F

  inFκ : ∀ {κ} → F (▹[ κ ] (ν[ κ ] F)) → ν[ κ ] F
  inFκ {κ} f = fmap (ap κ (fold κ (F ∘▸[ κ ]_))) f

  outFκ : ∀ {κ} → ν[ κ ] F → F (▹[ κ ] (ν[ κ ] F))
  outFκ {κ} f = fmap (ap κ (unfold κ (F ∘▸[ κ ]_))) f

  inoutFκ : ∀ {κ} x → inFκ {κ} (outFκ {κ} x) ≡ x
  inoutFκ {κ} x =
    let lem = funext (λ g → tickext (ap κ (foldunfold {F = F ∘▸[ κ ]_}) g))
    in begin
      inFκ (outFκ x)                       ≡⟨ fcomp _ _ x  ⟩
      fmap (λ z (@tick t) →
              fold κ (F ∘▸[ κ ]_) t
                   (unfold κ _ t (z t))) x ≡⟨⟩ -- cong (λ f → fmap f x) lem
      fmap (λ x → x) x                     ≡⟨ fid x ⟩
      x ∎

  outinFκ : ∀ {κ} x → outFκ {κ} (inFκ {κ} x) ≡ x
  outinFκ {κ} x =
    let lem = funext (λ g → (tickext (ap κ (unfoldfold {F = F ∘▸[ κ ]_}) g)))
    in begin
      outFκ (inFκ x)                       ≡⟨ fcomp _ _ x ⟩
      fmap (λ z (@tick t) →
              unfold κ (F ∘▸[ κ ]_) t
                     (fold κ _ t (z t))) x ≡⟨⟩ -- cong (λ f → fmap f x) lem
      fmap (λ x → x) x                     ≡⟨ fid x ⟩
      x ∎

  inF : F (ν F) → ν F
  inF f κ = inFκ (fmap (λ g → next κ (g κ)) f)

  outF : ν F → F (ν F)
  outF f = fmap force (fcomm (λ κ → outFκ (f κ)))

  inoutF : ∀ x → inF (outF x) ≡ x
  inoutF x = funext (λ κ → begin
    inF (outF x) κ                      ≡⟨ fcomp _ _ (outF x) ⟩
    fmap _ (fmap force (fcomm _))       ≡⟨ fcomp _ force (fcomm _) ⟩
    fmap _ (fcomm _)                    ≡⟨ sym (fcomp (ap κ (fold κ (F ∘▸[ κ ]_))) (λ g → g κ) (fcomm _)) ⟩
    fmap _ (fmap (λ g → g κ) (fcomm _)) ≡⟨ cong (fmap _) (fmapfcomm κ (λ κ′ → outFκ (x κ′))) ⟩
    inFκ (outFκ (x κ))                  ≡⟨ inoutFκ (x κ) ⟩
    x κ ∎)

  outinF : ∀ x → outF (inF x) ≡ x
  outinF x = begin
    outF (inF x)                        ≡⟨ cong (λ x → fmap force (fcomm x)) (funext (λ κ → outinFκ (fmap (λ g → next κ (g κ)) x))) ⟩
    fmap force (fcomm (λ κ → fmap _ x)) ≡⟨ cong (λ x → fmap force x) (fcommute (λ κ g → next κ (g κ)) (λ _ → x)) ⟩
    fmap force (fmap _ (fcomm _))       ≡⟨ fcomp _ _ (fcomm (λ _ → x)) ⟩
    fmap _ (fcomm _)                    ≡⟨ sym (fcommute (λ κ g → g κ) (λ _ → x)) ⟩
    fcomm (λ κ → fmap (λ g → g κ) x)    ≡⟨ fcommfmap x ⟩
    x ∎

  case : (P : ν F → Set) → (∀ t → P (inF t)) → ∀ x → P x
  case P p x = subst P (inoutF x) (p (outF x))

  coit : (A → F A) → A → ν F
  coit f a κ = fix κ (λ ▹coit a →
    inFκ (fmap (λ x → ap κ ▹coit (next κ x)) (f a))) a

  {----------------------
  We show that the coalgebra (νF, outF) is terminal
  by proving that the following square commutes:

         coit f
      A -------> νF
      |          |
    f |          | outF
      V          V
     F A -----> F νF
      fmap (coit f)

  It seemed easier to first show that
    inF ∘ fmap (coit f) ∘ f ≡ coit F
  then outF both sides and use outF ∘ inF cancellation.
  ----------------------}

  terminal′ : ∀ f κ (x : A) → inF (fmap (coit f) (f x)) κ ≡ coit f x κ
  terminal′ f κ x =
    let h = λ ▹coit a → inFκ (fmap (λ x → ap κ ▹coit (next κ x)) (f a))
    in cong inFκ (begin
    _ ≡⟨ fcomp _ _ _ ⟩
    _ ≡⟨ cong (λ g → fmap g (f x))
              (funext (λ a →
                tickext (λ (@tick t) →
                  cong (λ g → g a)
                       (sym (pfix κ h t))))) ⟩
    _ ∎)

  terminal : ∀ f (x : A) → fmap (coit f) (f x) ≡ outF (coit f x)
  terminal f x = begin
    _ ≡⟨ sym (outinF (fmap (coit f) (f x))) ⟩
    _ ≡⟨ cong outF (funext (λ κ → terminal′ f κ x)) ⟩
    _ ∎

{---------------------------
  INSTANCES OF COFIXPOINTS
      OF SOME FUNCTORS
---------------------------}

-- 🆕 A computing clock irrelevance axiom
postulate
  -- unquantifying over κlocks
  unκ : (primLockUniv → A) → A
  -- propositional equality for unκ
  punκ : ∀ κ x → unκ {ℓ} {A} x ≡ x κ
  -- definitional equality for unκ
  dunκ : ∀ x → unκ {ℓ} {A} (λ κ → x) ≡ x
  {-# REWRITE dunκ #-}
  -- coherence of punκ with dunκ
  cunκ : ∀ κ x → punκ {ℓ} {A} κ (λ κ → x) ≡ refl
  {-# REWRITE cunκ #-}

-- Polynomial functors
record ℙ (S : Set₁) (P : S → Set₁) (X : Set₁) : Set₁ where
  constructor _⟫_
  field
    shape : S
    position : P shape → X
open ℙ

-- Principle of induction under a clock
postulate
  elim : (S : primLockUniv → Set₁)
         (P : ∀ κ → S κ → Set₁)
         (X : primLockUniv → Set₁)
         (Q : (∀ κ → ℙ (S κ) (P κ) (X κ)) → Set₁) → 
         ((s : ∀ κ → S κ) (p : ∀ κ → P κ (s κ) → X κ) → Q (λ κ → s κ ⟫ p κ)) →
         ∀ p → Q p
  elimred : ∀ S P X Q h s (p : ∀ κ → P κ (s κ) → X κ) → elim S P X Q h (λ κ → s κ ⟫ p κ) ≡ h s p
{-# REWRITE elimred #-}

module poly (S : Set₁) (P : S → Set₁) where
  fmap : (A → B) → ℙ S P A → ℙ S P B
  fmap f (s ⟫ p) .shape = s
  fmap f (s ⟫ p) .position x = f (p x)

  fid : ∀ (x : ℙ S P A) → fmap (λ x → x) x ≡ x
  fid x = refl

  fcomp : ∀ {A B C} (g : B → C) (f : A → B) p → fmap g (fmap f p) ≡ fmap (λ x → g (f x)) p
  fcomp g f p = refl

  fcomm : {X : primLockUniv → Set₁} → (∀ κ → ℙ S P (X κ)) → ℙ S P (∀ κ → X κ)
  fcomm {X} p =
    let s ⟫ f = elim (λ κ → S) (λ κ s → P s) X
                     (λ _ → ℙ (primLockUniv → S) (λ s → ∀ κ → P (s κ)) (∀ κ → X κ))
                     (λ s p → s ⟫ λ b κ → p κ (b κ)) p
    in unκ s ⟫ λ b → f (λ κ → subst P (punκ κ s) b)

  fmapfcomm : ∀ {X} κ f → fmap (λ g → g κ) (fcomm {X} f) ≡ f κ
  fmapfcomm κ f = {!   !}

  fcommfmap : ∀ {X} p → fcomm {X} (λ κ → fmap (λ f → f κ) p) ≡ p
  fcommfmap p = refl

  fcommute : ∀ {X Y} (f : ∀ κ → X κ → Y κ) p → fcomm {Y} (λ κ → fmap (f κ) (p κ)) ≡ fmap (λ g κ → f κ (g κ)) (fcomm {X} p)
  fcommute f p = refl

  open coïn (lsuc lzero) (ℙ S P) fmap fid fcomp fcomm fmapfcomm fcommfmap fcommute public

  -- outF ∘ inF now computes!
  outinF′ : ∀ x → outF (inF x) ≡ x
  outinF′ x = refl

  -- this is stuck on `force` not computing properly
  caseIn : ∀ P p t → case P p (inF t) ≡ p t
  caseIn P p t = {! refl !}

-- Stream functors
record StreamF (D : Set₁) (X : Set₁) : Set₁ where
  constructor _∷_
  field
    hd : D
    tl : X
open StreamF

-- Principle of stream induction under a clock
postulate
  elimStream :
    (D : primLockUniv → Set₁)
    (X : primLockUniv → Set₁)
    (Q : (∀ κ → StreamF (D κ) (X κ)) → Set₁) → 
    ((d : ∀ κ → D κ) (x : ∀ κ → X κ) → Q (λ κ → d κ ∷ x κ)) →
    ∀ s → Q s
  elimStreamRed : ∀ D X Q h d x → elimStream D X Q h (λ κ → d κ ∷ x κ) ≡ h d x
{-# REWRITE elimStreamRed #-}

module stream (D : Set₁) where
  fmap : (A → B) → StreamF D A → StreamF D B
  fmap f s .hd = s .hd
  fmap f s .tl = f (s .tl)

  fid : ∀ (s : StreamF D A) → fmap (λ x → x) s ≡ s
  fid s = refl

  fcomp : ∀ {A B C} (g : B → C) (f : A → B) s → fmap g (fmap f s) ≡ fmap (λ x → g (f x)) s
  fcomp g f s = refl

  fcomm : {X : primLockUniv → Set₁} → (∀ κ → StreamF D (X κ)) → StreamF D (∀ κ → X κ)
  fcomm {X} s =
    let d ∷ x = elimStream (λ κ → D) X (λ _ → StreamF (primLockUniv → D) (∀ κ → X κ)) (_∷_) s
    in unκ d ∷ x

  fmapfcomm : ∀ {X} κ f → fmap (λ g → g κ) (fcomm {X} f) ≡ f κ
  fmapfcomm κ f = cong (λ d → d ∷ f κ .tl) (punκ κ (λ κ → f κ .hd))

  fcommfmap : ∀ {X} s → fcomm {X} (λ κ → fmap (λ f → f κ) s) ≡ s
  fcommfmap s = refl

  fcommute : ∀ {X Y} (f : ∀ κ → X κ → Y κ) s → fcomm {Y} (λ κ → fmap (f κ) (s κ)) ≡ fmap (λ g κ → f κ (g κ)) (fcomm {X} s)
  fcommute f s = refl

  open coïn (lsuc lzero) (StreamF D) fmap fid fcomp fcomm fmapfcomm fcommfmap fcommute public

-- Naturals
data ℕ : Set₁ where
  zero : ℕ
  succ : ℕ → ℕ

-- Induction on naturals under a clock
postulate
  elimℕ : (Q : (primLockUniv → ℕ) → Set₁) → Q (λ κ → zero) → ((n : ∀ κ → ℕ) → Q n → Q (λ κ → succ (n κ))) → ∀ n → Q n
  elimℕz : ∀ Q qz qs → elimℕ Q qz qs (λ κ → zero) ≡ qz
  elimℕs : ∀ Q qz qs n → elimℕ Q qz qs (λ κ → succ (n κ)) ≡ qs n (elimℕ Q qz qs n)
  {-# REWRITE elimℕz elimℕs #-}

ℕκ : (primLockUniv → ℕ) → ℕ
ℕκ = elimℕ (λ _ → ℕ) zero (λ _ → succ)

ℕcomm₁ : ∀ κ n → ℕκ n ≡ n κ
ℕcomm₁ κ = elimℕ (λ n → ℕκ n ≡ n κ) refl (λ _ q → cong succ q)

ℕcomm₂ : ∀ n → ℕκ (λ κ → n) ≡ n
ℕcomm₂ zero = refl
ℕcomm₂ (succ n) = cong succ (ℕcomm₂ n)

open stream ℕ public