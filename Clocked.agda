{-# OPTIONS --guarded --rewriting #-}

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

{-# BUILTIN REWRITE _≡_ #-}

primitive primLockUniv : Set₁
variable
  ℓ ℓ′ : Level
  A B C : Set ℓ
  P : primLockUniv → Set ℓ

_>0 : Level → Level
ℓ >0 = lsuc lzero ⊔ ℓ

▹[_] : primLockUniv → Set ℓ → Set ℓ
▹[ κ ] A = (@tick t : κ) → A

▸[_] : (κ : primLockUniv) → ▹[ κ ] (Set ℓ) → Set ℓ
▸[ κ ] A = (@tick t : κ) → A t

next : ∀ κ → A → ▹[ κ ] A
next _ a _ = a

ap : ∀ κ → ▹[ κ ] (A → B) → ▹[ κ ] A → ▹[ κ ] B
ap _ f a t = f t (a t)

postulate
  @tick ⋄ : {κ : primLockUniv} → κ
  tickext : {κ : primLockUniv} {A : κ → Set ℓ} {f g : (@tick t : κ) → A t} →
            ((@tick t : κ) → f t ≡ g t) → f ≡ g
  funext : {A : Set ℓ} {B : A → Set ℓ′} {f g : (x : A) → B x} →
           (∀ x → f x ≡ g x) → f ≡ g
  dfix  : ∀ κ → (▹[ κ ] A → A) → ▹[ κ ] A
  pdfix : ∀ κ f → dfix {ℓ} {A} κ f ⋄ ≡ f (dfix κ f)
  unfold  : ∀ κ → (F : ▹[ κ ] (Set ℓ) → Set ℓ) → (@tick t : κ) → dfix κ F t → F (dfix κ F)
  fold    : ∀ κ → (F : ▹[ κ ] (Set ℓ) → Set ℓ) → (@tick t : κ) → F (dfix κ F) → dfix κ F t

{-# REWRITE pdfix #-}

postulate
  punfold : ∀ κ → (F : ▹[ κ ] (Set ℓ) → Set ℓ) → unfold κ F ⋄ ≡ λ x → x
  pfold   : ∀ κ → (F : ▹[ κ ] (Set ℓ) → Set ℓ) → fold   κ F ⋄ ≡ λ x → x

{-# REWRITE punfold pfold #-}

fix : ∀ κ → (▹[ κ ] A → A) → A
fix κ f = f (dfix κ f)

force : (∀ κ → ▹[ κ ] (P κ)) → (∀ κ → P κ)
force f κ = f κ ⋄

_∘▸[_]_ : (Set ℓ → Set ℓ) → ∀ κ → ▹[ κ ] (Set ℓ) → Set ℓ
F ∘▸[ κ ] X = F (▸[ κ ] X)

ν[_]_ : ∀ κ → (Set ℓ → Set ℓ) → Set ℓ
ν[ κ ] F = fix κ (F ∘▸[ κ ]_)

-- We suppose an F such that:
-- * F is a functor
-- * F commutes with clock quantification
-- * η for guarded F holds (bisimilarity?)
module coïn (ℓ : Level)
            (F : Set (ℓ >0) → Set (ℓ >0))
            (fmap : ∀ {A B} → (A → B) → F A → F B)
            (fid : ∀ {A} (x : F A) → fmap (λ x → x) x ≡ x)
            (fcomp : ∀ {A B C} (g : B → C) (f : A → B) a → fmap g (fmap f a) ≡ fmap (λ a → g (f a)) a)
            (fcomm : {P : primLockUniv → Set (ℓ >0)} → (∀ κ → F (P κ)) → F (∀ κ → P κ))
            (fcommκ : ∀ {P} κ f → fmap (λ g → g κ) (fcomm {P} f) ≡ f κ)
            (foldunfold : ∀ {κ} (@tick t : κ) x → fold κ (F ∘▸[ κ ]_) t (unfold κ (F ∘▸[ κ ]_) t x) ≡ x) where

  ν : (Set (ℓ >0) → Set (ℓ >0)) → Set (ℓ >0)
  ν F = ∀ κ → ν[ κ ] F

  inFκ : ∀ {κ} → F (▹[ κ ] (ν[ κ ] F)) → ν[ κ ] F
  inFκ {κ} f = fmap (λ g (@tick t) → fold κ (F ∘▸[ κ ]_) t (g t)) f

  outFκ : ∀ {κ} → ν[ κ ] F → F (▹[ κ ] (ν[ κ ] F))
  outFκ {κ} f = fmap (λ g (@tick t) → unfold κ (F ∘▸[ κ ]_) t (g t)) f

  inoutFκ : ∀ {κ} x → inFκ {κ} (outFκ {κ} x) ≡ x
  inoutFκ {κ} x =
    let lem = cong (λ f → fmap f x) (funext (λ g → tickext (λ (@tick t) → foldunfold t (g t))))
    in begin
      inFκ (outFκ x)                       ≡⟨ fcomp _ _ x  ⟩
      fmap (λ z (@tick t) →
              fold κ (F ∘▸[ κ ]_) t
                   (unfold κ _ t (z t))) x ≡⟨ lem ⟩
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
    fmap _ (fcomm _)                    ≡⟨ sym (fcomp (λ g (@tick t) → fold κ (F ∘▸[ κ ]_) t (g t)) (λ g → g κ) (fcomm _)) ⟩
    fmap _ (fmap (λ g → g κ) (fcomm _)) ≡⟨ cong (fmap _) (fcommκ κ (λ κ′ → outFκ (x κ′))) ⟩
    inFκ (outFκ (x κ))                  ≡⟨ inoutFκ (x κ) ⟩
    x κ ∎)

  coit : (A → F A) → A → ν F
  coit f a κ = fix κ (λ ▹coit a →
    inFκ (fmap (λ x → ap κ ▹coit (next κ x)) (f a))) a

  case : (P : ν F → Set) → (∀ t → P (inF t)) → ∀ x → P x
  case P p x = subst P (inoutF x) (p (outF x))