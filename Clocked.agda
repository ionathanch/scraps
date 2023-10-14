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
  -- fold/unfold cancellation
  (foldunfold : ∀ {κ} (@tick t : κ) x → fold κ (F ∘▸[ κ ]_) t (unfold κ (F ∘▸[ κ ]_) t x) ≡ x)
  (unfoldfold : ∀ {κ} (@tick t : κ) x → unfold κ (F ∘▸[ κ ]_) t (fold κ (F ∘▸[ κ ]_) t x) ≡ x) where

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

  outinFκ : ∀ {κ} x → outFκ {κ} (inFκ {κ} x) ≡ x
  outinFκ {κ} x =
    let lem = cong (λ f → fmap f x) (funext (λ g → (tickext (λ (@tick t) → unfoldfold t (g t)))))
    in begin
      outFκ (inFκ x)                       ≡⟨ fcomp _ _ x ⟩
      fmap (λ z (@tick t) →
              unfold κ (F ∘▸[ κ ]_) t
                     (fold κ _ t (z t))) x ≡⟨ lem ⟩
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
  terminal′ f κ x = cong inFκ (begin
    _ ≡⟨ fcomp _ _ _ ⟩
    _ ≡⟨ cong (λ g → fmap g (f x))
              (funext (λ a →
                tickext (λ (@tick t) →
                cong (λ g → g a)
                     (sym (pdfixt t))))) ⟩
    _ ∎) where
    h = λ ▹coit a → inFκ (fmap (λ x → ap κ ▹coit (next κ x)) (f a))
    postulate pdfixt : (@tick t : κ) → dfix κ h t ≡ h (dfix κ h)
    -- is this meant to be postulated, with (pdfixt ⋄) computing to refl?

  terminal : ∀ f (x : A) → fmap (coit f) (f x) ≡ outF (coit f x)
  terminal f x = begin
    _ ≡⟨ sym (outinF (fmap (coit f) (f x))) ⟩
    _ ≡⟨ cong outF (funext (λ κ → terminal′ f κ x)) ⟩
    _ ∎