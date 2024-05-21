open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality

data ⊤ {ℓ} : Set ℓ where
  tt : ⊤

data Desc {ℓ} : Set (suc ℓ) where
  End : Desc
  Rec : Desc {ℓ} → Desc
  Arg : (A : Set ℓ) → (A → Desc {ℓ}) → Desc

El : ∀ {ℓ} → Desc {ℓ} → Set ℓ → Set ℓ
El End _ = ⊤
El (Rec D) X = X × El D X
El (Arg A D) X = Σ[ a ∈ A ] El (D a) X

data μ {ℓ} (D : Desc {ℓ}) : Set ℓ where
  init : El D (μ D) → μ D

Hyps : ∀ {ℓ} → (D : Desc {ℓ}) → (X : Set ℓ) → (X → Set ℓ) → (El D X) → Set ℓ
Hyps End _ _ _ = ⊤
Hyps (Rec D) X P (x , d) = P x × Hyps D X P d
Hyps (Arg A D) X P (a , d) = Hyps (D a) X P d

hyps : ∀ {ℓ} → (D : Desc {ℓ}) → (X : Set ℓ) → (P : X → Set ℓ) →
       (∀ x → P x) → (d : El D X) → Hyps D X P d
hyps End _ _ _ _ = tt
hyps (Rec D) X P p (x , d) = p x , hyps D X P p d
hyps (Arg A D) X P p (a , d) = hyps (D a) X P p d

replace : ∀ {ℓ X Y} → (D : Desc {ℓ}) → (dx : El D X) → Hyps D X (λ _ → Y) dx → El D Y
replace End _ _ = tt
replace (Rec D) (_ , d) (y , ys) = y , replace D d ys
replace (Arg A D) (a , d) y = a , replace (D a) d y

{-# TERMINATING #-}
ind : ∀ {ℓ} → (D : Desc {ℓ}) → (P : μ D → Set ℓ) →
      ((d : El D (μ D)) → Hyps D (μ D) P d → P (init d)) →
      (d : μ D) → P d
ind {ℓ} D P ih (init d) = ih d (hyps D (μ D) P (ind D P ih) d)

rec : ∀ {ℓ} → (D : Desc {ℓ}) → (P : Set ℓ) → (El D P → P) → μ D → P
rec D P ih = ind D (λ _ → P) (λ d hs → ih (replace D d hs))