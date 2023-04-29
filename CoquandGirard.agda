{-# OPTIONS --type-in-type #-}

open import Data.Empty
open import Data.Product
open import Data.Sum

_≡_ : ∀ {A : Set} → A → A → Set
_≡_ {A} x y = ∀ (P : A → Set) → P x → P y

record Rel : Set where
  constructor mkRel
  field
    A : Set
    rel : A → A → Set
open Rel

_⇒_ : Rel → Rel → Set
(mkRel A R) ⇒ (mkRel B S) = Σ[ f ∈ (A → B) ] (∀ x y → R x y → S (f x) (f y))

refl⇒ : ∀ R → R ⇒ R
refl⇒ (mkRel A R) = (λ x → x) , (λ x y r → r)

D : (R : Rel) → R .A → Set
D (mkRel _ R) x = (∃[ y ] R x y) ⊎ (∃[ y ] R y x)

EMB : Rel → Rel → Set
EMB AR@(mkRel A R) (mkRel B S) =
  (Σ[ f ∈ (A → B) ]
    (∀ x y → D AR x → D AR y → R x y → S (f x) (f y)) ×
    (∃[ b ] (∀ x → D AR x → S (f x) b)))

WF : Rel → Set
WF (mkRel A _<_) = ∀ (Acc : A → Set) → ∀ x → (∀ y → y < x → Acc y) → Acc x

record USN : Set where
  field
    A : Set
    i : Rel → A
    i⇒ : ∀ R S → i R ≡ i S → R ⇒ S
open USN

module BuraliForti
  (A : Set)
  (i : Rel → A)
  (i⇒ : ∀ R S → i R ≡ i S → R ⇒ S) where

  wf : A → Set
  wf x = Σ[ R ∈ Rel ] (x ≡ i R × WF R)

  emb : A → A → Set
  emb x y = Σ[ R ∈ Rel ] Σ[ S ∈ Rel ]
    (x ≡ i R) × (y ≡ i S) × EMB R S

  emb₀ : A → A → Set
  emb₀ x y = emb x y × wf x × wf y

  R₀ : Rel
  R₀ = mkRel A emb₀

  lem1 : WF R₀
  lem1 Acc x acc = acc x ({!   !} , {!   !} , {!   !})

  lem2 : ∀ R → WF R → EMB R R₀
  lem2 R wfR = {!   !} , {!   !} , {!   !} , {!   !}

  lem3 : ∀ R → WF R → EMB R R → ⊥
  lem3 R wfR (f , g , b , h) = {!   !}

  false : ⊥
  false = lem3 R₀ lem1 (lem2 R₀ lem1)

false : ⊥
false = BuraliForti.false
  ((Rel → Set) → Set)
  (λ r x → x r)
  (λ R S p → p (λ x → x (λ T → R ⇒ T)) (refl⇒ R))