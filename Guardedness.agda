{-# OPTIONS --guardedness #-}

open import Relation.Binary.PropositionalEquality

data ListF (A : Set) (List : Set) : Set where
  [] : ListF A List
  _∷_ : A → List → ListF A List

record List (A : Set) : Set where
  coinductive
  constructor list
  field observe : ListF A (List A)
  {-# ETA List #-}
open List

case : ∀ {A} (P : List A → Set) → P (list []) → (∀ x l → P l → P (list (x ∷ l))) → ∀ l → P l
case P p[] p∷ l with l .observe in eq
... | [] = subst P (cong list (sym eq)) p[]
... | x ∷ xs = subst P (cong list (sym eq)) (p∷ x xs (case P p[] p∷ xs))

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : Stream A
open Stream

zip : ∀ {A} → (A → A → A) → Stream A → Stream A → Stream A
zip f s t .hd = f (s .hd) (t .hd)
zip f s t .tl = zip f (s .tl) (t .tl)

shuffle : ∀ {A} → (A → A → A) → (A → A → A) → Stream A → Stream A → Stream A
shuffle _*_ _+_ s t .hd = s .hd * t .hd
shuffle _*_ _+_ s t .tl = zip (_+_) (shuffle _*_ _+_ (s .tl) t) (shuffle _*_ _+_ s (t .tl))