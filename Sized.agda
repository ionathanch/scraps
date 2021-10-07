{-# OPTIONS --sized-types #-}

open import Size

variable
  A : Set

module Forestry where
  data Tree {A : Set} : Set
  data Forest {A : Set} : Set

  data Tree {A} where
    node : A → Forest {A} → Tree
  
  data Forest {A} where
    leaf : Forest
    cons : Tree {A} → Forest {A} → Forest

  travForest : (Tree {A} → Tree {A}) → Forest {A} → Forest {A}
  travForest f leaf = leaf
  -- travForest f (cons (node a forest) rest) = cons (f (node a (travForest f forest))) (travForest f rest)
  travForest f (cons tree rest) with f tree
  ... | node a forest = cons (node a (travForest f forest)) (travForest f rest)

module SimplySizedForestry where
  data Tree {A : Set} : Size → Set
  data Forest {A : Set} : Size → Set

  data Tree {A} where
    node : ∀ {s} → A → Forest {A} s → Tree (↑ s)
  
  data Forest {A} where
    leaf : ∀ {s} → Forest (↑ s)
    cons : ∀ {s} → Tree {A} s → Forest {A} s → Forest (↑ s)

  travForest : ∀ {s} → (∀ {s'} → Tree {A} s' → Tree {A} s') → Forest {A} s → Forest {A} s
  travForest f leaf = leaf
  travForest f (cons tree rest) with f tree
  ... | node a forest = cons (node a (travForest f forest)) (travForest f rest)

module SupSizedForestry where
  data Tree {A : Set} : Size → Set
  data Forest {A : Set} : Size → Set

  data Tree {A} where
    node : ∀ {s} → A → Forest {A} s → Tree (↑ s)
  
  data Forest {A} where
    leaf : ∀ {s} → Forest (↑ s)
    cons : ∀ {st sf} → Tree {A} st → Forest {A} sf → Forest (↑ (st ⊔ˢ sf))
    -- cons : ∀ {st sf} → Tree {A} st → Forest {A} sf → Forest ((↑ st) ⊔ˢ (↑ sf))

  travForest : ∀ {s} → (∀ {s'} → Tree {A} s' → Tree {A} s') → Forest {A} s → Forest {A} s
  travForest f leaf = leaf
  travForest f (cons tree forest) with f tree
  travForest {_} .{↑ ((↑ st) ⊔ˢ sf)} f (cons .{↑ st} {sf} tree forest)
    | (node {st} a forest') = cons (node a (travForest {_} {st} f forest')) (travForest {_} {sf} f forest)

module LtSizedForestry where
  data Tree {A : Set} (s : Size) : Set
  data Forest {A : Set} (s : Size) : Set

  data Tree {A} s where
    node : ∀ {s' : Size< s} → A → Forest {A} s' → Tree s
  
  data Forest {A} s where
    leaf : ∀ {s' : Size< s} → Forest s
    cons : ∀ {s₁ s₂ : Size< s} → Tree {A} s₁ → Forest {A} s₂ → Forest s

  travForest : ∀ {s} → (∀ {s'} → Tree {A} s' → Tree {A} s') → Forest {A} s → Forest {A} s
  travForest f leaf = leaf
  travForest f (cons tree rest) with f tree
  ... | node a forest = cons (node a (travForest f forest)) (travForest f rest)

module False where

  open import Data.Empty

  data _<_ : Size → Size → Set where
    lt : ∀ s → (r : Size< s) → r < s

  data Acc (s : Size) : Set where
    acc : (∀ {r} → r < s → Acc r) → Acc s

  wf : ∀ s → Acc s
  wf s = acc (λ {(lt .s r) → wf r})

  ¬wf∞ : Acc ∞ → ⊥
  ¬wf∞ (acc p) = ¬wf∞ (p (lt ∞ ∞))

  ng : ⊥
  ng = ¬wf∞ (wf ∞)
