{-
  A reproduction of the proofs that impredicativity + proof-irrelevance + regularity ⇒ nonnormalization
  from "Failure of Normalization in Impredicative Type Theory with Proof-Irrelevant Propositional Equality":
  https://doi.org/10.23638/LMCS-16(2:14)2020
-}

{-# OPTIONS --prop --type-in-type #-}

⊥ : Prop
⊥ = ∀ A → A

{- A "nonnormalizing" chain of definitional equalities hold
   even without an explicit cast operator;
   however, it can be added like in Casting to force reduction
   by defining ω h A = cast (h ⊤ A) δ. -}
module Castless where
  ¬_ : Prop → Prop
  ¬ A = A → ⊥
  
  ⊤ : Prop
  ⊤ = ¬ ⊥
  
  δ : ⊤
  δ z = z ⊤ z
  
  ω : ¬ ∀ A B → A → B
  ω h A = h ⊤ A δ
  
  Ω : ¬ ∀ A B → A → B
  Ω h = δ (ω h)
  -- ω h ⊤ (ω h)
  -- h ⊤ ⊤ δ (ω h)
  -- δ (ω h)

{- Normally, Ω would simply reduce to ω, 
   but if cast ignores the function when
   casting to a definitionally equal type,
   then it could instead reduce directly to δ ω. -}
module Casting where
  ⊤ : Prop
  ⊤ = ∀ A → A → A
  
  δ : ⊤ → ⊤
  δ z = z (⊤ → ⊤) (λ x → x) z
  
  cast : ∀ {A B : Prop} → (A → B) → A → B
  cast h a = h a
  -- cast {A} {A} _ a ▷ a
  
  ω : ⊤
  ω A a = cast (λ _ → a) δ
  
  Ω : ⊤
  Ω = δ ω
  -- ω (⊤ → ⊤) (λ x → x) ω
  -- cast (λ _ → λ x → x) δ ω
  -- δ ω