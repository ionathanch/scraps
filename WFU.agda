data ⊥ : Set where

{-# NO_UNIVERSE_CHECK #-}
data U : Set where
  u : (X : Set) → (X → U) → U

data WF : U → Set₁ where
  wf : ∀ (X : Set) (f : X → U) → (∀ x → WF (f x)) → WF (u X f)

loop : U
loop = u U (λ x → x)

nwf : WF loop → ⊥
nwf (wf X f h) = nwf (h loop)

wfU : ∀ u → WF u
wfU (u X f) = wf X f (λ x → wfU (f x))

false : ⊥
false = nwf (wfU loop)