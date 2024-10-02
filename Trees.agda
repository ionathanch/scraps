open import Data.Empty
open import Relation.Binary.PropositionalEquality.Core

{-# NO_UNIVERSE_CHECK #-}
data U : Set where
  mk : (X : Set) → (X → U) → U

loop : U
loop = mk U (λ x → x)

data WF : U → Set₁ where
  wf : ∀ {X f} → (∀ x → WF (f x)) → WF (mk X f)

wfu : (x : U) → WF x
wfu (mk X f) = wf (λ x → wfu (f x))

nwf : WF loop → ⊥
nwf (wf x) = nwf (x loop)

falseWF : ⊥
falseWF = nwf (wfu loop)

regular : U → Set
regular (mk X f) = ∀ x → (f x ≡ mk X f) → ⊥

regU : (x : U) → regular x
regU (mk X f) x p = subst regular p (regU (f x)) x p

nreg : regular loop → ⊥
nreg reg = reg loop refl

falseReg : ⊥
falseReg = nreg (regU loop)