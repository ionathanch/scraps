inductive eq {A : Type} (a : A) : A → Type where
| refl : eq a a

def K (P : eq a a → Type) (d : P eq.refl) : ∀ p, P p
| eq.refl => d

def UIP : ∀ (p : eq a a), eq p eq.refl
| eq.refl => eq.refl
