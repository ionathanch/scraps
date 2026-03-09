variable
  {A : Type}
  {P : A → Type}
  {lt : A → A → Prop}

class Reflexive {A : Type} (r : A → A → Prop) where
  refl : ∀ x, r x x

variable [lt_refl : Reflexive lt]

@[reducible]
def f x (h : ∀ y, lt y x → P y) : P x := h x (lt_refl.refl x)

set_option pp.proofs true

def acc_inv x (t : Acc lt x) : ∀ y, lt y x → Acc lt y :=
  match t with
  | Acc.intro _ h => h

def recf {x} (h : ∀ y, lt y x → Acc lt y) :
  Acc.rec (motive := λ x _ ↦ P x) (λ x _ h ↦ f x h) (Acc.intro x h)
  = f x (λ y p ↦ Acc.rec (λ x _ h ↦ f (lt_refl := lt_refl) x h) (h y p))
  := by rfl

def frec {x} (h : ∀ y, lt y x → Acc lt y) :
  f x (λ y p ↦ Acc.rec (λ x _ h ↦ f x h) (h y p))
  = Acc.rec (motive := λ x _ ↦ P x) (λ x _ h ↦ f (lt_refl := lt_refl) x h) (h x (lt_refl.refl x))
  := by rfl
