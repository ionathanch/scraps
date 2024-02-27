Require Import Coq.Unicode.Utf8_core.

Unset Positivity Checking.
Inductive A : Type := an { _ : (A → Prop) → Prop }.
Set Positivity Checking.

Definition f (p : A → Prop) : A := an (λ q, q = p).

Definition injf [p q] (r : f p = f q) : p = q :=
  match r in _ = an g return g p with
  | eq_refl => eq_refl
  end.

Definition P₀ (x : A) : Prop := ∃ P, x = f P ∧ ¬ (P x).
Definition x₀ : A := f P₀.

Definition notP₀x₀ (P₀x₀ : P₀ x₀) : False :=
  match P₀x₀ with
  | ex_intro _ _ (conj fP₀fP notPx₀) =>
    notPx₀ (match injf fP₀fP with eq_refl => P₀x₀ end)
  end.

Definition false : False :=
  notP₀x₀ (ex_intro _ _ (conj eq_refl notP₀x₀)).