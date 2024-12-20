set_option autoImplicit false
set_option pp.fieldNotation false

inductive Term : Type where
  | 𝒰 : Nat → Term
open Term

inductive Ctxt : Type where
  | nil : Ctxt
  | cons : Ctxt → Term → Ctxt
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons

inductive Eqv : Term → Term → Prop where
  | trans {a b c} :
    Eqv a b →
    Eqv b c →
    ---------
    Eqv a c
  | 𝒰 {a b} :
    a = b →
    ----------------
    Eqv (𝒰 a) (𝒰 b)
infix:40 (priority := 1001) "≈" => Eqv

mutual
inductive Wf : Ctxt → Prop where
  | nil : Wf (⬝)
  | cons {Γ A k} :
    Wf Γ →
    Wt Γ A (𝒰 k) →
    --------------
    Wf (Γ ∷ A)

inductive Wt : Ctxt → Term → Term → Prop where
  | 𝒰 {Γ j k} :
    j < k →
    -----------------
    Wt Γ (𝒰 j) (𝒰 k)
  | conv {Γ A B a k} :
    A ≈ B →
    Wt Γ a A →
    Wt Γ B (𝒰 k) →
    --------------
    Wt Γ a B
end

notation:40 "⊢" Γ:40 => Wf Γ
notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wt Γ a A

theorem wt𝒰Inv {Γ j A 𝒰'} : Γ ⊢ A ∶ 𝒰' → A = 𝒰 j → ∃ k, 𝒰 k ≈ 𝒰' := by
  intro h e; subst e
  -- induction h
  /- 'induction' tactic does not support mutually inductive types,
     the eliminator 'Wt.rec' has multiple motives -/
  cases h with
  | 𝒰 lt => exact ⟨_, Eqv.𝒰 rfl⟩
  | conv e₁ h _ =>
    let ⟨_, e₂⟩ := wt𝒰Inv h rfl
    exact ⟨_, Eqv.trans e₂ e₁⟩
  -- termination_by structural h => h
  /- failed to infer structural recursion:
     Cannot use parameter h:
       unknown constant 'Wt.brecOn' -/
