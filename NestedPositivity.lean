/-*----------------------------------
inductive D : Prop where
  | intro E : D = E → (E → False) → D
----------------------------------*-/

axiom D : Prop
axiom introD (E : Prop) (p : E = D) (h : E → False) : D
axiom matchD (d : D) : ∃ E, (E = D) ∧ (E → False)

theorem notD (d : D) : False :=
  let ⟨E, p, h⟩ := matchD d
  by rw [p] at h; exact h d

theorem d : D := introD D rfl notD

theorem false : False := notD d
