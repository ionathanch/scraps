Inductive Equal (A: Prop) : Prop -> Prop :=
| refl : Equal A A.

(** These axioms correspond to the following inductive definition:
 *  Inductive D : Prop :=
 *  | C : forall (E: Prop) (p: Equal D E), (E -> False) -> D. *)
Axiom D : Prop.
Axiom introD: forall (E: Prop) (p: Equal D E), (E -> False) -> D.
Axiom matchD: forall (E: Prop) (p: Equal D E), D -> (E -> False).

Definition DnotD (d: D): (D -> False) := matchD D (refl D) d.
Definition notD (d: D): False := (DnotD d) d.
Definition isD: D := introD D (refl D) notD.
Definition bottom: False := notD isD.
