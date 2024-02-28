Set Printing Universes.
Set Universe Polymorphism.

Inductive Empty.

Definition P (S : Type) : Type := S -> Type.

Definition U : Type := 
 forall (x : Type), ((P (P x)) -> x) -> (P (P x)).

Definition tau (t : P (P U)) : U :=
  fun x f p => t (fun s => p (f (s x f))).

Definition sigma (s : U) : P (P U) := s U tau.

Definition Delta (y : U) : Type :=
  (forall (p : P U), sigma y p -> p (tau (sigma y))) -> Empty.

Definition Omega : U :=
  tau (fun p => forall (x : U), sigma x p -> p x).

Definition M (x : U) (two : sigma x Delta) : Delta x :=
  fun three => three Delta two (fun p => three (fun y => p (tau (sigma y)))).

Fail Definition R (p : P U) (one : forall x, sigma x p -> p x) : p Omega :=
  one Omega (fun x => one (tau (sigma x))).

Fail Definition L (zero : forall p, (forall x, sigma x p -> p x) -> p Omega) : Empty :=
  zero Delta M (fun p => zero (fun y => p (tau (sigma y)))).

(* Definition loop : Empty := L R. *)