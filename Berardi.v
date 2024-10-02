Require Import Coq.Unicode.Utf8.
From Coq Require Import ssreflect.

(*----------------------------------------------------------------
  We need some impredicative universe 𝒰
  for which the excluded middle holds.
  This file requires -impredicative-set,
  which makes Set impredicative while still allowing
  strong elimination of small inductives in Set.
  We could also use Prop, but it disallows strong elimination.
  Note that strong elimination of large impredicative inductives
  is /always/ inconsistent.
  From here onwards, we refer to types in 𝒰 as propositions.
----------------------------------------------------------------*)
Definition 𝒰 := Set.
Axiom EM : ∀ (A : 𝒰), A + {A → False}.

(*--------------------------------------------------------------
  To show that proof irrelevance holds for /all/ propositions,
  we parametrize this section over an arbitrary proposition
  with two inhabitants.
--------------------------------------------------------------*)
Section Berardi.
Variable P : 𝒰.
Variable p1 : P.
Variable p2 : P.

(* We can use excluded middle to swap from one inhabitant to the other. *)
Definition swap (p : P) :=
  match EM (p = p1) with
  | inleft _ => p2
  | inright _ => p1
  end.

(*------------------------------------------------------
  Treating P as a boolean-like proposition,
  we define a powerset function on X
  using P to discriminate elementhood in the powerset.
------------------------------------------------------*)
Definition ℙ X := X → P.

(*--------------------------------------------------------------------------
  Impredicativity is needed so that a U can be instantiated with U itself.
  There's no need to disable universe checking ith -impredicative-set on.
--------------------------------------------------------------------------*)
(* Unset Universe Checking. *)
Definition U : 𝒰 := ∀ X, ℙ X.
(* Set Universe Checking. *)

(*
  A ⊲ B says that A is a retract of B,
  where usually B is bigger than A,
  and there's 
  if there is a retraction from B to A
  such that
*)
Definition retract (A B : 𝒰) :=
  { g : A → B & { f : B → A & (λ x, g (f x)) = (λ x, x)}}.
Notation "A ⊲ B" := (retract A B) (at level 70).

(*----------------------------------------------------------------------------
  We use excluded middle to show a form of choice, pulling out existentials:
  if ℙ A ⊲ ℙ B → ∃ g, f. g ∘ f = id, then ∃ g, f. ℙ A ⊲ ℙ B → g ∘ f = id.
----------------------------------------------------------------------------*)
Lemma t A B
  : { g : ℙ A → ℙ B & {f : ℙ B → ℙ A & ℙ A ⊲ ℙ B → (λ x, g (f x)) = (λ x, x)}}.
Proof.
  destruct (EM (ℙ A ⊲ ℙ B)) as [(g & f & e) | e].
  * exists g, f. tauto.
  * exists (λ _ x, p1), (λ _ x, p1). contradiction.
Qed.

(* This is a retraction from ℙ U to U. *)
Definition injU : ℙ U → U := λ pu X,
  match t U U, t U X with
  | existT _ _ (existT _ psi _), existT _ phi _ => phi (psi pu)
  end.

(* Given any mapping U → U, it has a fixed point. *)
Definition u f : U := injU (λ x, f (x U x)).
Lemma fixu f : (u f) U (u f) = f ((u f) U (u f)).
Proof.
  unfold u at 1, injU.
  destruct (t U U) as (phi & psi & e).
  have r : ℙ U ⊲ ℙ U.
  exists (λ x, x), (λ x, x); tauto.
  specialize (e r).
  apply (f_equal (λ g, g (λ (x : U), f (x U x)) (u f)) e).
Qed.

(*--------------------------------------------
  Then swap also has a fixed point,
  but it always swaps the elements,
  so it must be that the elements are equal.
--------------------------------------------*)
Lemma irrel : p1 = p2.
Proof.
  have := fixu swap.
  generalize ((u swap) U (u swap)).
  intro p. unfold swap.
  destruct (EM (p = p1)); subst; tauto.
Qed.
End Berardi.

(* Proof irrelevance for all propositions. *)
Definition proof_irrel : ∀ (P : 𝒰) (p1 p2 : P), p1 = p2 := Berardi.irrel.

(*---------------------------------------------------------------------------
  Bool is a two-element "proposition".
  Showing that Bool's inhabitants are distinct requires strong elimination.
  More verbosely, we define a strong mapping {true ↦ True, false ↦ False},
  so that it suffices to show that True = False → False,
  which can be done by transporting I : True across the equality.
---------------------------------------------------------------------------*)
Inductive Bool : 𝒰 := true | false.
Lemma neqBool : true <> false.
Proof. intro e. inversion e. Qed.

Definition contradiction : False := neqBool (proof_irrel Bool true false).