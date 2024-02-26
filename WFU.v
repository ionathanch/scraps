Import EqNotations.

Unset Universe Checking.
Inductive U : Prop := u (X : Prop) (f : X -> U) : U.
Set Universe Checking.

Definition injU [u1 u2 : U] (p : u1 = u2) :
  match u1, u2 with
  | u X1 f1, u X2 f2 =>
    exists (q : X1 = X2),
      rew [fun Z => Z -> U] q in f1 = f2
  end :=
  rew dependent p in
  match u1 with
  | u _ _ => ex_intro _ eq_refl eq_refl
  end.

Definition loop : U :=
  u U (fun x => x).

Inductive WF : U -> Prop :=
| wf : forall X f, (forall x, WF (f x)) -> WF (u X f).

Fixpoint wfU (u : U) : WF u :=
  match u with
  | u X f => wf X f (fun x => wfU (f x))
  end.

Require Import Coq.Program.Equality.

Lemma nwf' (u : U) (p : u = loop) (wfl : WF u) : False.
Proof.
  dependent induction wfl.
  apply injU in p as [q r].
  simpl in q. subst.
  simpl in r. subst.
  eapply H0. reflexivity.
Qed.

Definition nwf (wfl : WF loop) : False := nwf' loop eq_refl wfl.

Fixpoint nwf'' (wfl : WF loop) : False :=
  match wfl in WF u' return loop = u' -> False with
  | wf _ f h => fun p => let (q , r) := injU p in
    (rew dependent [fun _ q => forall f,
      rew [fun Z => Z -> U] q in (fun x => x) = f
      -> (forall x, WF (f x))
      -> False] q
    in fun _ r =>
      rew [fun f => (forall x, WF (f x)) -> False] r
      in fun h => nwf'' (h loop)) f r h
  end eq_refl.

Definition false : False := nwf (wfU loop).