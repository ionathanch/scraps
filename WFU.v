Import EqNotations.
Unset Universe Checking.

Inductive U : Prop := u { X : Prop ; f : X -> U }.

Inductive WF : U -> Prop :=
| wf : forall X f, (forall x, WF (f x)) -> WF (u X f).

Definition loop : U :=
  u U (fun x => x).

Definition invU [u1 u2 : U] (p : u1 = u2) :
  exists (q : u1.(X) = u2.(X)),
    rew [fun Z => Z -> U] q in u1.(f) = u2.(f) :=
  rew dependent p in ex_intro _ eq_refl eq_refl.

Fixpoint nwf' (wfl : WF loop) : False :=
  match wfl in WF u' return loop = u' -> False with
  | wf _ f h => fun p => let (q , r) := invU p in
    (rew dependent [fun _ q => forall f,
      rew [fun Z => Z -> U] q in (fun x => x) = f
      -> (forall x, WF (f x))
      -> False] q
    in fun _ r =>
      rew [fun f => (forall x, WF (f x)) -> False] r
      in fun h => nwf' (h loop)) f r h
  end eq_refl.

Require Import Coq.Program.Equality.
Lemma nwf (u : U) (p : u = loop) (wfl : WF u) : False.
Proof.
  dependent induction wfl.
  apply invU in p as [q r].
  simpl in q. subst.
  simpl in r. subst.
  eapply H0. reflexivity.
Qed.

Fixpoint wfU (u : U) : WF u :=
  match u with
  | u X f => wf X f (fun x => wfU (f x))
  end.

Definition false : False := nwf loop eq_refl (wfU loop).