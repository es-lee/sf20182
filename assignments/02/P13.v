Require Export P12.


(** **** Problem #13 : 3 stars (le_exercises) *)
Print le_S.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
(* intros m n o H1 H2. induction H1. apply H2. inversion H2.
- rewrite H0. apply IHle. apply le_S in H1. rewrite H0 in H1.
apply H1 in IHle. *)

intros m n o H1 H2. revert m H1. induction H2.
- intros. apply H1.
- intros o H3. apply le_S. apply IHle. apply H3.
Qed.
