Require Export P11.



(** **** Problem #12 : 2 stars (ev_sum) *)
SearchAbout (_+0).
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
intros n m H1 H2.
induction H1.
- simpl. apply H2.
- apply ev_SS. apply IHev.
Qed.

