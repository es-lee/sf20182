Require Export P08.



(** **** Problem : 3 stars (mult_comm) *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite plus_assoc. reflexivity.
Qed.

