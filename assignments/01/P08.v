Require Export P07.



(** **** Problem : 2 stars (double_plus) *)

(* See [D.v] for the definition of [double] *)

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. SearchAbout (_+_). rewrite plus_n_Sm. reflexivity.
Qed.

