Require Export P03.



(** **** Problem #2 : 1 star (zero_nbeq_plus_1) *)

(* See the base file for the definition of [beq_nat] below. *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

