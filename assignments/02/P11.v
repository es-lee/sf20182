Require Export P10.



(** **** Problem #11 : 3 stars, advanced (not_exists_dist) *)
Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
intros P contra. unfold not in contra. apply contra. right. intros contra2. apply contra.
left. apply contra2.
Qed.

