Require Export P07.



(** **** Problem #8 : 2 stars (not_implies_our_not) *)

Theorem not_False :
  ~False.
Proof.
  unfold not. intros H. destruct H. Qed.
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.
Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
unfold not. intros. apply H in H0. inversion H0.
Qed.

