Require Export P12.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.


Lemma rev_app : forall (l:natlist) (m:nat),
  rev (l ++ [m]) = m::(rev l).
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite snoc_append. rewrite snoc_append. rewrite IHl. reflexivity.
Qed.

  
(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite snoc_append. rewrite rev_app. rewrite IHl. reflexivity.
 Qed.
