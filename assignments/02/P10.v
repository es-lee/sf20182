Require Export P09.



(** **** Problem #10 : 4 stars (tr_rev_correct) *)
Lemma app_assoc : forall X (l1 l2 l3 : list X), l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
intros X l1. induction l1.
- simpl. intros. reflexivity.
- simpl. intros. rewrite IHl1. reflexivity.
Qed.

Lemma rev_append_rev : forall X (l1 l2 : list X), rev_append l1 l2 = rev l1 ++ l2.
Proof.
intros. revert l2. induction l1.
- reflexivity.
- intros. simpl. rewrite IHl1. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma tr_rev_correct : forall X l, @tr_rev X l = @rev X l.
Proof.
intros. induction l.
- simpl. reflexivity.
- unfold tr_rev. rewrite rev_append_rev. simpl. rewrite <- app_assoc. simpl. reflexivity.
Qed.

