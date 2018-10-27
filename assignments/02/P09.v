Require Export P08.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** **** Problem #9 : 2 stars (In_app_iff) *)
Check In.
Print In.
Lemma In_app_iff : forall A (l:list A) (l':list A) (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
split.
- intros. induction l.
  + simpl in H. simpl. right. apply H.
  + simpl in H. simpl. destruct H. left. left. apply H. apply IHl in H.
  destruct H. left. right. apply H. right. apply H.
- intros. induction l.
  + simpl. simpl in H. destruct H. inversion H. apply H.
  + simpl in H. simpl. destruct H. 
    destruct H. 
      left. apply H.
      right. apply IHl. left. apply H.
      right. apply IHl. right. apply H.
  
Qed.

