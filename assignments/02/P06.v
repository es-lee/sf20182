Require Export P05.



Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
intros n X l. revert n. induction l as [| x l'].
- reflexivity.
- simpl. intros. destruct n. 
    + inversion H.
    + simpl. apply IHl'. inversion H. reflexivity.
Qed.

