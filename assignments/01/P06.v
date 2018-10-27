Require Export P05.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. 
   intros. induction n.
   - rewrite plus_O_n. rewrite <- plus_n_O. reflexivity.
   - rewrite plus_Sn_m. rewrite <- plus_n_Sm. rewrite IHn. reflexivity.
Qed.

