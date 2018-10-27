Require Export P04.



(** **** Problem #5 : 1 star (inversion_ex3) *)
Example inversion_ex3 : forall (X : Type) (x y z w : X) (l j : list X),
  x :: y :: l = w :: z :: j ->
  x :: l = z :: j ->
  x = y.
Proof.
intros. inversion H. inversion H0. rewrite <- H2. rewrite <- H5. reflexivity.
Qed.

