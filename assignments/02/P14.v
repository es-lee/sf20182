Require Export P13.



(** **** Problem #14 : 3 stars (exp_match_ex1) *)

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
intros T s re1 re2 [Hm1 | Hm2].
apply MUnionL. apply Hm1.
apply MUnionR. apply Hm2.
Qed.

