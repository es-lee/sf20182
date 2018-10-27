Require Export P14.


(** **** Problem #15 : 3 stars (exp_match_ex1') *)
(* If ss : list (list T) represents a sequence of strings
   s1, ..., sn, then fold app ss [] is the result of concatenating them all together. *)
Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
intros. induction ss.
- simpl. apply MStar0.
- simpl. apply MStarApp.
  + apply H. simpl. left. reflexivity.
  + apply IHss. intros. apply H. simpl. right. apply H0.
Qed.




