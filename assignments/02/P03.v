Require Export P02.



(** **** Problem #3 : 3 stars (map_rev) *)

(* Show that map and rev commute. You may need to define an auxiliary lemma. *)
Lemma mapmul : forall (X Y: Type) (f: X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
intros. induction l1.
- reflexivity.
- simpl. rewrite IHl1. reflexivity.
Qed.
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros. induction l.
- reflexivity.
- simpl. rewrite mapmul. rewrite IHl. reflexivity.
Qed.
