op Q:bool.

(*lemma mayuresh: forall (x:'a), (x<>x) = false.
    trivial.
qed. *)

lemma test: Q<>Q => Q=Q.
proof.
 have mayuresh : forall (x:bool), (x<>x) = false.
    trivial.
    rewrite mayuresh.
    trivial.
qed.

