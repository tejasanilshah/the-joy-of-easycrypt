require import Int.

pragma Goals:printall.

lemma square_pos a: 0 <= a*a.
    smt.
qed.

lemma le_refl a: a <= a.
    smt.
qed.

lemma mulMle: forall (x y a: int), 0 <= x <= y => x*(a*a) <= y*(a*a).
    move => x y a H1.
    search (<=)( * ).
    smt.
qed.

lemma mono a: 3*(a*a) <= 5*(a*a).
    
    search ( < ).
    search (<) ( * ) .
    apply mulMle.
    (* 0<=3<=5 *)
    split.
    by trivial.
    move => useless.
    clear useless.
    by trivial.
qed.

print mono.

op P: int -> bool.
op Q: int -> bool.
op f: int -> int.

axiom f_prop x: f x = x+1.

lemma test:
    (forall (x:int), P x => Q (x+1))
  =>
    P 5
  =>
    Q (f 5).
  move =>  PQ_rel P5.
  rewrite f_prop.
  apply PQ_rel.
  apply P5.
qed.



