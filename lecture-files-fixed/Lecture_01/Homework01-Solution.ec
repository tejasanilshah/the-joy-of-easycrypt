require import AllCore.

(* Just to test whether your EasyCrypt (and the external SMT solvers) run correctly:
   The following proof should work. *)
  
lemma test: 1+1=2.
    smt.
qed.

(*
  Problem 1:
  State and prove that for integers x we have (x+x)*x = x*x+x*x.
*)

lemma practice1 (x: int): (x+x)*x = x*x + x*x.
    smt.
qed.

(*
  Problem 2:
  State and prove the associativity of multiplication for the real numbers.
*)

lemma real_assoc (x: real)(y: real)(z: real): (x*y)*z = x*(y*z).
    smt.
  qed.

lemma int_assoc: forall (x: int)(y: int)(z: int), (x*y)*z = x*(y*z).
    smt.
qed.

(*
  Problem 3:
  Show that (x^2)^2 = x*(x*x)*x  (because the rhs looks kind of pretty)
  for integers x.

  Try whether it helps to uncomment the lemma "helper" below!
    *)
    
lemma helper (x:int): x^2 = x*x.
    change (x^(1+1) = x*x).
    search (^).
    print exprS.
    rewrite exprS.
    trivial.
    search (^).
    print expr1.
    rewrite expr1.
    trivial.
  qed.

lemma helper2 (x:int): x * (x * x) = (x * x) * x.
    print int_assoc.
    rewrite -int_assoc.
    trivial.
qed.    
    
lemma problem3 (x: int): (x^2)^2 = x*(x*x)*x.
    rewrite helper.
    rewrite helper.
    rewrite -int_assoc.
    rewrite -int_assoc.
    trivial.
qed.
(*
    Problem 4:
    State Fermat's last theorem.
    (http://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem)
    
    Hint: to "prove" it, use "admit." 
    This is a "cheat-tactic" which can be used to "prove" 
    any goal that cannot be proven.
    It must not be used in the final proof (or in the problems above).
    But it can be very useful while developing a larger proof, 
    to leave some things for later.

    Hint:
    - Implication is written "A => B", e.g., "n>2 => fermat"
    - Inequality is written: "a <> b"
*)

search ( < ).

lemma problem4 (a b c n : int): 
    2<n  => 0<a => 0<b => 0<c =>
    a^n + b^n <> c^n.
    admit.
qed.
