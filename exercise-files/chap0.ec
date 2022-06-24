(* TODO: In the textbook, include some screenshots with highlights *)

(* TODO: Instructions on how to navigate  *)

require import Int.

(*

Let us start with simple mathematical properties of Integers
and see how we can prove them in EasyCrypt

*)

lemma x_equal (x: int): x = x.
proof.
    trivial.
qed.
    (* Need help *)
    (* The manual doesn't have information about what trivial does. *)

lemma x_plus_equal (x: int): x + 3 = x + 1 + 1 + 1.
proof.
    simplify.
    (* Need help *)
    (* true? Explain what this is *)
    trivial.
qed.

(* ---- Exercise ---- *)

lemma x_minus_equal (x: int): x - 10 = x - 9 - 1.
proof.
admit.
qed.

(* TODO: Write about things that are given to us and explain printing *)
print addzC.

(* Commutativity *)
lemma int_comm (x y: int): x + y = y + x.
proof.
    (* TODO: Write about apply *)
    apply addzC.
qed.

(* ---- Exercise ---- *)

(* Associativity *)
print addzA.

lemma int_assoc (x y z: int): x + (y + z) = (x + y) + z.
proof.
    admit.
qed.

(* TODO: How to look for things *)

(* TODO: Searching *)

(* TODO:  ---- Exercise ---- *)

(* Distributivity *)

lemma int_distr (x y z: int): (x + y) * z = x * z + y * z.
proof.
    search ( * ) (+) (=).
    apply mulzDl.  
qed.


lemma x_pos (x: int): 0 < x => 0 < x+1.
proof.
    move => x_ge0.
    simplify.
    trivial.
    (* Both of those tactics don't work. We need something else here *)
    search (<) (+) (0).

    (* TODO: Write about rewrite *)
    rewrite addz_gt0.
    (* Splits into two goals *)

        (* Goal 1: 0 < x *)
        (*TODO: Explain assumption  *)
        assumption.

        (* Goal 2: 0 < 1 *)
        trivial.
qed.

(* TODO:  ---- Exercise ----  assumption and rewrite *)

(* Let us see some variations *)

lemma int_assoc_rev (x y z: int): x + y + z = x + (y + z).
proof.
    rewrite -addzA.
    simplify.
    trivial.
qed.

(* TODO: Introduce smt. Do all the previous exercises with smt *)

require import AllCore.

pragma Goals: printall.

(* Logs and exponents *)

lemma exp_product (x: real) (a b: int): x^(a*b) = x ^ a ^ b.
proof.
    search (^) (=).
    by apply RField.exprM.
qed.

lemma exp_product2 (x: real) (a b: int): x <> 0%r => x^a * x^b = x^(a + b).
proof.
    move => x_pos.
    search (^) (=).
    (* Need help here *)
    (* It holds even for x=0 so why is there a pre-condition for x <> 0 in this *)
    print  RField.exprD.
    rewrite -RField.exprD.
    assumption.
    trivial.
qed.

(* Logarithm exercises *)
(* TODO: Exercise to get students to op log *)

require import RealExp.

lemma ln_product (a b: real) : 0%r < a  => 0%r < b => ln (a*b) = ln a + ln b.
proof.
    search (ln) (+).
    move => H1 H2.
    by apply lnM.
qed.
    

(* As an exercise try to do it for log *)
(* Intro to functions in EC  *)
lemma log_product (a b x : real): 0%r < a  => 0%r < b => log x (a*b) = log x a + log x b.
proof.
    move => H1 H2.
    (* TODO: Need help here *)
    (* Unfold log? inline log? *)
    smt.
qed.

(* Modulo arithmatic exercises *)
require import IntDiv.

(* Need help here *)
(* How to search for strings in the theories *)
(* Trying to search for "mod" *)

(* This doesn't work for some reason.*)
search (%%).

print modzDm.

lemma mod_add (x y z: int): (x %% z + y %% z) %% z = (x + y) %% z.
proof.
    by apply modzDm.
qed.
