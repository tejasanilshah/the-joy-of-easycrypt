require import Int.
require import Real.

pragma Goals:printall.

(* 
   Due: Sunday, Feb 22, 2015

   If possible, call your solution 02-name.ec where name is your first
   name. For each problem, please indicate how long it took you. *)


(* In the following, unless mentioned differently, you may only use
   the following tactics. The tactics in parentheses are allowed, but
   not necessary (we did not discuss them).

  - intros
  - apply
  - rewrite
  - trivial
  - split
  - (cut)
  - (assumption)

  Remember: usually it's a good idea to use "intros" as much as
  possible as the first step of a proof.

*)

op Q : int->bool.
axiom q_axiom: forall x, Q x.

(* Problem 1: Prove the following using q_axiom. *)

lemma problem1:
    forall (x:bool), Q 5.
    move => x.
    apply q_axiom.
qed.

(* Problem 2: Prove the following using q_axiom. *)

lemma problem2: Q 5 /\ Q 6.
proof.
  split.
  apply q_axiom.
  apply q_axiom.
qed.

op g: int -> int.
axiom g_ax: forall x, g x = x+1.

(* Problem 3: Prove the following using g_ax.
   "apply" won't work here. *)

lemma problem3: g (g (g (g (g (g 0))))) = 6.
proof.
by do! rewrite g_ax.
qed.

op R: int->bool.
axiom R_fact: g (g (g (g (g (g 0))))) = 6 => R 17.

(* Problem 4: Prove the following using R_fact. *)

lemma problem4: R 17.
proof.
  rewrite R_fact.
  apply problem3.
qed.

(* Problem 5: Prove the following. This combines a a number of tactics
   we have seen. *)

lemma problem5: 
    forall (f:int->int),
    (forall (x y:int), x <= y => f x <= f y) => 
    6 = f 5 =>
    6 <= f 7.
proof.
move => f H1 H2.
rewrite H2.
rewrite H1.
trivial.
qed.

(* Problem 6: Prove the following. This is almost like the previous,
   but there is a subtle difference.

   Note: "rewrite -name" does the opposite of "rewrite name". That is,
   if "name: A=B", then "rewrite -name" replaces B by A. *)

lemma problem6: 
    forall (f:int->int),
    (forall (x y:int), x <= y => f x <= f y) => 
    f 5 = 6 =>
    6 <= f 7.
proof.
move => f H1 H2.
rewrite -H2.
by rewrite H1.
qed.

(* Problem 7: Prove the following. This is almost like the problem 5
   but there is a subtle difference.

   Note: If there are several places where "rewrite" might rewrite,
   use "rewrite {n} name" to rewrite the n-th occurrence only. E.g.,
   if "name: A=B", then "rewrite {2} name" will change "... A ... A
   ... A ..." into "... A ... B ... A ...". *)

lemma problem7: 
    forall (f:int->int),
    (forall (x y:int), x <= y => f x <= f y) => 
    6 = f 5 =>
    6 <= f 6.
proof.
move => f H1 H2.
rewrite {1} H2.
by rewrite H1.
qed.

(* Problem 8: Prove the following. Use existing lemmas to make the
   proof simpler. *)

lemma problem8: 
    forall (f:int->int),
    (forall (x y:int), x <= y => f x <= f y) => 
    6 = f 5 =>
    6 <= f 7 /\ 6 <= f 6.
proof.
move => f H1 H2.
split.
apply problem6.
assumption.
rewrite H2.
trivial.
apply problem7.
by assumption.
by assumption.
qed.

(* Problem 9: Prove the following. It shows how much of predicate
   logic can be shown using just basic tactics, without needing any
   external lemmas.

   Hint: The following recipe is often helpful for simple tasks:
   - Introduce whatever you can introduce.
   - Use apply/split/rewrite with anything that applies to the current goal.
   - Succeed. *)


lemma problem9 A B C D:
    (A=>B) => (B=>C) => (C=>D) => (A=>D).
proof.
move => AB BC CD H.
apply CD.
apply BC.
apply AB.
by assumption.
qed.
