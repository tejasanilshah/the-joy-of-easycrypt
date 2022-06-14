require import AllCore.
require FSet.

(*
Due: Mar 22, 2015
*)

(* 

You are allowed to use smt.

*)

pragma Goals:printall.

module M1 = {
  proc f(x:int):int = { x <- x+1; return x+1; }
  proc g():int = { return 15; }
}.

(* Problem 1: Prove the following using the byphoare tactic. *)

lemma problem1 &m p:
    p <= 1%r =>
    Pr[M1.g() @ &m : 0 <= res ] >= p.
proof.
  move => H1.
  byphoare => //.
  by proc.
qed.

(* Problem 2: Prove the following using the byphoare tactic.

   Hint: since we call M1.f with argument x', we have that the local
     variable x will be initialized with x' (and thus be >=0) However,
     you will notice that byphoare produces a phoare-tuple that does
     not have any precondition. Thus when reasoning about the
     phoare-tuple, you cannot use that x>=0. To overcome this, you can
     use the syntax "byphoare (_: bla)" to force byphoare to use "bla"
     as the precondition. (Try also what happens if you use a "wrong"
     precondition, e.g., "byphoare (_: x=20)". It's instructive.)

   Note: you may notice that I used the variable name x' instead of x
     for the all-quantified variable that is passed to M1.f. It is
     allowed to use x here, but in my experience it can lead to a lot
     of confusion. Better keep the variable names separate. (This only
     applies to local variables because global variables need to be
     written with a full path (e.g. M.x) anyway, so no confusion is
     possible.)
*)
lemma problem2 (x':int) &m:
    0<=x' =>
    Pr[M1.f(x') @ &m : 0<= res] >= 1%r/2%r.
proof.
   move => H1.
 byphoare (_: 0<=x') => //.
proc; auto; smt.
move => &m1 H2.
clear H2.
(* Need help here. *)
admit.
qed.

module type Adv2 = {
  proc a():unit
}.

module M2(A:Adv2) = {
  proc f() : int = {
    var x:int;
    x<-5;
    A.a();
    return x;
  }
}.

(* Problem 3: Prove the following lemma.
   
   Note: It would be so much easier if "x=5;" would be the last statement of M2.f().

   Note: And a call to "simplify" can often make things clearer.
*)

lemma problem3 (A<:Adv2): 
  hoare [ M2(A).f : true ==> res=5 ].
proof.
hoare. 
proc.
swap 1.
wp.
trivial.
qed.

module Exp = {
  var x : int
  proc f1() : unit = { x <- x+1; }
  proc f2() : unit = { f1(); f1(); }
  proc f3() : unit = { f2(); f2(); }
  proc f4() : unit = { f2(); f3(); }
  proc f5() : unit = { f4(); f2(); }
  proc f6() : unit = { f5(); f5(); }
  proc f7() : unit = { f6(); f3(); }
  proc f8() : unit = { f6(); f7(); }
  proc f9() : unit = { f8(); f1(); }
  proc f10() : unit = { f3(); f9(); }
  proc f() : unit = { f10(); f10(); x <- x-82; }
}.

(* Problem 4: prove the following lemma *)

lemma lots_of_inlining: hoare [ Exp.f : Exp.x=0 ==> Exp.x=0 ].
proof.
proc.
inline *.
by wp.
qed.

op some_distribution : int distr.

module M5 = {
  proc f() : int = {
    var x : int;
    x <$ some_distribution;
    return x;
  }
}.

(* Problem 5: 

  Apply tactics until there is only the following goal left:

---------------------------
Context : M5.f
Bound   : [>=] 1%r / 2%r

pre = true

(1)  x =$ some_distribution   

post = x = 0
---------------------------

  Hint: Use conseq.

  Note: You cannot prove this lemma. So after reaching the desired
    goal, just use admit. But make sure you close all other goals!

 *)

lemma problem5:
    phoare [ M5.f : true ==> res=res*res ] >= (1%r/2%r).
proof.
proc.
(*Need help here*)
conseq (_:_ ==> true) => //.
admit.
admit.
qed.

(* Axiomatizing a cointoss distribution *)
op cointoss : bool distr.
(* This states that a coin says "true" with probability 1/2 *)
axiom cointoss_true: mu cointoss (fun x => x) = 1%r/2%r.

module M6 = {
  proc f():bool = {
    var x,y : bool;
    x <$ cointoss;
    return x;
  }
}.

(* Problem 6: Prove the following lemma. rnd is your friend. *)

lemma problem6:
    phoare [ M6.f : true ==> res ] = (1%r/2%r).
proof.
proc.
rnd.
simplify.
skip.
simplify.
by apply cointoss_true.
qed.

(* Problem 7: Write the following game in EasyCrypt:

    - b is a uniformly chosen boolean
    - b' is a uniformly chosen boolean
    - c is chosen by the adversary (given input b)
    - the adversary wins if c=b /\ b'

   Note: the adversary should be abstract (i.e., you should not
         specify a specific adversary).

   Note: "{0,1}" is short for "FSet.Duni.duni (ISet.Finite.toFSet ISet.univ<:bool>)"

*)

module type Adv7 = {
  proc adv(b: bool) : bool
}.

module Game7(A:Adv7) = {
  proc main() : bool = {
    var b, b', c: bool;
    b <$ cointoss;
    c <- A.adv(b);
    b'<$ cointoss;
    return c = b /\ b';
  }
}.

(* Problem 8: State the fact that in the game from problem 7, the
   adversary wins with probability at most 3/4 as a lemma (you can use
   admit to "prove" it).
*)

lemma three_quarters &m (A<: Adv7):
    phoare [ Game7(A).main : true ==> res ] = (3%r/4%r).
proof.
proc.
rnd.
simplify.
conseq (_:_ ==> b=true) => //.
(* Need help here*)
admit.
admit.
qed.
