(* Due: March 30 *)

pragma Goals:printall.

require import AllCore.
require import Distr.
require DBool. (* We need to require this for the <$ {0,1} syntax to work *)

module type Adv = {
  proc a1(x:int): unit
}.

module M(A:Adv) = {
  proc f1(x:int) : int = { A.a1(x+1); x <- x+1; return x; }
  proc f2(x:int) : int = { x <- x+1; A.a1(x); return x; }
}.

(* Problem 1: Prove the following lemma *)

lemma problem1 (A<:Adv):
    equiv [ M(A).f1 ~ M(A).f2 : ={x,glob A} ==> ={res} ].
proof.
  proc.
  wp.
  call (_: true).
  simplify.
  wp.
  skip.
  smt.
qed.

op dist: int -> int distr.
module M2 = {
  proc f(x1,x2:int) : int = { var y1, y2:int; y1 <$ dist x1; y2 <$ dist x2; return y1+y2; }
}.


(* Many of the tactics that exist for Hoare triples can also be
applied to pRHL (probabilistic relational Hoare logic) to one of the
two programs by adding a side selector. E.g., "swap {1} 1 1" will do
"swap 1 1" on the left program. While "swap {2} 1 1" will do it on the
right one. *)

(* Problem 2: Prove the following lemma 

  Hint: recall that "rnd" works well when the left and right last
  statement are of the form "... <$ d1" and "...<$ d2" where "d1" and
  "d2" are the same distribution. Notice also that "dist x1" and "dist
  x1" on the left and right may not be the same distribution if x1 has
  different values on left and right.

  Note: at least on my computer, smt didn't work for the final
  goal. But "progress; smt." did. So try that.
*)

lemma problem2: 
    equiv [ M2.f ~ M2.f : x1{1}=x2{2} /\ x2{1}=x1{2} ==> ={res} ].
proof.
  proc.
  swap {2} 1 1.
  rnd. rnd.
  auto.
  smt.
qed.

(* Problem 3: Prove the following lemma.

   Hint: You can use problem2 for this. But you will need an
   application of "conseq" to make things match.
*)

lemma problem3 &m x1' x2':
    Pr[M2.f(x1',x2') @ &m : 0 <= res] = Pr[M2.f(x2',x1') @ &m : 0<= res].
    proof.
    byequiv => //.
    conseq (_: x1{1}=x2{2} /\ x2{1}=x1{2} ==> _) => //.
    by apply problem2.

   (* Different proof: Same steps as problem2 *)
   (*
      byequiv => //. 
      proc.
      swap {2} 1 1.
      rnd. rnd.
      auto.
      smt.
   *)    
  qed.

module M4 = {
  proc f():bool = { var x; x <${0,1}; return x; }
  proc g():int = { var i; i <$ witness; return i; }
}.

(* Problem 4: Prove. *)

lemma problem4:
    equiv [M4.f ~ M4.f : true ==> res{1}=res{2}].
proof.
  proc.    
  rnd.
  skip.
  trivial.
qed.

(* Problem 5: Prove. 

   For a pRHL statement, the tactic "rnd" optionally takes two
   arguments f, f1. These arguments specify how the values returned by
   the left distribution and those returned by the right distribution
   are related. For example: if we have the statements x<$d1 and
   x<$d2, and we want to express that whenever d1 returns i, then d2
   returns i+1, then we can write:

   rnd (fun (x:int), x+1) (fun (x:int), x-1).

   That is, the first function maps a d1-output to a d2-output, and
   the second function maps a d2-output to a d1-output.
*)

lemma problem5:
    equiv [M4.f ~ M4.f : true ==> res{1}<>res{2}].
proof.
  proc.    
  rnd (fun (x:bool), !x) (fun (x:bool), !x).
  skip.
  smt.
qed.

type key.
type msg.
type ciph.
op enc: key -> msg -> ciph.
op keygen: key distr.

(* You won't actually need to use those axioms.
   They specify some characteristics of the one-time pad. *)
(* axiom unif k k': mu_x keygen k = mu_x keygen k'. *)

axiom otp: (exists f, forall a b k,
  ( enc k a = enc (f a b k) b
    /\
    f a b (f b a k) = k  )
).

(* Problem 6: Formulate the following as a game (i.e., give a module):

   - b (boolean) is a parameter of the game, i.e., an input to the main function
   - a key k is picked (use "<$keygen")
   - the adversary outputs two messages m0,m1
   - c := enc(k,m) is computed where m is m0 or m1, depending on b
   - the adversary gets c and makes a guess b'
   - the game should return the guess of the adversary

  Note: differently from the cases we saw so far, the adversary module
  will have two procedures.
*)

module type Otp_adv = {
  proc pick_m(): msg
  proc guess(c: ciph) : bool
}.

module Otp_game(A:Otp_adv) = {

  proc main(b) : bool = {
    
    var k, m0, m1, c, b';
    k <$ keygen;
    m0 <- A.pick_m();
    m1 <- A.pick_m();
    c <- enc k (if b then m0 else m1);
    b'<- A.guess(c);
    return b';
  } 
}.

(* Problem 7: State the fact that the probability that the adversary
returns b' for b=true and for b=false is equal (i.e., we have perfect
secrecy). 

Use an "equiv" statement for that. (You can refer to the input b in
the precondition.)

Don't forget to state that the adversary has the same global variables in both cases!

No proof is needed.
*)

(* My attempt *)
(* lemma problem6 (A<:Otp_adv):
    equiv [ Otp_game(A).main(b=true) ~ Otp_game(A).main(b=false) :
    ={glob A} ==> ={res} ]. *)

lemma problem6 (A<:Otp_adv):
equiv [ Otp_game(A).main ~ Otp_game(A).main:
      b{1}=true /\ b{2}=false /\ ={glob A} ==> ={res} ].
    proof.
    admit.    
qed.
