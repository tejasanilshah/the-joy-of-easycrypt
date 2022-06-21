(* Due: March 15, 2015

Please call your file "04-name.ec" where "name" is your given name in
small letters.

Please indicate the time for each problem.

*)

require import AllCore.
require Distr.

(* I am writing fully qualified names a lot, even when not necessary,
to make it easier for you to find the corresponding theories. *)

type D.
clone Distr.MFinite as DD with
  type t <= D.
op f: D->D.
op invf : D -> D.
axiom cancel1: cancel f invf.
axiom cancel2: cancel invf f.

lemma invf_cancel x: invf (f x) = x. smt. qed.

module OWP_Game = {
  proc adv(y) : D = {
    return invf y;
  }
  proc main() : bool = {
    var x,x',y : D;
    x <$ DD.dunifin;
    y <- f x;
    x' <- adv(y);
    return x=x';
  }
}.

(* Problem 1: Show the following lemma (i.e., that the adversary
   always succeeds). 

   You may need the following tactic: "inline OWP_Game.adv." replaces
   a function call to "OWP_Game.adv" by the body of that function
   (inlining.)

   You are allowed to use all tactics including smt. (But not
   "admit"!)
*)

lemma adv_succ: 
  hoare [ OWP_Game.main : true ==> res=true ].
proof.
proc.
  inline OWP_Game.adv.
wp.
rnd.
skip.
simplify.
move => x dist.
by rewrite invf_cancel.
qed.

require import IntDiv.          (* IntDiv contains the definition for %% *)
require import Distr.
op E (pk:_*_) (m:int) : int = m^(pk.`1) %% (pk.`2).
op D (sk:_*_) (c:int) : int = c^(sk.`1) %% (sk.`2).

(* valid_RSA_keypair pk sk means that pk and sk match. (In particular,
   same N, N is a product of two distinct primes, e*d=1 mod N, etc.)
   The details of that definition are not so important here, thus
   omitted. *)
op valid_RSA_keypair: (int*int) -> (int*int) -> bool.
axiom rsa_correct pk sk m:
  valid_RSA_keypair pk sk =>
  D sk (E pk m) = m %% pk.`2.
axiom same_N pk sk:
  valid_RSA_keypair pk sk =>
  pk.`2 = sk.`2.

(* A distribution over pairs of pairs. It is supposed
  to represent the distribution of matching keypairs.
  You can pick using "(pk,sk) = $keygen;" *)
op keygen: ((int*int)*(int*int)) distr.

axiom keygen_valid pk sk:
  support keygen (pk,sk)  =>
  valid_RSA_keypair pk sk.
(* This variant will help smt below. *)
lemma keygen_valid' pksk:
  support keygen pksk => 
  valid_RSA_keypair pksk.`1 pksk.`2.
    elim pksk.
    move=> pk sk.
    smt.
qed.

(* Problem 2: Write a game that takes one message as an argument,
encrypts it with a random RSA key (using "keygen"), decrypts it, and
checks whether the decryption is correct (mod N) *)
module RSA_Correct = {
  proc main(m:int) : bool = {
    var pk, sk: int*int;
    var c, m':int;
    (pk,sk) <$ keygen;
    c <- E pk m;
    m' <- D sk c;
    return m'= m%%sk.`2;
  }
}.

(* Problem 3: Prove correctness of RSA with as defined by the above
game. That is, show the following: *)

lemma rsa_correct_game:
    hoare [ RSA_Correct.main : true ==> res=true ].
proof.
proc.
auto.
simplify.
move => ? pksk assm.
  rewrite rsa_correct.
  smt.
rewrite (same_N pksk.`1 pksk.`2).
  smt.
trivial.
qed.
    
module M = {
  proc f1(x:int) : int = { return x*x; }
  proc f2(x:int) : int = { x <- x*x; x<- x-x; return x; }
  proc f3(x:int) : int = { x <- 15; return x; }
}.

(* Problem 4: Put in the weakest precondition
   instead of ??? and prove the lemma*)
lemma f1: hoare [ M.f1 : 4 <= x ==> 16 <= res ].
proof.
proc.
skip.
smt.
qed.

(* Problem 5: Put in the weakest precondition
   instead of ??? and prove the lemma*)
lemma f2: hoare [ M.f2 : true ==> res=0 ].
proof.
proc.
wp.
skip.
by simplify.
qed.

(* Problem 6: Put in the weakest precondition
   instead of ??? and prove the lemma*)
lemma f3: hoare [ M.f3 : false ==> res=0 ].
proof.
proc.
auto.
qed.

