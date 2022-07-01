(* Due: May 3, 2015 *)

pragma Goals:printall.

require import AllCore.
require import Bool.
require import Distr.

(* Problem 1:

  Information-theoretically secure PRFs.

  It is possible to make a PRF information-theoretically secure (i.e.,
  against arbitrary, unlimited adversaries) if we make the key large
  enough. Namely, if the key encodes the whole value table of the
  function, then the PRF can be secure. (This is actually relatively
  trivial if you think about it.

  Below, I have adapted the definition of the function "prf" such that
  it takes a function as the key, and returns "k(m)" when you evaluate
  "f(k,m)".

  Prove that this is information-theoretically secure.

  (That does not give us much, of course, but it is useful as a sanity
  check for the definitions.)

*)


type M. (* messages *)
type Mblock. (* PRF input *)
type C. (* output of PRF and random function *)
type K = Mblock -> C.


clone Distr.MFinite as KS with
  type t <= K.

clone Distr.MFinite as MBS with
  type t <= Mblock.

clone Distr.MFinite as CTS with
  type t <= C.

clone Distr.MFinite as MBlockToC with
type t <= Mblock -> C.




(* Definition of PRFs *)

(* This defined "prf k m" to be "k m" *)
op prf (k:K) = k.

module type PRFOracleT = {
  proc query(m:Mblock): C 
}.

module type AdvPRF(O:PRFOracleT) = {
    proc guess(): bool
}.

module PRFOracle:PRFOracleT = {
  var f:Mblock -> C (* either random or "prf k" *)
  var q:int
  var num_q:int

  proc query(m:Mblock) : C = {
      var r;
      if (q <= num_q) {
        r <- witness;
      } else {
        num_q <- num_q + 1;
        r <- f m;
      }
      
      return r;
  }
}.

module Game1(A : AdvPRF) = {
  module A = A(PRFOracle)

  proc main(q0:int) : bool = {
    var k, b;
    k <$ KS.dunifin;
    PRFOracle.f <- prf k;
    PRFOracle.q <- q0;
    PRFOracle.num_q <- 0;
    
    b <- A.guess();
    return b;
  }
}.

module Game2(A : AdvPRF) = {
  module A = A(PRFOracle)

  proc main(q0:int) : bool = {
    var b;
    PRFOracle.f <$ MBlockToC.dunifin;
    PRFOracle.q <- q0;
    PRFOracle.num_q <- 0;
    
    b <- A.guess();
    return b;
  }
}.

(* A hint for the following lemma:

   The "call" tactic (e.g., "call (_:true).") can produce subgoals if
   the adversary may call other procedures. For example, if the
   adversary could (via some module) call M.f(), then call will return
   some subgoals concerning M.f(). This is to be expected, because if
   M.f() behaves differently on the two sides, then A may behave
   differently on the two sides as well.

   In general, whether M.f() behaves the same on both sides may depend
   on the global variables of M. Thus, if you call "call (_:true)" and
   get a subgoal like "equiv [ M.f ~ M.f : true ==> true ]" you will
   be stuck. The precondition does not imply that M.f has the same
   global variables.

   To avoid this problem, call allows you to give an invariant that
   should be maintained throughout the adversary execution. For
   example "call (_: ={glob M})" will give you the subgoal "equiv [
   M.f ~ M.f : ={glob M} ==> ={glob M} ]" instead. This can then be
   proven (e.g., by calling "proc" etc.)

   Use this idea to get the proof of lemma PRF through.

*)

lemma PRF (A<:AdvPRF{PRFOracle}) q &m:
  Pr[Game1(A).main(q) @ &m : res] = Pr[Game2(A).main(q) @ &m : res].
proof.
  byequiv => //.
  proc.
  call (_: ={glob PRFOracle}) => //.
  proc.
  auto.
  auto.
  smt.
qed.
(* #POINTS 3 *)

(* Problem 2.

  Lemma problem2 below is wrong.

  Try to understand out why it does not hold. (E.g., by trying to
  prove it.)

  Then change it so that it becomes true and prove it.

  (The change should preserve the spirit of the lemma. For example,
  changing it to 

  lemma problem2 (A<:A):
    equiv [ M(A).f ~ M(A).f : ={M.x} /\ ={glob A} ==> ={res} ].

  or something equally trivial is not allowed.)


 *)


module type A = {
  proc a() : unit
}.

module M(A:A) = {
  var x : int
  proc f() : int = { x <- x+1; A.a(); return x; }
  proc g() : int = { A.a(); x <-x+1; return x; }
}.

(*
Original:
lemma problem2 (A<:A):
    equiv [ M(A).f ~ M(A).g : ={M.x} /\ ={glob A} ==> ={res} ].
*)

lemma problem2 (A<:A{M}):
    equiv [ M(A).f ~ M(A).g : ={M.x} /\ ={glob A} ==> ={res} ].
proof.
  proc.
  swap {1} 1.
  wp.
  call (_: true).
  auto.
qed.
(* #POINTS 3 *)


(* Problem 3:

   Show that if H is collision resistant, so is "H o H" 

   That is, give the definition of B below and prove lemma cr.
*)

type D.

op H : D->D.
op HH x = H (H x).

module type AdvCR = {
  proc adv() : D*D
}.

module CR_H(A:AdvCR) = {
  proc main(): bool= {
    var x,x':D;
    (x,x') <- A.adv();
    return H x = H x' /\ x<>x';
  }
}.


module CR_HH(A:AdvCR) = {
  proc main(): bool= {
    var x,x':D;
    (x,x') <- A.adv();
    return HH x = HH x' /\ x<>x';
  }
}.

module B(A:AdvCR) = {
  proc adv() : D*D = {
    var x,x';
    (x,x') <- A.adv();
    return (if H x = H x' then (x,x') else (H x, H x'));
  }
}.

lemma cr (A<:AdvCR) &m:
    Pr[CR_HH(A).main() @ &m : res]
    <=
    Pr[CR_H(B(A)).main() @ &m : res].
proof.
  byequiv => //.
  proc.
  inline B(A).adv.
  wp.
  call (_: true).
  auto.
  smt.
qed.
(* #POINTS 4 *)

