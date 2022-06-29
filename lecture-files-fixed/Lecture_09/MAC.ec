pragma Goals:printall.

require import AllCore.
require import Distr.
require import List.
require import FinType.

type K.
type M. (* messages *)
type Mblock. (* PRF input *)
type C. (* output of PRF and random function *)

clone Distr.MFinite as KS with
  type t <= K.

clone Distr.MFinite as MBS with
  type t <= Mblock.

clone Distr.MFinite as CTS with
  type t <= C.

clone Distr.MFinite as MBlockToC with
type t <= Mblock -> C.

(* 
Here we are axiomatizing the finiteness of multiple things.
First we axiomatize the finiteness of different data-types.
Next, we are axiomatizing the finiteness of the functions that map Mblock -> C.
This is still "cheating". If we didn't want to cheat, we would need to
prove multiple things.
We looked at how we could do this in Lecture 4, however we are trying to learn
how to work with cryptographic protocols so we will proceed with the
axiomatic approach.
*)

(* Definition of PRFs *)

op prf: K -> Mblock -> C.


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
    (* Need help here *)
    PRFOracle.f <$ MBlockToC.dunifin ;
    PRFOracle.q <- q0;
    PRFOracle.num_q <- 0;
    
    b <- A.guess();
    return b;
  }
}.

(*
axiom PRF (A<:AdvPRF{PRFOracle}) q &m:
  polytime A => poly q =>
  | Pr[Game1(A).main(q) @ &m : res] - Pr[Game2(A).main(q) @ &m : res] | <= small.
*)



(* Collision resistance *)

op H : M->Mblock.

module type AdvCR = {
  proc adv() : M*M
}.

module CR(A:AdvCR) = {
  proc main(): bool= {
    var x,x':M;
    (x,x') <- A.adv();
    return H x = H x' /\ x<>x';
  }
}.

(*
axiom H_CR (A<:AdvCR):
  polytime A =>
  Pr[CR(A).main() @ &m : res] <= small.
*)



(* EF-CMA *)

op mac = prf.

module type MacOracleT = {
  proc query(m:Mblock): C 
}.

print List.

module MacOracle:MacOracleT = {
  var k:K
  var q:int
  var msgLog: Mblock list

  proc query(m:Mblock) : C = {
      var r;
      if (q <= size msgLog) {
        r <- witness;
      }
      else {
        msgLog <- m :: msgLog;
        r <- mac k m;
      }
      
      return r;
  }
}.

module type AdvEFCMA (O:MacOracleT) = {
  proc guess () : Mblock*C
}.

print (\in).

print mem.


module EF_CMA_Game (A : AdvEFCMA) = {
  module A = A(MacOracle)
  
  proc main (q0:int): bool = {
    var m', t';
    MacOracle.k <$ KS.dunifin;
    MacOracle.q <- q0;
    MacOracle.msgLog <- [];
    
    (m',t') <- A.guess ();

      (* Need help here *)
    return (! m' \in MacOracle.msgLog) /\ (mac MacOracle.k m' = t');
  }
}.

(*
(* Bad axiom: A may access the global variables of MacOracle!
   (In particular, access the key, or clear msgLog) *)
axiom onetime_EFCMA (A<:AdvEFCMA) q &m:
  q <= 1 =>
  Pr[EF_CMA_Game(A).main(q) @ &m : res] = 0%r.
*)

(* 

A <: T{M}  means:
- A is of type T
- glob A and glob M are disjoint

(glob A = all variables that A's code (incl. subcalls to other non-argument modules) accesses)

Hence the following quantifies over adversaries not accessing the global variables of MacOracle

*)
(*
axiom onetime_EFCMA (A<:AdvEFCMA{MacOracle}) q &m:
  q <= 1 =>
  Pr[EF_CMA_Game(A).main(q) @ &m : res] = 0%r.
*)
(*
axiom EFCMA (A<:AdvEFCMA{MacOracle}) q &m:
  polytime A => poly q =>
  Pr[EF_CMA_Game(A).main(q) @ &m : res] <= small.
*)
