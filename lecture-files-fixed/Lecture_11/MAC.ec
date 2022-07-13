pragma Goals:printall.

require import AllCore.
require import Distr.
require import List.
require ROM.
require import FSet.
require import SmtMap.

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
  proc queryPRF(m:Mblock): C 
}.

module type AdvPRF(O:PRFOracleT) = {
    proc guess(q:int): bool (* Adv gets max number of queries *)
}.

module PRFOracle:PRFOracleT = {
  var f:Mblock -> C (* either random or "prf k" *)
  var max_q:int
  var num_q:int

  proc queryPRF(m:Mblock) : C = {
      var r;
      if (max_q <= num_q) {
        r <- witness;
      } else {
        num_q <- num_q + 1;
        r <- f m;
      }
      
      return r;
  }
}.

module PRF_Game1(A : AdvPRF) = {
  module A = A(PRFOracle)

  proc main(q0:int) : bool = {
    var k, b;
    k <$ KS.dunifin;
    PRFOracle.f <- prf k;
    PRFOracle.max_q <- q0;
    PRFOracle.num_q <- 0;
    
    b <- A.guess(q0);
    return b;
  }
}.

clone ROM as MyROM with
  type in_t <- Mblock,
  type out_t <- C,
  op dout <- fun (x:Mblock), CTS.dunifin
proof *.

module RO = MyROM.Lazy.LRO.

module PRFOracleRO:PRFOracleT = {
  var max_q:int
  var num_q:int

  proc queryPRF(m): C = {
    var r;
    if (max_q <= num_q) {
      r <- witness;
    } else {
      num_q <- num_q + 1;
      r <- RO.o(m);
    }      
    return r;
  }
}.




module PRF_Game2(A : AdvPRF) = {
  module A = A(PRFOracleRO)

  proc main(q0:int) : bool = {
    var b;
    RO.init();
    PRFOracleRO.max_q <- q0;
    PRFOracleRO.num_q <- 0;
    
    b <- A.guess(q0);
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

module MacOracle:MacOracleT = {
  var k:K
  var max_q:int  (* Max number of queries *)
  var msgLog: Mblock list

  proc query(m:Mblock) : C = {
      var r;
      if (max_q <= size msgLog) {
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

module EF_CMA_Game (A : AdvEFCMA) = {
  module A = A(MacOracle)
  
  proc main (q0:int): bool = {
    var m', t';
    MacOracle.k <$ KS.dunifin;
    MacOracle.max_q <- q0;
    MacOracle.msgLog <- [];
    
    (m',t') <- A.guess ();
    return (! m' \in MacOracle.msgLog) /\ (mac MacOracle.k m' = t');
  }
}.

(*
Comments from old lecture.

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


(* ======================================================================= *)

section. (* This keyword starts a section in which we can fix an
adversary "once and for all", so that we do not need to quantify over
it in each lemma *)

declare module A <: AdvEFCMA{MacOracle,PRFOracle}. 
  (* Here we pick an adversary *)


(* Problem 1: Define an adversary B such that the lemmas same_ora and
step1 below are true. 

(The source code of B must not contain the function "mac" directly,
nor must it access any variables of O directly.) *)



local module B(O:PRFOracleT) = {
  module MacOra:MacOracleT = {
    var max_q:int
    var msgLog: Mblock list

    proc query(m:Mblock) : C = {
    var r;
    if ( max_q <= size msgLog) {
        r <- witness;
      }
      else {
        msgLog <- m :: msgLog;
        r <- O.queryPRF(m);
      }
      
      return r;
    }
  }
 
  module A = A(MacOra)

  (* Be careful to initialize everything correctly (Also MacOra's
    variables).  If you do something wrong, you will get stuck in the
    proof of step1.
    
    Note: In the formulation of lemma step1, I have assumed that the
    max_q for the PRFOracle is one mor than for the MacOracle. Make
    sure to initialize accordingly.
  *)

  proc guess(q:int): bool = { 
    var m', t', t'';
    MacOra.msgLog <- [];
    MacOra.max_q <- q-1;
    (m',t') <- A.guess();

    t'' <- O.queryPRF(m');
    return (! m' \in MacOra.msgLog) /\ (t'' = t'); 
  }
}.
(* #POINTS 3 *)

(* This lemma states that, give same input, the two Mac-oracles behave
the same, and additionally they preserve a specific inveriant I *)

(*  Problem 2: Prove this lemma.

    Hint: You may find the tactic "if" useful, which makes a case
    distinction over the condition of the first statement (assumed to
    be an "if").

    Hint: The lemma should be relatively simple to prove. If you need
    fancy tools, probably your definitions above are incorrect.
*)


local lemma same_ora:
    equiv [ MacOracle.query ~ B(PRFOracle).MacOra.query : 
      ={m} /\
    (* Invariant I: *) (MacOracle.msgLog{1}=B.MacOra.msgLog{2} /\ MacOracle.max_q{1}=B.MacOra.max_q{2}
               /\ (size B.MacOra.msgLog=PRFOracle.num_q /\ B.MacOra.max_q<PRFOracle.max_q){2}
        /\ (PRFOracle.num_q < PRFOracle.max_q){2}
               /\ PRFOracle.f{2}=mac MacOracle.k{1})
      ==> ={res} /\ (MacOracle.msgLog{1}=B.MacOra.msgLog{2} /\ MacOracle.max_q{1}=B.MacOra.max_q{2}
               /\ (size B.MacOra.msgLog=PRFOracle.num_q /\ B.MacOra.max_q<PRFOracle.max_q){2}
        /\ (PRFOracle.num_q < PRFOracle.max_q){2}
               /\ PRFOracle.f{2}=mac MacOracle.k{1}) ].
proc.
if => //.
by auto.
inline *.
auto.
smt.
qed.

(* #POINTS 3 *)


(*  Problem 3: Prove this lemma.

    This one is tricky. If you get stuck on an smt-goal, try
    progress. progress splits your goal into lots of small goals.  Try
    solving each with smt. If one of them is not solvable, that
    probably indicates where the problem lies.

*)


(* This lemma states that the two games behave the same. Note that we
run the second game with one more query. This is because the adversary
B needs to make one extra call to the PRF to check the tag t *)

local lemma step1 &m q:
    0 <= q =>
    Pr[ EF_CMA_Game(A).main(q) @ &m : res ] = Pr [ PRF_Game1(B).main(q+1) @ &m : res].
proof.
move => q_nat.
byequiv => //.
proc.
inline PRF_Game1(B).A.guess.
inline *.
wp.
conseq (_: ={glob A} /\ q0{1}+1=q0{2} /\ 0 <= q0{1}
  ==> ={m',t'} /\ MacOracle.msgLog{1}=B.MacOra.msgLog{2}
      /\ mac MacOracle.k{1}=PRFOracle.f{2}
      /\ PRFOracle.num_q{2} < PRFOracle.max_q{2}). smt.  smt.
call (_: MacOracle.msgLog{1}=B.MacOra.msgLog{2} /\ MacOracle.max_q{1}=B.MacOra.max_q{2}
               /\ (size B.MacOra.msgLog=PRFOracle.num_q /\ B.MacOra.max_q<PRFOracle.max_q){2}
               /\ (PRFOracle.num_q < PRFOracle.max_q){2}
               /\ PRFOracle.f{2}=mac MacOracle.k{1}).
by apply same_ora.
conseq (_: _ ==>
     ={glob A} /\ MacOracle.msgLog{1}=B.MacOra.msgLog{2} /\ MacOracle.max_q{1}=B.MacOra.max_q{2}
               /\ (size B.MacOra.msgLog=PRFOracle.num_q /\ B.MacOra.max_q<PRFOracle.max_q){2}
               /\ (PRFOracle.num_q < PRFOracle.max_q){2}
               /\ PRFOracle.f{2}=mac MacOracle.k{1}).
smt.
wp.
conseq (_: _ ==> ={glob A} /\ MacOracle.k{1} = k{2} /\0 <=  q0{1} /\ q0{1}+1 = q0{2}).
smt.
rnd.
auto.
qed.


(*
TODO: This is carried over to the homework. Probably best to 
leave it out. Discuss about this.
*)

op cardC = CTS.Support.card.

local lemma forge_ro q &m:
    Pr[ PRF_Game2(B).main(q) @ &m : res ]
      <= 1%r/cardC%r.
proof.
  byphoare => //.
  proc.
  inline PRF_Game2(B).A.guess.

  (* TODO: Fix this *)
  seq 7: (PRFOracleRO.num_q < PRFOracleRO.max_q
         /\ dom RO.m = oflist B.MacOra.msgLog) => //.
(* TODO:
- Fix seq-call: make all the probability bounds in the different games correct
- In first half: show invariant holds as postcondition
- In second half: make case distinction over "fresh m'"
- Two elementary proofs
*)
