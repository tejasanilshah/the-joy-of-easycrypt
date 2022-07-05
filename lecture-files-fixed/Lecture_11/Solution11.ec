(* Due: May 16, 2015 *)

(* Search for START to find the actual problem statements *)

pragma Goals:printall.

require import Int.
require import Real.
require import Bool.
require import Option.
require import Distr.
require import ISet.
require import List.
require ROM.

pragma Goals:printall.


type K.
type M. (* messages *)
type Mblock. (* PRF input *)
type C. (* output of PRF and random function *)

axiom Mblockfin: Finite.finite univ<:Mblock>.
axiom Cfin: Finite.finite univ<:C>.
axiom Kfin: Finite.finite univ<:K>.

op unif = FSet.Duni.duni (ISet.Finite.toFSet ISet.univ<:'a>).

(* Definition of PRFs *)

op prf: K -> Mblock -> C.


module type PRFOracleT = {
  proc queryPRF(m:Mblock): C 
}.

module type AdvPRF(O:PRFOracleT) = {
  proc guess(q:int): bool  (* Adv gets max number of queries *)
}.

module PRFOracle:PRFOracleT = {
  var f:Mblock -> C (* either random or "prf k" *)
  var max_q:int
  var num_q:int

  proc queryPRF(m:Mblock) : C = {
      var r;
      if (num_q >= max_q) {
        r = witness;
      } else {
        num_q = num_q + 1;
        r = f m;
      }
      
      return r;
  }
}.

module PRF_Game1(A : AdvPRF) = {
  module A = A(PRFOracle)

  proc main(q0:int) : bool = {
    var k, b;
    k = $ unif;
    PRFOracle.f = prf k;
    PRFOracle.max_q = q0;
    PRFOracle.num_q = 0;
    
    b = A.guess(q0);
    return b;
  }
}.

(* TODO: ROM again *)

clone ROM.Lazy as MyROM with
  type from <- Mblock,
  type to <- C,
  op dsample <- fun (x:Mblock), unif<:C>.

module RO = MyROM.RO.

module PRFOracleRO:PRFOracleT = {
  var max_q:int
  var num_q:int

  proc queryPRF(m): C = {
    var r;
    if (num_q >= max_q) {
      r = witness;
    } else {
      num_q = num_q + 1;
      r = RO.o(m);
    }      
    return r;
  }
}.




module PRF_Game2(A : AdvPRF) = {
  module A = A(PRFOracleRO)

  proc main(q0:int) : bool = {
    var b;
    RO.init();
    PRFOracleRO.max_q = q0;
    PRFOracleRO.num_q = 0;
    
    b = A.guess(q0);
    return b;
  }
}.

(*
axiom PRF (A<:AdvPRF{PRFOracle}) q &m:
  polytime A => poly q =>
  | Pr[PRF_Game1(A).main(q) @ &m : res] - Pr[PRF_Game2(A).main(q) @ &m : res] | <= small.
*)



(* Collision resistance *)

op H : M->Mblock.

module type AdvCR = {
  proc adv() : M*M
}.

module CR(A:AdvCR) = {
  proc main(): bool= {
    var x,x':M;
    (x,x') = A.adv();
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
  var max_q:int (* Max number of queries *)
  var msgLog: Mblock list

  proc query(m:Mblock) : C = {
      var r;
      if (length msgLog >= max_q) {
        r = witness;
      }
      else {
        msgLog = m :: msgLog;
        r = mac k m;
      }
      
      return r;
  }
}.

module type AdvEFCMA (O:MacOracleT) = {
  proc guess() : Mblock*C
}.

module EF_CMA_Game (A : AdvEFCMA) = {
  module A = A(MacOracle)
  
  proc main (q0:int): bool = {
    var m', t';
    MacOracle.k = $ unif;
    MacOracle.max_q = q0;
    MacOracle.msgLog = [];
    
    (m',t') = A.guess();
    return (! mem m' MacOracle.msgLog) /\ (mac MacOracle.k m' = t');
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




section. (* This keyword starts a section in which we can fix an
adversary "once and for all", so that we do not need to quantify over
it in each lemma *)

declare module A : AdvEFCMA{MacOracle,PRFOracle,PRFOracleRO}. 
  (* Here we pick an adversary *)


local module B(O:PRFOracleT) = {
  module MacOra:MacOracleT = {
    var max_q:int
    var msgLog: Mblock list

    proc query(m:Mblock) : C = {
    var r;
    if (length msgLog >= max_q) {
        r = witness;
      }
      else {
        msgLog = m :: msgLog;
        r = O.queryPRF(m);
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
    MacOra.msgLog = [];
    MacOra.max_q = q-1;
    (m',t') = A.guess();

    t'' = O.queryPRF(m');
    return (! mem m' MacOra.msgLog) /\ (t'' = t'); 
  }
}.


(* This lemma states that, give same input, the two Mac-oracles behave
the same, and additionally they preserve a specific inveriant I *)


local lemma same_ora:
    equiv [ MacOracle.query ~ B(PRFOracle).MacOra.query : 
      ={m} /\
    (* Invariant I: *) (MacOracle.msgLog{1}=B.MacOra.msgLog{2} /\ MacOracle.max_q{1}=B.MacOra.max_q{2}
               /\ (length B.MacOra.msgLog=PRFOracle.num_q /\ B.MacOra.max_q<PRFOracle.max_q){2}
               /\ (PRFOracle.num_q < PRFOracle.max_q){2}
               /\ PRFOracle.f{2}=mac MacOracle.k{1})
      ==> ={res} /\ (MacOracle.msgLog{1}=B.MacOra.msgLog{2} /\ MacOracle.max_q{1}=B.MacOra.max_q{2}
               /\ (length B.MacOra.msgLog=PRFOracle.num_q /\ B.MacOra.max_q<PRFOracle.max_q){2}
               /\ (PRFOracle.num_q < PRFOracle.max_q){2}
               /\ PRFOracle.f{2}=mac MacOracle.k{1}) ].
proc.
if => //.
by auto.
inline *.
auto.
timeout 9. smt.
qed.


(* This lemma states that the two games behave the same. Note that we
run the second game with one more query. This is because the adversary
B needs to make one extra call to the PRF to check the tag t *)

local lemma step1 &m q:
    q >= 0 =>
    Pr[ EF_CMA_Game(A).main(q) @ &m : res ] = Pr [ PRF_Game1(B).main(q+1) @ &m : res].
proof.
intros q_nat.
byequiv => //.
proc.
inline *.
wp.
conseq (_: ={glob A} /\ q0{1}+1=q0{2} /\ q0{1} >= 0
  ==> ={m',t'} /\ MacOracle.msgLog{1}=B.MacOra.msgLog{2}
      /\ mac MacOracle.k{1}=PRFOracle.f{2}
      /\ PRFOracle.num_q{2} < PRFOracle.max_q{2}). smt.  progress; smt.
call (_: MacOracle.msgLog{1}=B.MacOra.msgLog{2} /\ MacOracle.max_q{1}=B.MacOra.max_q{2}
               /\ (length B.MacOra.msgLog=PRFOracle.num_q /\ B.MacOra.max_q<PRFOracle.max_q){2}
               /\ (PRFOracle.num_q < PRFOracle.max_q){2}
               /\ PRFOracle.f{2}=mac MacOracle.k{1}).
by apply same_ora.
conseq (_: _ ==>
     ={glob A} /\ MacOracle.msgLog{1}=B.MacOra.msgLog{2} /\ MacOracle.max_q{1}=B.MacOra.max_q{2}
               /\ (length B.MacOra.msgLog=PRFOracle.num_q /\ B.MacOra.max_q<PRFOracle.max_q){2}
               /\ (PRFOracle.num_q < PRFOracle.max_q){2}
               /\ PRFOracle.f{2}=mac MacOracle.k{1}).
smt.
wp.
conseq (_: _ ==> ={glob A} /\ MacOracle.k{1} = k{2} /\ q0{1} >= 0 /\ q0{1}+1 = q0{2}).
progress; smt.
rnd.
auto.
qed.


(* ================= START ================= *)

op cardC = FSet.card (ISet.Finite.toFSet univ<:C>).

(* Some useful lemma *)
lemma cardC_pos: 1%r/cardC%r >= 0%r.
    admit.
qed.

(* Some useful lemma *)
lemma card_pr t': mu unif (fun (y : C) => y = t') = 1%r / cardC%r.
proof.
  rewrite (_: (fun (y : C) => y = t') = (=) t').
    admit. (* apply fun_ext; smt. *)
  rewrite -/mu_x.
  cut H1: mu_x unif t' = 1%r / cardC%r.
    smt.
  smt.
qed.



(* Problem 1:

    Prove the following lemma.

    It states that the invariant (derived in the lecture) that should
    hold before the second half of the game is preserved by
    B(PRFOracleRO).MacOra.query-calls. (I have generalized the
    invariant a bit here.)

    Hint:

    You already know the "if" tactic that splits an if (that must be
    the first statement) into two subgoals.

    Another useful tactic is the "rcondf" tactic.  If you have an "if"
    in line n, and you know the condition of the if will always be
    false, you can use "rcondf n". This will replace the if by it's
    else branch. (E.g., hoare [ c; if (b) c1 else c2 : b=False ==> Q ]
    becomes gives the new subgoal "hoare [ c; c2 : b=False ==> Q ]" as
    well as a goal "hoare [ c : b=False ==> !b ]".)

    Similarly, "rcondf" can be used if you know that the if-condition
    is always true.

*)

local lemma query_inv:
  hoare [ B(PRFOracleRO).MacOra.query : 
            B.MacOra.max_q < PRFOracleRO.max_q
            /\ FMap.dom RO.m = FSet.of_list B.MacOra.msgLog
            /\ length B.MacOra.msgLog <= B.MacOra.max_q         
            /\ PRFOracleRO.num_q = length B.MacOra.msgLog
        ==>
            B.MacOra.max_q < PRFOracleRO.max_q
            /\ FMap.dom RO.m = FSet.of_list B.MacOra.msgLog
            /\ length B.MacOra.msgLog <= B.MacOra.max_q         
            /\ PRFOracleRO.num_q = length B.MacOra.msgLog ].
proof.
    proc.
    inline *.
    if => //.
      auto; smt.
    rcondf 3.
      auto; smt.
    auto.
  progress; smt.
qed.
(* #POINTS 3 *)

(* Problem 2:
   
   Prove the success probabily bound below.

   Reminder: "call (_: I)" applied to a program that ends in an
   adv-call will give you goals of the kind "hoare [ q : I ==> I ]"
   for any function the adversary can call. Use this in combination
   with lemma query_inv.

   Hint: An tactic that you will need is "case". "case (C)" will split
   the current goal into two subgoals, one with assumption "C" and the
   other with assumption "!C". If the current goal is a
   hoare-statement, the assumption C / !C will be added to the
   precondition. Example: "hoare [ c : P ==> Q ]" becomes "hoare [ c :
   P /\ mem m' B.MacOra.msgLog ==> Q]" and "hoare [ c : P /\ ! mem m'
   B.MacOra.msgLog ==> Q]" when using "call (mem m' B.MacOra.msgLog)".

*)

local lemma forge_ro q &m:
    q > 0 =>
    Pr[ PRF_Game2(B).main(q) @ &m : res ]
      <= 1%r/cardC%r.
proof.
  intros q0.
  byphoare (_: q0 > 0) => //.
  proc.
  inline PRF_Game2(B).A.guess.
  seq 7: (true) 1%r (1%r/cardC%r) 0%r _
         (PRFOracleRO.num_q < PRFOracleRO.max_q
            /\ FMap.dom RO.m = FSet.of_list B.MacOra.msgLog) => //.
  
  (* Two subgoals left at this point *)

  (* Invariant is satisfied after first half of game *)
  call (_: B.MacOra.max_q < PRFOracleRO.max_q
            /\ FMap.dom RO.m = FSet.of_list B.MacOra.msgLog
            /\ length B.MacOra.msgLog <= B.MacOra.max_q         
            /\ PRFOracleRO.num_q = length B.MacOra.msgLog).
    by apply query_inv.
    (* #POINTS 1 *) (* -- for the call tactic *)

  inline *; auto; smt.
  (* #POINTS 1 *) (* -- for the first subgoal *)

  (* There should be only one subgoal left at this point *)
  
  (* Proof that winning probability is <= 1/cardC in second half *)
  inline *.
  rcondf 2. (* We don't end up in the "r=witness" branch *)
    auto; smt.

  (* Two cases: m' fresh or m' not fresh *)
  case (mem m' B.MacOra.msgLog).
  
    (* Case: m' not fresh *)
    hoare. auto; smt.
    auto; smt.

    (* Case: m' fresh *)
    rcondt 5. auto; smt. 
    wp.
    conseq (_: _ ==> y=t'). smt.
    rnd (fun y, y=t').
    auto.
    rewrite card_pr.
    smt.
  (* #POINTS 3 *) (* -- for the second subgoal *)
qed.

