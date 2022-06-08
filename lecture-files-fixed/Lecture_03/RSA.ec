require import AllCore.
require import IntDiv.



(* op name args : type = stuff. *)

(* Tuple-access: bla.`1 bla.`2 *)

op E (pk:int*int) m : int = exp m (pk.`1) %% pk.`2.

op D (sk:int*int) c : int = exp c (sk.`1) %% sk.`2.
(*op D' (pk:int*int) (sk:int) c : int = c^sk %% pk.`2.*)

op phi : int -> int.

axiom exp_mul a b c: 0<=b => 0<=c => 
  exp (exp a b) c = exp a (b*c).

axiom exp_mul_mod a b c n: 
  0<=b => 0<=c => 0<n =>
  exp ( (exp a b) %% n) c %% n = (exp a (b*c)) %% n.


axiom fermat a n: 
0<n => (exp a (phi(n))) %% n = 1.

axiom fermat' a b n:
 0<n => b %% phi(n) = 1 => (exp a b) %% n = a.


lemma rsa_correct (pk:int*int) (sk:int*int) m:
    pk.`1 * sk.`1 %% phi (sk.`2) = 1
    => pk.`2 = sk.`2
    =>  0 <= pk.`1
    =>  0 <= sk.`1
    =>  0 < sk.`2 
    => D sk (E pk m) = m.
proof.
  rewrite /D /E.
  move => Hedprod HmatchN pk1pos sk1pos sk2pos.
  rewrite HmatchN.
  rewrite exp_mul_mod => //.
  by apply fermat'.
qed.
