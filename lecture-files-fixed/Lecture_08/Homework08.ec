(*
  Due: April 19 (Problem 1)
  Due: April 22 (Problems 2 and 3)
*)


pragma Goals:printall.

require import AllCore.
require import Distr.

(* In the previous homework, we showed that if f is an OWP, then g:=f o f is an OWP.

  What happens if we consider OWFs instead (that is, we do not assume
  that the function is a permutation).

  For this, we need to slightly change the security definition of
  one-wayness slightly.  Instead of "x=x'" as the winning condition
  for the adversary, we check whether "f x=f x'".

  I have adapted the game OWF_game (former OWP_game) accordingly below.

  *)

type D.
clone Distr.MFinite as DD with
  type t <= D.
op f: D->D.
  
abbrev dist = (DD.dunifin).       (* Uniform distribution of type D *)

module type Adv = {
  proc guess(y:D): D
}.


module OWF_game(A:Adv) = {
  proc main(f':D->D) : bool = {
    var x,y,x';
    x <$ dist;
    y <- f' x;
    x'<- A.guess(y);
    return f' x=f' x'; (* Changed! *)
  }
}.

module B(A:Adv) = {
  proc guess(z:D) : D = {
    var y, x';
    y <- f(z);
    x'<- A.guess(y);
    return x';
  }
}.

op g = fun x, f (f x).

(* Here is the lemma that we proved for OWPs.
   Does it still hold? *)

lemma reduction (A<:Adv) &m:
    Pr[OWF_game(A).main(g) @ &m : res]
    <= Pr[OWF_game(B(A)).main(f) @ &m : res].
proof.
  byequiv => //.
  proc.
  inline B(A).guess; wp.
  call (_:true).
  auto.
simplify.
  (* Oops! The proof from the last homework does not work any more! *)
  admit.
qed.


(* Can you figure out why the proof didn't work? *)

(* Problem 1:

  Find an example of an OWF f1:D1->D1 such that g1(x):=f1(f1(x)) is not a
  one-way function. 

  Write down the Easycrypt definitions of D1 and f1.

  Hint: One possibility of doing that is to start with a OWF f:D->D
  (like the one axiomatized above), and to construct a OWF
  f1:D*D->D*D from that OWF.

  Note: Since the further problems depend on this one, I will publish
  on Monday only a partial solution that contains the answer to this
  one.  You will then have three more days to solve the remaining
  problems.
    *)

(* Solution:

  If f is a one-way function, then f1(x,y) := (f(y),0) is a one-way
  function. (Namely, if you can break invert f1 on random inputs, the
  first component of your output is a preimage of f(y).)

  Furthermore, f1(f1(x,y)) = f1(f(y),0) = (f(0),0).  Thus f1 is a
  constant function! Hence it cannot be one-way (since any input to f1
  is a preimage of f1(x,y)).

*)

type D1 = D * D.
op null : D.
op f1 (xy:D1) : D1 = (f xy.`2,null).

(* -------------- *)

module type Adv1 = { 
  (* Redefining the adversary type, since we don't use D as the domain any more *)
  proc guess(y:D1): D1
}.

clone Distr.MFinite as DD1 with
  type t <= D1.
abbrev dist1 = (DD1.dunifin).
 
(* Same for the OWF game. *)

module OWF_game1(A:Adv1) = {
  proc main(f':D1->D1) : bool = {
    var x,y,x';
    x <$ dist1;
    y <- f' x;
    x'<- A.guess(y);
    return f' x=f' x';
  }
}.

op g1 x = f1 (f1 x).


(* Problem 2: 
  
  Write an efficient adversary A that breaks the one-wayness of g1.

  (Efficient means that you should not invoke the inverse of f or
  similarly.)

*)

module A : Adv1 = {
  proc guess(y:D1) : D1 = {
    return (witness, witness);
  }
}.

lemma attack &m:
    Pr[OWF_game1(A).main(g1) @ &m : res] >= 1%r.
proof.
  byphoare (_: f'=g1 ==> _) => //.
  proc.
  conseq (_: _ ==> f'=g1). smt.
  call (_:true) => //.
  auto.
  smt.
qed.

(* Problem 3:

  Show that f1 is one-way (if f is). *)

(* I am redefining the game here with f1 and f hardcoded,
respectively. This makes the proof below somewhat easier *)

module OWF_game1'(A:Adv1) = {
  proc main() : bool = {
    var x,y,x';
    x <$ dist1;
    y <- f1 x;
    x'<- A.guess(y);
    return f1 x=f1 x';
  }
}.

module OWF_game'(A:Adv) = {
  proc main() : bool = {
    var x,y,x';
    x <$ dist;
    y <- f x;
    x'<- A.guess(y);
    return f x=f x';
  }
}.


module B1(A:Adv1) : Adv = {
  proc guess(y:D) : D = {
    var x;
    x <- A.guess((y,null));
    return x.`2;
  }
}.

(* This is the lemma you should prove.

If you reach a subgoal of the form:

| pre = ={glob A}
| 
| x =$ dist1                 (1)  x =$ dist                
| 
| post = ={glob A} /\ x{1}.`2 = x{2}

you can just use admit. (This goal is a bit tricky to do with Easycrypt.)

*)

lemma reduction1 (A<:Adv1) &m:
    Pr[OWF_game1'(A).main() @ &m : res]
    <= Pr[OWF_game'(B1(A)).main() @ &m : res].
    proof.
     byequiv => //.
  proc.
  inline B1(A).guess; wp.
  conseq (_: _ ==> ={glob A} /\ x{1}.`2=x{2} /\ x'{1}.`2=x0{2}.`2). smt.
  call (_:true).
  conseq (_: _ ==> ={glob A} /\ x{1}.`2=x{2} /\ y{1}=(y0,null){2}). smt.
  wp.
  conseq (_: ={glob A} ==> ={glob A} /\ x{1}.`2=x{2}). smt. smt.

  admit.
qed.
