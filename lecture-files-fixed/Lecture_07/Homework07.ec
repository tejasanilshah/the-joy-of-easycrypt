(* Due: March 5 *)

pragma Goals:printall.

require import AllCore.
require import Distr.

(* Problem: Prove the lemma "reduction" below. This will finish the
proof from the lecture and show that "g:=f o f" is an OWP.

There are a number of games on the way to be defined (see the
whiteboard from the first lecture) and equivalences between them
stated. However, if you prove "reduction" in some other way, that's
fine, too. (As long as you don't change the definitions of OWP_game,
B, Adv, f, D, or add other axioms, or use admit.)

*)

type D.
clone Distr.MFinite as DD with
  type t <= D.
op f: D->D.
  
abbrev dist = (DD.dunifin).       (* Uniform distribution of type D *)

module type Adv = {
  proc guess(y:D): D
}.


module OWP_game(A:Adv) = {
  proc main(f':D->D) : bool = {
    var x,y,x';
    x  <$ dist;
    y  <- f' x;
    x' <- A.guess(y);
    return x=x';
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

module Game0(A:Adv) = {
  proc main(): bool = {
  var x, y, x';
  x <$ dist;
  y <- g x;
  x' <- A.guess(y);
  return x=x';
  }
}.

module Game1(A:Adv) = {
  proc main(): bool = {
  var x, y, x';
  x <$ dist;
  y <- f (f x);
  x' <- A.guess(y);
  return x=x';
  }
}.

module Game2(A:Adv) = {
  proc main(): bool = {
  var x, y, x', z;
  x <$ dist;
  z <- f x;
  y <- f z;
  x' <- A.guess(y);
  return x=x';
  }
}.

module Game3(A:Adv) = {
  module B = B(A)
  proc main() : bool ={
    var x, x', z : D;
    x <$ dist;
    z <- f x;
    x' <- B.guess(z);
    return x = x';
  }
}.

module Game4(A:Adv) = {
  module B = B(A)
  proc main (): bool = {
    var x, y, z, x' : D;
    x <$ dist;
    y <- f x;
    x'<- B.guess(y);
    return x = x';
  }
}.

(* Equivalence of games 0 and 1.
    (i.e., Pr[...] = Pr[...] or similar) *)
lemma Game0_1 (A<:Adv) &m: Pr[Game0(A).main() @ &m: res] = Pr[Game1(A).main() @ &m : res].
    proof.
byequiv => //.
proc.
call (_: true).
simplify.
auto.
qed.    

lemma Game1_2 (A<:Adv) &m: Pr[Game1(A).main() @ &m: res] = Pr[Game2(A).main() @ &m : res].
    proof.
byequiv => //.
proc.
call (_: true).
simplify.
auto.
qed.    

lemma Game2_3 (A<:Adv) &m: Pr[Game2(A).main() @ &m: res] = Pr[Game3(A).main() @ &m : res].
    proof.
byequiv => //.
proc.
inline *.
wp.
call(_:true).
simplify.
auto.
qed.

lemma Game3_4 (A<:Adv) &m: Pr[Game3(A).main() @ &m: res] = Pr[Game4(A).main() @ &m : res].
    proof.
byequiv => //.
proc.
inline *.
wp.
call(_:true).
simplify.
auto.
qed.

(* Equivalence of OWP_game with g, and Game 0 *)
lemma OWP_game_g_0 (A<:Adv) &m: Pr[OWP_game(A).main(g) @ &m: res] = Pr[Game0(A).main() @ &m : res].
proof.
byequiv => //.
proc.
call(_:true).
auto.
qed.

(* Equivalence of Game 4, and OWP_game with f *)

lemma Game_4_OWP_game_f (A<:Adv) &m: Pr[Game4(A).main() @ &m: res] = Pr[OWP_game(B(A)).main(f) @ &m : res].
    proof.
    byequiv => //.
    proc.
    inline *.
    wp.
    call(_:true).
    auto.
qed.

(* This lemma should be proven in the end *)
lemma reduction (A<:Adv) &m:
    Pr[OWP_game(A).main(g) @ &m : res]
    <= Pr[OWP_game(B(A)).main(f) @ &m : res].
proof.
byequiv => //.
proc.
inline *.
wp.
call(_:true).
auto.
qed.
