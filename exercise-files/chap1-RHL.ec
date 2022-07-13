pragma Goals: printall.

require import AllCore.

module Jumbled = {
  proc exchange1 (x y: int) : int*int = {
  var z;
  z <- x;
  x <- y;
  y <- z;
  return (x,y);
  }

  proc exchange2 (x y: int) : int*int = {
  var z;
  z <- y;
  y <- x;
  x <- z;
  return (x,y);
  }
}.

lemma exchanges_equivalent: equiv [Jumbled.exchange1 ~  Jumbled.exchange2 : ={x, y} ==> ={res}  ].
proof.
proc.
simplify.
wp 2 2.
wp 1 1.
wp.
skip.
trivial.
qed.

(* Introduce the concept of adversary and games *)
module type Adv = {
  proc eavesdrop_one(): bool
  proc eavesdrop_two(): bool
}.

module A : Adv = {
  proc eavesdrop_one() = {
    return true;
  }

  proc eavesdrop_two() = {
    return false;
  }
}.

module Games = {
  proc t(): bool = { var x; x <- A.eavesdrop_one(); return x; }
  proc f(): bool = { var x; x <- A.eavesdrop_two(); return x; }
}.

lemma games_quadruple (A<:Adv): equiv [Games.t ~ Games.f : ={glob A} ==> res{1} <> res{2}].
proof.
proc.
inline *.
wp.
simplify.
trivial.
qed.

(*
As we discussed in the textbook, one of the use cases of RHL
is to ensure that compiler optimizations do not modify program
behaviour.
Let us take a look at an example of this with a simple compiler
optimization called invariant hoisting.
Take a look at the programs defined below.
*)

module Compiler = {
  proc unoptimized (x y z: int) : int*int = {
    while (y < z){
      y <- y + 1;
      x <- z + 1;
    }
    return (x,y);
  }
  proc optimized (x y z: int) : int*int = {
    x <- z + 1;
    while (y < z){
      y <- y + 1;
    }
    return (x,y);
  }
}.

lemma optimization_correct: equiv [Compiler.unoptimized ~  Compiler.optimized : ={x, y ,z} ==> ={res}  ].
proof.
proc.
sp.
simplify.

  (* TODO: Help *)

while ( y{1} < z{1} /\ y{2} < z{2}).
