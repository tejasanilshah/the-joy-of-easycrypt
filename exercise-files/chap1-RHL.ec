pragma Goals: printall.

require import AllCore.

(*
Let us work with Relational Hoare Logic and see how
to handle it in EasyCryt. As usual let us start simple and
define two functions that swap variables.
*)

module Jumbled = {
  proc swap1 (x y: int) : int*int = {
  var z;
  z <- x;
  x <- y;
  y <- z;
  return (x,y);
  }

  proc swap2 (x y: int) : int*int = {
  var z;
  z <- y;
  y <- x;
  x <- z;
  return (x,y);
  }
}.

(*
A couple of things to observe in the definitions.
Firstly, they infact swap variables, however the order in which
they swap them is different.
Secondly, the return type of the functions is a tuple.
Notice the syntax of how it is done. (int*int)

On paper we define hoare quadruples like so:
{P} C1 ~ C2 {Q}
While in EC, we use the following syntax to say the same:
equiv [C1 ~ C2 := P ==> Q]
As with Hoare triples in EC, we access the results of both the programs using the
"res" keyword. The numbers in the curly braces are the identifiers.
So res{1} should be read as result from program 1.
Let us first prove that swap1 is equivalent to itself.
*)
lemma swap1_equiv_swap1:
equiv [Jumbled.swap1 ~  Jumbled.swap1 : x{1}=x{2} /\ y{1}=y{2} ==> res{1} = res{2}].
proof.
proc.
simplify.
auto.
qed.

(*
Let us now prove that both the swap functions are equivalent.
Notice the shorthand that we use for the conditions.
The eagle-eyed readers would've noticed this shorthand in the goals pane
in the previous exercise.
*)

lemma swaps_equivalent:
equiv [Jumbled.swap1 ~  Jumbled.swap2 : ={x, y} ==> ={res}  ].
proof.
proc.
simplify.
(*
Now we have different programs, and the way we work with them is by using similar tactics
that we used for HL. The only difference now is that we have to add identifiers 
to the tactics for them to target specific sides and lines of code.
For instance, for the sake of a demonstration let us use the wp tactic
in an asymmetric way.
*)
wp 1 2.
(*
wp n1 n2: Consumes exactly n1 lines of the first program,
and n2 lines of the second program.
*)
wp 0 1.
wp 0 0.
(* TODO: Strange behaviour (Inconsistent with the manual) *)
skip.
trivial.
qed.

(*
To be fair, the equivalence of swap1 and swap2
is quite easy to prove, let us use the power of auto to
clean up the proof.
*)

lemma swaps_equivalent_clean:
equiv [Jumbled.swap1 ~  Jumbled.swap2 : ={x, y} ==> ={res}  ].
proof.
proc.
auto.
qed.

(*
Now let us take a small detour here and build on the the module types
that we breifly introduced in the execise file of HL.
When working with cryptography, we generally don't know about the
inner workings of an adversary or an oracle.
In order to model these in EC we have the module types.
*)

module type Adv = {
  proc eavesdrop_one(): bool
  proc eavesdrop_two(): bool
}.

(*
By defining the module type Adv, we are instructing EC, that any
concrete module which is of the Adv type has to, at the very least,
implement eavesdrop_one, and eavesdrop_two procedures.
What is interesting is that EC allows us to reason with the
abstract module types as well. For example let us define a module
which expects an Adv as input, and has a procedure called
*)

module Abstract_game(A:Adv) = {
  proc one(): bool = {
      var x;
      x <- A.eavesdrop_one();
      return x;
  }
}.

(*
At this stage, we don't know what A.eavesdrop_one does.
Neither does EC. However, we can still prove certain facts
related to it. Let us take a look at a simple example reflexivity
example to understand how that works.
Notice that we have a new term glob A, in the precondition.
It stands for the global variable of the module A.
So in this next lemma we claim that, if the global state of the A
which is of type Adv is equal at the beginning of the program
then running the same program yields us the same result.
Quite a simple lemma, however the point to note here is
that we haven't defined what the function is.
*)

lemma eavesdrop_reflex(A<:Adv):
equiv [Abstract_game(A).one ~ Abstract_game(A).one : ={glob A} ==> ={res} ].
proof.
proc.
call (_: true).
(*
TODO: How do I explain this?
Manual is a bit messy as usual.
*)
auto.
qed.

(*
However, let us also define a concrete instantiation of Adv,
and reason with it. A is quite basic, and either always returns
true or always returns false.
*)

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
(* auto can replace wp. simplify. trivial  *)
qed.

(*
The point of this detour is that,
when we work with cryptographic proofs we will
be dealing with adversaries both concrete and abstract ones,
and we warming up and getting comfortable with EasyCrypt's
tactics and ways.
*)

(*
Before we move on to other things, let us take a look at
something non-trivial in RHL.
As we discussed earlier, one of the use cases of RHL
is to ensure that compiler optimizations preserve program behaviour.
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

  (*
  As you can observe, the variable x is not affected by the loop,
  hence to save computation, the compiler hoists that line out
  of the scope of the while loop. Like so:
  *)

  proc optimized (x y z: int) : int*int = {
    x <- z + 1;
    while (y < z){
      y <- y + 1;
    }
    return (x,y);
  }
}.

(*
Now let us try to prove the fact that
the behaivour of both the programs is equivalent.
*)
lemma optimization_correct: equiv [Compiler.unoptimized ~  Compiler.optimized : ={x, y ,z} ==> ={res}  ].
proof.
proc.
sp.
simplify.


(* swap {1} (1.2) 1. *)
(* TODO: Help *)

while ( y{1} < z{1} /\ y{2} < z{2}).

(*
TODO: Non-trivial RHL exercises.
*)
