pragma Goals: printall.

require import AllCore.

(*
Let us start small and work with some examples that we saw in the text.
Please pay attention to the syntax of the modules,
and capitalization of some names.
EC expects the first letters of module names,
and module type names to be capitalized.
*)

module Func1 = {
  proc add_1 (x:int) : int = { return x+1; }

  (* 
     proc stands for procedure.
     Since EC is typed, we are required to mention the 
     return type of procedures in the definition.
  *)

  proc add_2 (x: int) : int = {return x+2; }
}.

(*
EC allows us to define concretely defined procedures like we did above.
But since we want to model adversaries about whom we know nothing,
we can also define abstract procedures like an eavesdrop procedure 
of an evil adversary. We don't what the procedure does, but we
do know its return type. We will return to this later when we
start working with cryptographic protocols. But this is
an important fact that we need to keep in mind.

Also notice that now we have a module type and not just a module.
This is because, Evil_adv is a type that we will need to instantiate.

*)

(* TODO: Expand on why it is module type and not just a module *)

module type Evil_adv = {
  proc eavesdrop () : bool
}.

(* 
Let us return to hoare triples and take a look at some triples and
try to prove them in EC.
To declare a hoare triple we use the following syntax
*)

lemma triple1: hoare [ Func1.add_1 : x = 1 ==> res = 2 ].
proof.
proc.
(*
The proc tactic simply fills in the procedures with the
definitions for both abstract and concrete procudures.
*)

(* TODO: Write about skip  *)
skip.
move => &m x.
(* TODO: Write about memory and subst *)
subst.
trivial.
qed.

lemma triple2: hoare [ Func1.add_1 : x = 1 ==> res = 3 ].
proof.
proc.
skip.
move => &m x.
subst.
(* 
Clearly this isn't true.
So to abort a proof, we simply use abort *)
abort.

(* Using some automation *)

module Func2 = {
  proc x_sq (x:int) : int = { return x*x; }
  proc x_0  (x:int) : int = { x <- x*x; x<- x-x; return x; }
  proc f_15 (x:int) : int = { x <- 15; return x; }
}.

lemma triple3: hoare [ Func2.x_sq : 4 <= x ==> 16 <= res ].
proof.
proc.
skip.
smt.
qed.

lemma triple4: hoare [ Func2.x_0 : true ==> res=0 ].
proof.
proc.
wp.
skip.
by simplify.
qed.


lemma triple5: hoare [ Func2.f_15 : false ==> res=0 ].
proof.
proc.
wp.
skip.
auto.
qed.

(* Note about how this triple holds. Absurdity! *)

module Func3 = {

proc exp (x a: int) : int = 
{
  var r;
  r <- 1;
  while (a <> 0){
    r <- r * x;
    a <- a-1;
  }
  return r;
}

}.

lemma exp_correct: hoare [ Func3.exp : x = 10 /\ a = 2 ==> res = 100 ].
proof.
proc.
simplify.
(* TODO: HELP! *)
while (  i <= a /\ r = r * x  ).
wp.
skip.
auto.
smt.
wp.
skip.
admit.
qed.
