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

  proc add_2 (x: int) : int = {x<- x + 2; return x; }
}.

(*
EC allows us to define concretely defined procedures like we did above.
But since we want to model adversaries about whom we know nothing,
we can also define abstract procedures like an eavesdrop procedure 
of an evil adversary. We don't know what the procedure does, but we
do know its return type. We will return to this later when we
start working with cryptographic protocols. But this is
an important fact that we need to keep in mind.

Also notice that now we have a module type and not just a module.
This is because, Evil_adv is a type that we will need to instantiate.

*)

module type Evil_adv = {
  proc eavesdrop () : bool
}.

(* 
Let us return to hoare triples and take a look at some triples and
try to prove them in EC.
A triple denoted by {P} C {Q} in theory is expressed as
hoare [C : P ==> Q ] in EC, with the usual definitions.
Additionally, the return value of the program C, is stored in a special 
keyword called res.
*)

lemma triple1: hoare [ Func1.add_1 : x = 1 ==> res = 2].
proof.
(*
When working with hoare logic, or pHL, or pRHL, the goal will be different from
what a goal in ambient logic looks like. We need to start stepping through
the procedure or program that is being reasoned about and change the
preconditions and postconditions according axioms and lemmas that we have.
To make progress here, we first need to tell EC what Func1.add_1 is.
The way to do that is by using the "proc" tactic.
It simply fills in the definitions of the procedures that we define.
*)
proc.

(*
When the goal’s conclusion is a statement judgement whose program is empty,
like we have now the "skip" tactic reduces it to the goal whose conclusion
is the ambient logic formula P => Q,
where P is the original conclusion’s precondition, 
and Q is its postcondition.
*)

skip.

(*
Now we are back in familiar territory, except the fact that
we have an interesting "&hr" lurking in the goal.
This refers to the memory in which the program acts.
When we deal with multiple programs, there is a possibility
that the variables come from different memories. So EC provides us
a different name spaces to deal with them.
To introduce memory into the context we need to prepend "&" to a variable name.
Like so:
*)

move => &m H1.
subst.
(* The "subst" tactic simply substitutes variables *)
trivial.
qed.


lemma triple2: hoare [ Func1.add_2 : x = 1 ==> res = 3 ].
proof.
proc.
(*

Now we have a program which is not empty,
so we can't use the skip tactic directly. 
Thankfully we learnt about postcondition weakening.
Take a look at this proof-tree. Applying the "wp" tactic
computes the weakest precondition that needs to hold by
consuming program statements and replacing the conclusion's
postcondition with the weakest precondition R such that the 
statement judgement consisting of R, the consumed suffix(es) and
the conclusion’s original postcondition holds.

                {x = 1} x:= x+2 {x=3}
          -------------------------------wp
                 {x = 1}     {x+2=3}
          -------------------------------skip
                   x = 1  => x+2=3

  (* TODO: Show it formally once (help) *)
*)
wp.
skip.
move => &m x.
subst.
trivial.
qed.

(* Using some automation *)

(*
We generally don't want to be dealing with the low-level proofs,
so we will be combining Hoare logic with the automated tactics that
we saw previously. One thing to remember is that the automated tactics
work well with ambient logic.
*)
module Func2 = {
  proc x_sq (x:int) : int = { return x*x; }
  proc x_0  (x:int) : int = { x <- x*x; x<- x-x; return x; }
  proc f_15 (x:int) : int = { x <- 15; return x; }
}.

lemma triple3: hoare [ Func2.x_sq : 4 <= x ==> 16 <= res ].
proof.
proc.
skip.
(*
Here this conclusion is trivial for us to understand and prove on paper
however it can be quite hard to do with EC, so we will simply outsource it to smt.
The external provers are quite powerful, and can make our life easier.
*)
smt.
qed.

(*
Now let us look at the special cases that we had in the text.
Namely: {true} C {Q}, and {false} C {Q}.
*)
lemma triple4: hoare [ Func2.x_0 : true ==> res=0 ].
proof.
proc.
wp.
skip.
move => &m T x.
by simplify.
(* Prepending the "by" keyword to a tactic
tries to close the goals by applying trivial
to the result of the tactic, and fails if the goal can't be closed *)
qed.

(*
"by" is called a tactical. Tacticals are commands that can work with
other tactics. We will see more later.
*)

(*
So far so good, that was pretty much what we expected.
However let us take a look at the next lemma. Now we are looking at the triple:
{false} x:=15 {x = 0}.
This shouldn't hold, but watch what happens.
*)

lemma triple5: hoare [ Func2.f_15 : false ==> res=0 ].
proof.
proc.
wp.
skip.
move => _ f.

(*
The underscore essentially is a pattern for introduction 
which tells EC to ignore whatever is in that position.
Here since we have a "forall _" in the goal already, we tell EC to ignore it.
You could also use a "?", to let EC decide what to call the variable being moved
to the assumptions.
*)

(*
Pause here for a moment and ponder about what the goal currently says.
It says that assuming that "false" holds, we want to prove that 15 = 0.
As absurd as it is, we know that "false" is the strongest statement there is.
And we have arrived to a state we say that "false" holds. This would imply that anything and
everything can be derived from false. Hence we can actually "prove" that 15 = 0.
*)
trivial.
qed.

(*
The point to understand here is that we could only do this 
because we moved "false" into the context manually when we used
the "move" tactic. So our math is still consistent and the world hasn't exploded yet.
The way to think about this triple is assuming "false" holds implies that 15 = 0.
*)


module Flip_Exp = {

proc flipper (x: bool) : bool =
{
  var r: bool;
  if (x = true) 
  { r <- false; }
  else
  { r <- true; }
  return r;
}

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

lemma flipper_correct: hoare [ Flip_Exp.flipper : x = true ==> res = false ].
proof.
proc.
(*
When the first statement of the program is an if condition, we can use the
"if" tactic to branch into two different goals with appropriate truth values for
the if condition.
In our case, the goal branches into x = true, and x <> true based, and these
conditions are added to the preconditions.
*)
if.

  (*Goal 1:  x = true *)
  wp.
  auto.
 
  (* If the current goal is a HL, pHL, pRHL statement the "auto" tactic
    uses various program logic tactics in an attempt to reduce the goal
    to a simpler one. Never fails, but may fail to make any progress. *)

  (* Goal 2: x <> true.
  Yields a contradiction in the assumptions.
  we can use some automation to deal with it.
  *)
  wp.
  auto.
  smt.
qed.

(*
Notice the repetition of proof steps in the branches.
This can be reduced by using tacticals.
In order to tell EC to repeated use certain tactics on
resulting goals, we use the ":" tactical.
So, we can simplify the above proof like so:
*)

lemma flipper_correct': hoare [ Flip_Exp.flipper : x = false ==> res = true ].
proof.
proc.
if; wp; auto; smt.
qed.

lemma exp_correct: hoare [ Flip_Exp.exp : x = 10 /\ a = 2 ==> res = 100 ].
proof.
proc.
simplify.
(* TODO HELP! *)
while ().

qed.
