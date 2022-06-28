(* 
Welcome to Proof-General, the front-end the we use to work with EasyCrypt (EC).
Proof-General itself is based on Emacs, so most of the standard Emacs keybindings
work as well.
All commands begin either with the CONTROL key, denoted by "C", 
or the META or ALT key denoted by "M".
So if you see "C-c C-n" it simply means: CONTROL + c and then CONTROL + n.
Go ahead, try it. This will evaluate the current comment and
place a black dot on the left margin at the beginning of the next one.
*)

(*
The black dot denotes the point until which EC has already evaluated the script.
Most formal proofs are written interactively.
The proof-assistant, EC in our case, will keep track of the goals
(context, and conclusions) for us.
The front-end, Proof-General + Emacs in our case, will show us the 
goals and messages from the assistant, in the "goals" pane, and "response" pane 
on the right.
Our objective is to use different tactics to prove or "discharge" the goal.
Since we only have comments so far there are no goals for EC to work with.
We will change that in a short while.
*)

(*
Here is a short list of keystrokes that will come in handy for this file:
1. C-c C-n :  Evaluate next line or block of code 
2. C-c C-u :  Go back one line or block of code
3. C-c C-ENTER: Evaluate until the cursor position
4. C-c C-l: To reset the Proof-General layout
5. C-x C-s: Save file
6. C-x C-c: Exit Emacs (read the prompt at the bottom of the screen)
*)

(*
EC has a typed expression language, so everything we declare
should either explicitly have a type or it should be inferable
from the operators that are used.
To begin with let us import the built-in Integer theory file.
*)

require import Int.

(* The pragma line simply tells EC to print all goals *)
pragma Goals: printall.

(*
Now, let us start with something trivial to prove.
Let us start reflexivity of integers.
Reflexivity is simply the property that an integer is equal to itslef.
Mathematically, we would write it like so:
For every integer x, x=x.
*)

(*
Here is how we declare something like that in EC.
C-c C-n multiple times to get EC to evaluate the lemma.
Or alternatively, move the cursor to the line with the lemma,
and hit C-c C-ENTER.
*)

lemma int_refl (x: int): x = x.
(*
Notice how EC populates the goals pane on the right
with the context and the conclusion.
Keep stepping through the proof with C-c C-n.
*)
proof.
    trivial.
qed.

(*
We begin a formal proof with the tactic called "proof",
although it is optional to begin a proof with the "proof" keyword/tactic, 
it is considered good style to use it.

Then we use a set of tactics which transform the goal into zero or more subgoals.
In this case, we used the tactic "trivial", to prove our int_refl lemma.
Once there are no more goals, we can end the proof with "qed",
and EC saves the lemma for further use.
*)

(* Need help *)
(* The manual doesn't have information about what trivial does. *)

print int_refl.

(*
The "print" command prints out the request in the response pane.
We can print types, modules, operations, etc using the print keyword.
*)

(*
Now EC, knows the lemma int_refl, and can use it to prove other lemmas.
Although the next lemma is trivial, it illustrates the idea of this applying 
known results.
*)

lemma forty_two_equal: 42 = 42.
proof.
   apply int_refl.
qed.

(*
Apply tries to match the conclusion of what we are applying (the proof term), 
with the goal's conclusion. If there is a match, it replaces the goal
with the subgoals of the proof term.
In our case, EC matches int_refl to the goal's conclusion, sees that it
matches, and replaces the goal with what needs to be proven for int_relf which is
nothing, and it concludes the proof.
*)

(*
In the proofs, sometimes tactics yield us something that can be simplified
We use the tactic "simplify", in order to carry out the simplification.

The simplify tactic reduces the goal to a normal form using lambda calculus.
We don't need to worry about the specifics of how, but we it is important to
understand that EC can simplify the goals given it knows how to.
It will leave the goal unchanged if the goal is already in the normal form.

For instance, here is another contrived example that illustrates the idea.
We will get to more meaningful examples in a bit, going through these
simple examples will make writing more complex proofs easier.
*)

lemma x_plus_equal (x: int): x + 3 = x + 1 + 1 + 1.
proof.
    simplify.
    (* EC does the mathematical computation for us and reduces the goal to true *)
    (* Need help *)
    (* How do I explain true? *)

    simplify.
    (* simplify doesn't fail, and leaves the goal unchanged *)

    trivial.
qed.

(* ---- Exercise ---- *)
(* 
"admit" is a tactic that closes the current goal by admitting it.
Replace admit in the following lemma and prove it using the earlier tactics.
*)

lemma x_minus_equal (x: int): x - 10 = x - 9 - 1.
proof.
admit.
qed.

(*
The goal list in EC is an ordered one, and you have to prove them
in the same order as EC lists it. "admit" can be used to bypass a certain 
goal and focus on something else in the goal list.
*)

(* 
EC comes with a lot of predefined lemmas and axioms that we can already use.
For instance, let us take a look at the "addzC" and "addzA" axioms.
Try to use these to prove commutativity and associativity for integers.
*)
print addzC.

(* Commutativity *)

lemma int_comm (x y: int): x + y = y + x.
proof.
    admit.
qed.


(* Associativity *)
print addzA.

lemma int_assoc (x y z: int): x + (y + z) = (x + y) + z.
proof.
    admit.
qed.

(* Searching in EC *)

(*
Since, there is a lot that is already done in EC,
we need a way to look for things. 
We do that using the "search" command. It prints out all axioms and lemmas 
involving the list of operators that give it.
*)

search [-].
(* [] - Square braces for unary operators  *)

search (+).
search ( * ).
(* () - Curly braces for binary operators. 
Notice the extra space for the "*" operator.
We need that since (* *) also indicates comments.
*)

search (-) (+).
(* Lists of operators *)


(*---- Exercises ----*)

(* Distributivity *)
(* Search for the appropriate axiom and apply it to discharge this goal. *)
lemma int_distr (x y z: int): (x + y) * z = x * z + y * z.
proof.
    admit.
qed.

(*
So far, we saw lemmas without any assumptions 
except for that of the type of the variable in quesiton.
More often than not we will have assumption regarding variables.
We need to treat these assumptions as a given and introduce them into the context.
This is done by using "move => ..." followed by the name you want to give
the assumption.
*)

lemma x_pos (x: int): 0 < x => 0 < x+1.
proof.
    move => x_ge0.
    simplify.
    trivial.
    (* Both of those tactics don't work. We need something else here *)
    (* Let us see is EC has something that we can use. *)
    search (<) (+) (0) (=>).
    rewrite addz_gt0.
    (* Splits into two goals *)

        (* Goal 1: 0 < x *)

        (*
        When we have a goal matches an assumption, we 
        can use the tactic assumption to discharge it.
        *)
        assumption.

        (* Goal 2: 0 < 1 *)
        trivial.
qed.


(* Let us see some variations *)

lemma int_assoc_rev (x y z: int): x + y + z = x + (y + z).
proof.
    rewrite -addzA.
    simplify.
    trivial.
qed.

(* TODO: Introduce smt. Do all the previous exercises with smt *)

require import AllCore.

(* Logs and exponents *)

lemma exp_product (x: real) (a b: int): x^(a*b) = x ^ a ^ b.
proof.
    search (^) (=).
    by apply RField.exprM.
qed.

lemma exp_product2 (x: real) (a b: int): x <> 0%r => x^a * x^b = x^(a + b).
proof.
    move => x_pos.
    search (^) (=).
    (* Need help here *)
    (* It holds even for x=0 so why is there a pre-condition for x <> 0 in this *)
    print  RField.exprD.
    rewrite -RField.exprD.
    assumption.
    trivial.
qed.

(* Logarithm exercises *)
(* TODO: Exercise to get students to op log *)

require import RealExp.

lemma ln_product (a b: real) : 0%r < a  => 0%r < b => ln (a*b) = ln a + ln b.
proof.
    search (ln) (+).
    move => H1 H2.
    by apply lnM.
qed.
    

(* As an exercise try to do it for log *)
(* Intro to functions in EC  *)
lemma log_product (a b x : real): 0%r < a  => 0%r < b => log x (a*b) = log x a + log x b.
proof.
    move => H1 H2.
    (* TODO: Need help here *)
    (* Unfold log? inline log? *)
    smt.
qed.

(* Modulo arithmatic exercises *)
require import IntDiv.

(* Need help here *)
(* How to search for strings in the theories *)
(* Trying to search for "mod" *)

(* This doesn't work for some reason.*)
search (%%).

print modzDm.

lemma mod_add (x y z: int): (x %% z + y %% z) %% z = (x + y) %% z.
proof.
    by apply modzDm.
qed.


(* 
A couple of more keystrokes that might be useful.

1. C-c C-r: Begin evaluating from the start
2. C-c C-b: Evaluate until the end of the file.

Go ahead and give these a try.
*)
