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
Since we only have comments so far there is no goal for EC to work with.
We will change that in a short while.
*)

(*
Here is a short list of keystrokes that will come in handy for this file:
1. C-c C-n :  Evaluate next line or block of code 
2. C-c C-u :  Go back one line or block of code
3. C-s: Search for a string in the code
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

pragma Goals: printall.
(* The pragma line simply tells EC to print all goals *)

(*
Now, let us start with something trivial to prove.
Let us start reflexivity of integers.
Reflexivity is simply the property that an integer is equal to itslef.
Mathematically, we would write it like so:
For every integer x, x=x.
*)

(*
Here is how we declare something like that in EC.
C-c C-n multiple times to get EC to read the next line.
Or alternatively, move the cursor to the line with the lemma, and hit C-c C-ENTER.
*)

lemma int_refl (x: int): x = x.
(*
Notice how EC populates the goals pane on the right
with the context and the conclusion.
*)
proof.
    trivial.
qed.

(* Need help *)
(* The manual doesn't have information about what trivial does. *)

(* TODO: Write about what tactics are *)

(* TODO: Write about simplify *)

lemma x_plus_equal (x: int): x + 3 = x + 1 + 1 + 1.
proof.
    simplify.
    (* Need help *)
    (* How do I explain true? *)
    trivial.
qed.

(* TODO: Write about admit *)
(* ---- Exercise ---- *)

lemma x_minus_equal (x: int): x - 10 = x - 9 - 1.
proof.
admit.
qed.

(* TODO: Write about things that are given to us and explain printing *)
print addzC.

(* Commutativity *)
lemma int_comm (x y: int): x + y = y + x.
proof.
    (* TODO: Write about apply *)
    apply addzC.
qed.

(* ---- Exercise ---- *)

(* Associativity *)
print addzA.

lemma int_assoc (x y z: int): x + (y + z) = (x + y) + z.
proof.
    admit.
qed.

(* TODO: How to look for things *)

(* TODO: Searching *)

(* TODO:  ---- Exercises ---- *)

(* Distributivity *)

lemma int_distr (x y z: int): (x + y) * z = x * z + y * z.
proof.
    search ( * ) (+) (=).
    apply mulzDl.  
qed.


lemma x_pos (x: int): 0 < x => 0 < x+1.
proof.
    move => x_ge0.
    simplify.
    trivial.
    (* Both of those tactics don't work. We need something else here *)
    search (<) (+) (0).

    (* TODO: Write about rewrite *)
    rewrite addz_gt0.
    (* Splits into two goals *)

        (* Goal 1: 0 < x *)
        (*TODO: Explain assumption  *)
        assumption.

        (* Goal 2: 0 < 1 *)
        trivial.
qed.

(* TODO:  ---- Exercise ----  assumption and rewrite *)

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
