require import AllCore.
require FSet.
require Distr.

type D.
clone Distr.MFinite as DD with
  type t <= D.

(*
Implicitly axiomatized finiteness:
If we wanted not to axiomatize it,
we would add "proof *" before the . in the clone command

To make this idea clear let us define another type called throwaway,
and see what we would need to prove if we didn't axiomatize the finiteness.
*)

type throwaway.
clone Distr.MFinite as Finthrowaway with
    type t <= throwaway
    proof *.

(* EC requires us to prove Support.enum_spec, which we can
do by using "realize". However, since throwaway is an abstract type,
we can't really do so.
Similarly, in our exercise we have the type D, which is an abstract type.
At this point this isn't the focus of the lecture so we will 
go continue with the axiomatized approach. But it is important to know
that this is "cheating".
 *)
realize Support.enum_spec.
admit.
qed.

(* Let us throwaway the throwaway type, and continue with the lecture. *)


op f : D -> D.
axiom f_bij: bijective f.
axiom no_fix x: f x <> x.

module Game = {
  proc owp() : bool = {
    var x : D;
    var x' : D;
    var y : D;
    x <$ DD.dunifin; (* x uniform in D *)
    y <- f (x);  (* x := f x *)
    x' <- y; (* Adv returns x':=y *)
    return x=x';
  }
}.

lemma adv_silly:
    hoare [ Game.owp : true ==> res<>true ].
proof.
(*
  proc.
  wp 2.
  wp 1.
  rnd.
  skip.
  smt.
*)
  proc; auto; smt.
qed.

module Game2 = {
  proc owp() : bool = {
    var x : D;
    var x' : D;
    var y : D;
    x <$ DD.dunifin; (* x uniform in D *)
    y <- f x;  (* x := f x *)
    x' <- f y; (* Adv returns x':=f(y) *)
    return x=x';
  }
}.

axiom ff_nofix x: f (f x) <> x.

lemma adv_silly2:
    hoare [ Game2.owp : true ==> res<>true ].
proof.
  proc; auto; smt.
qed.
