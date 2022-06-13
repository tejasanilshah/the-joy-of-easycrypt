require import AllCore.
require FSet.
require Distr.

type D.
clone Distr.MFinite as DD with
  type t <= D.

(* Implicitly axiomatized finiteness:
If we wanted not to axiomatize it,
we would add "proof *" before the . in the clone command
Like so:

clone Distr.MFinite as DD with
  type t <= D
  proof *. *)

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
