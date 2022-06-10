require import AllCore.
(* require import Fun. *)
(* import Fun.Bijections. *)
require FSet.
(* require ISet. *)

(* print FSet.Duni.duni . *)

type D.
(* axiom finD: ISet.Finite.finite ISet.univ<:D>. *)
op f : D -> D.
axiom f_bij: bijective f.
axiom no_fix x: f x <> x.

module Game = {
  proc owp() : bool = {
    var x : D;
    var x' : D;
    var y : D;
    x <$ FSet.Duni.duni (ISet.Finite.toFSet ISet.univ<:D>); (* x uniform in D *)
    y = f (x);  (* x := f x *)
    x' = y; (* Adv returns x':=y *)
    return x=x';
  }
}.

lemma adv_silly:
    hoare [ Game.owp : true ==> res<>true ].
proof.
(*  proc.
  wp 2.
  wp 1.
  rnd.
  skip.
  smt. *)
  proc; auto; smt.
qed.

module Game2 = {
  proc owp() : bool = {
    var x : D;
    var x' : D;
    var y : D;
    x = $ FSet.Duni.duni (ISet.Finite.toFSet ISet.univ<:D>); (* x uniform in D *)
    y = f x;  (* x := f x *)
    x' = f y; (* Adv returns x':=f(y) *)
    return x=x';
  }
}.

axiom ff_nofix x: f (f x) <> x.

lemma adv_silly2:
    hoare [ Game2.owp : true ==> res<>true ].
proof.
  proc; auto; smt.
qed.
