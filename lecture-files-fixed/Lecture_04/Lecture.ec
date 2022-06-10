require import AllCore.
(* require import Fun. *)
(* import Fun.Bijections. *)
require FSet.
(* require ISet. *)
require Distr.

(* print FSet.Duni.duni . *)

type D.
clone Distr.MFinite as DD with
  type t <= D.
(* Implicitly axiomatized finiteness: *)
print DD.Support.enum_spec.
(* If we wanted not to axiomatize it, we would add "proof *" before the . in the clone command *)

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

import List.
import Distr.
print duniform.
lemma test (x:'a): mu1 (duniform []) x = 0%r.
    smt.
qed.

lemma test2 (x:'a) l:
    (x \in l)%List =>
    mu1 (duniform l) x > 0%r.
    smt.
qed.

type 'a set = 'a -> bool.

op superduniform (s : 'a set) : 'a distr =
  duniform (choiceb (fun l => s = List.mem l) []).


op finite (s: 'a set) : bool =
  exists l, s = List.mem l.

(* lemma finlist (s:'a set): *)
(*     finite s => exists l, s = List.mem l. *)
(*   smt. *)
(* qed. *)

lemma link (l:'a list):
    duniform l = superduniform (List.mem l).
    rewrite /superduniform.
    pose l0 := choiceb (fun (l0 : 'a list) => mem l = mem l0) [].
    rewrite -eq_duniformP.
    have Hl0: mem l = mem l0.
    smt.
    rewrite Hl0.
    trivial.
qed.
    
lemma test3 (x:'a) s:
    finite s =>
    s x =>
    mu1 (superduniform s) x > 0%r.
    
    move => Hfin Hmem.
    have Hex: exists l, s = List.mem l.
    rewrite /finite in Hfin.
    apply Hfin.
    elim Hex.

    move => l Hl.
    rewrite Hl.
    rewrite -link.

    apply test2.
    rewrite -Hl.
    apply Hmem.

qed.
