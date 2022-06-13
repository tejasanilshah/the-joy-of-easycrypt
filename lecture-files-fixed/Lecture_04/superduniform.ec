require import AllCore.
require import Distr.
import List.

print duniform.

  (* This file consists of the ideas and exploration when working with lists and distributions *)

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
