(* OWC - One-way constant *)

require import AllCore.
require Distr.
pragma Goals:printall.

type D.
clone Distr.MFinite as DD with
  type t <= D.
op f : D -> D.
axiom f_const x y: f x = f y.

module type Adv = {
  proc adv(y:D) : D
}.

module Game(A:Adv) = {
  proc main() : bool = {
    var x,x',y : D;
    x <$ DD.dunifin;
    y <- f witness;
    x' <- A.adv(y);
    return x=x';
  }
}.

op cardd = DD.Support.card.

lemma unif_prob x': 
    mu
    DD.dunifin
    (fun (x : D) => (x = x') = true) <= 1%r / cardd%r.
    simplify.
    admit.
qed.


lemma secure &m (A<:Adv):
    Pr[Game(A).main() @ &m : res=true] 
       <= 1%r / cardd%r.
proof.
  byphoare => //.
  proc.
  swap 1 2.
  rnd.
  simplify.
  conseq (_: _ ==> true).
    move => &hr H.
    simplify.
    by apply unif_prob.
  trivial.
qed.

module Game1(A:Adv) = {
  proc main() : bool = {
    var x,x',y : D;
    x <$ DD.dunifin;
    y <- f x;
    x'<- A.adv(y);
    return x=x';
  }
}.

(* { true } Game.main ~ Game1.main { res_1 = res_2 } *)
lemma samegame (A<:Adv):
    equiv [ Game(A).main ~ Game1(A).main : ={glob A} ==> res{1}=res{2} ].
proof.
  proc.
  call (_: true).
  simplify.
  conseq (_: _ ==> ={y,glob A,x}). smt.
  wp.
  conseq (_: _ ==> ={glob A, x}). smt.
  rnd.
  simplify.
  skip.
  trivial.
qed.

lemma samegame_pr (A<:Adv) &m:
    Pr[Game(A).main() @ &m : res=true]
    =
    Pr[Game1(A).main() @ &m : res=true].
proof.
  byequiv => //.
  conseq (_: ={glob A} ==> _) => //.
  apply (samegame A).
qed.

lemma secure1 &m (A<:Adv):
    Pr[Game1(A).main() @ &m : res=true] 
       <= 1%r / cardd%r.
  rewrite -(samegame_pr A &m).
  exact (secure &m A).
qed.

