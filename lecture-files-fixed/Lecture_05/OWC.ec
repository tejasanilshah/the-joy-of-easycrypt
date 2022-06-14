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
