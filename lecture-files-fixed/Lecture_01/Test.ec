require import Int.
require import Real.

lemma test (x:real): x+x=x+x.
    trivial.
qed.

lemma test2: forall (x:real), x+x=x+x.
    trivial.
qed.

lemma simple_lemma: 1+1=2.
    trivial.
qed.

lemma simple_lemma_real: 1%r+1%r=2%r.
    trivial.
qed.
