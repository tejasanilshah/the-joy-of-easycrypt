(* Due: Mar 8, 2015 *)


(* Call your solution 02-name.ec where name is your first
   name. For each problem, please indicate how long it took you. *)


require import AllCore IntDiv.

pragma Goals:printall.

(* RSA encryption and decryption, as in the lecture *)
op E (pk:_*_) m : int = exp m (pk.`1) %% (pk.`2).
op D (sk:_*_) c : int = exp c (sk.`1) %% (sk.`2).

(* Euler phi function, axiomatized *)
op phi : int -> int.
op coprime : int -> int -> bool.
axiom fermat a n: 0<n => coprime a n => a^(phi(n)) %% n = 1.
axiom phi_pos n: 0<n => 0 < phi n.

(* Many nice laws *)
lemma exp_add (a b c:int): 0<=b => 0<=c => a^(b+c) = ((a^b) * (a^c)). smt. qed.
lemma mod_pos a n: 0<n => 0 <= a%%n. smt. qed.
lemma exp_mul (a b c:int): 0<=b => 0<=c => (a^b)^c = a^(b*c). smt. qed.
axiom add_mod (a b n: int): 0<n => (a + b) %% n = ((a %% n) + (b %% n)) %% n.
axiom mul_mod (a b n: int): 0<n => (a*b) %% n = ((a %% n) * (b %% n)) %% n. 
axiom exp_mod (a b n: int): 0<n => 0<=b => (a^b) %% n = ((a %% n) ^ b) %% n. 
lemma mul_pos (a b: int): 0<=a => 0<=b => 0<=a*b. smt. qed.
lemma exp_a1 (a : int): a^1 = a. smt. qed.
lemma exp_1a (a : int): 0<=a => 1^a = 1. smt. qed.
lemma mod_mod (a n : int): 0<n => (a %% n %% n) = (a %% n). smt. qed.
axiom mod_def (a n : int): 0<=a => exists k, 0<=k /\ a=a%%n + n*k. 
lemma le_less (a : int): 0<a => 0<=a. smt. qed. 
lemma mod_1 (n : int): 0<n => n<>1 => 1 %% n = 1. smt. qed.
lemma mul_a1 (a : int ): a*1 = a. smt. qed.

(* Problem: Prove the following generalization of "fermat".
   I have added some structure already, but you can prove it differently, 
   if you wish. You are not allowed to use "smt".
 *)

lemma fermat' a b n:
 0<n => n<>1 => 0<=b => coprime a n => b %% phi(n) = 1 => a^b %% n = a %% n.
proof.
  move => npos n1 bpos coprime assm.

  have Hb: exists k, 0<=k /\ b=b%%phi(n) + phi(n)*k.
  by apply mod_def.
  elim Hb. (* If you have a theorem H of the form "exists x, bla",
              you can use "elim H" (plus some intros) 
              to get some x with property bla. Try. *)
  move => k H.


  (* If you have a theorem H of the form "A /\ B", you can
     also use "elim H" to get the assumptions "A" and "B". *)
  elim H.
  move => k_ge H.

  (* From here on, use all the above lemmas (including fermat) to
     rewrite the goal successively to make the goal simpler and
     simpler. The rewrite rules will give you subgoals, these have
     can by solved by applying various of the above rules. 
  
     One note: Remember that %% binds least. So something like "a%%n +
     b%%n" actually means "((a%%n)+b)%%n" and not
     "(a%%n)+(b%%n)". Keeping that in mind will avoid a lot of
     confusing when reading the subgoals.
  *)
rewrite H.
rewrite exp_add => //.
rewrite assm => //.
rewrite mul_pos => //.
have phi_pos: 0 < phi n. exact phi_pos.
by apply le_less.

rewrite -exp_mul => //.
have phi_pos: 0 < phi n. exact phi_pos.
by apply le_less.

rewrite mul_mod => //.
rewrite assm.
rewrite exp_a1.
rewrite exp_mod => //.
rewrite fermat => //.
rewrite exp_1a => //.
rewrite mod_1 => //.
rewrite mul_a1 => //.
rewrite mod_mod => //.
qed.


(* This is the proof from the lecture, with a few fixes.  We have the
   additional "coprime m N" assumption.  To get rid of that, we
   actually need a completely different proof (using Chinese remainder
   theorem). *)

lemma rsa_correct (e d N m: int):
    e*d %% phi N = 1
    => 0 <= e
    => 0 <= d
    => 0 < N
    => N <> 1
    => coprime m N
    => D (d,N) (E (e,N) m) = m %% N.
proof.
  rewrite /D /E.
  move => Hedprod epos dpos Npos N1 cop.
  simplify. 
  rewrite -exp_mod => //.
  rewrite exp_mul => //. 
  apply fermat' => //. 
    by apply mul_pos.
qed.
