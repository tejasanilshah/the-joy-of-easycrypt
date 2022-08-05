Hoare Logic enables us to reason about programs and build formal proof trees, but it doesn't have any way to work with pairs of programs.

For instance, let us say we build a compiler which optimizes some user-written code. At the very least, the users would expect the compiler to preserve program behaviour across optimizations. So, we would like to provide some assurance to the users about how the compiled and optimized code still performs the same tasks. To do this, we need to relate the two programs (user written and optimized) and conclude that given the same initial conditions executing both the programs yield the same final state. However, there is no straightforward way to do this with classical Hoare Logic.

To address the deficiency discussed above, a simple variation of classical Hoare logic called \textbf{Relational Hoare Logic} (RHL) was conceived. RHL allows us to make judgements about two programs with the introduction of a \textbf{Hoare quadruple}. A Hoare quadruple is denoted like so: $$ \{P\} \, C \sim D \, \{Q\}$$

Here as with classical Hoare logic $P \text{ and } Q$, are conditions on the program variables used in $C \text{ and } D$. The only difference is that we now have to understand that $C \text{ and } D$ act on two different memories. The conditions $P \text{ and } Q$ have to take this into account. The rest of the ideas carry over quite naturally from classical Hoare logic.

We say that a Hoare quadruple, $\{P\} \, C \sim D \, \{Q\}$, holds, if whenever $C \text{ and } D$ are executed from a state satisfying $P$ and upon the execution and termination of $C \text{ and } D$, the resultant state satisfies $Q$.

The axioms and rules from classical Hoare logic are also modified slightly to work with quadruples instead of triples. 

For instance, consider the sequencing axiom from HL (the symbols have their usual meanings):
$$
\dfrac{
\vdash \{P\}\, C_1 \,\{Q'\}, \,
\vdash \{Q'\}\, C_2 \,\{Q\},
}
{
\vdash \{P\}\, C_1;C_2 \,\{Q\}
}
$$

In RHL, we modify it to work with quadruples like so:
$$
\dfrac{
\vdash \{P\}\, C_1 \sim D_1 \,\{Q'\}, \,
\vdash \{Q'\}\, C_2 \sim D_2 \,\{Q\},
}
{
\vdash \{P\}\, C_1;C_2 \sim D_1;D_2 \,\{Q\}
}
$$

This is a recurring theme when it comes to discussing Hoare logic and its variations. Each variation addresses a deficiency that the previous version has, and we update or add axioms to work with the modifications that we introduced. We will rely on EasyCrypt to take care of the details.

\subsection{RHL in EasyCrypt}
Now to get a little practice with RHL, let us switch to EasyCrypt. As usual, we start with some simple exercises.
\subsubsection{Basic Hoare quadruples}
We begin with two functions, \ec{swap1} and \ec{swap2}, which swap variables. However, the way they swap variables is slightly different, and we'd like to establish the fact that they accomplish the same task. We define \ec{swap1} and \ec{swap2} like so:

\begin{easycrypt}{}{}
module Jumbled = {
  proc swap1 (x y: int) : int*int = {
  var z;
  z <- x;
  x <- y;
  y <- z;
  return (x,y);
  }

  proc swap2 (x y: int) : int*int = {
  var z;
  z <- y;
  y <- x;
  x <- z;
  return (x,y);
  }
}.
\end{easycrypt}
In both functions, \ec{z} is the temporary variable. In \ec{swap1}, \ec{x} is first stored in \ec{z}, while in \ec{swap2} \ec{y} is stored first. However, both the functions accomplish the task of swapping variables.

A Hoare quadruple, $ \{P\} \, C_1 \sim C_2 \, \{Q\}$, is expressed in EasyCrypt with the statement \ec{equiv [C1 ~ C2 : P ==> Q].} As with Hoare triples, we access the results of both the programs using the \ec{res} keyword. However, since we now have two programs, we need to add identifiers to the variables that we use and also to the results to convey the program that we are speaking about. For instance, to prove that \ec{swap1} is equivalent to itself, we would have the following lemma.
\begin{easycrypt}{}{}
lemma swap1_equiv_swap1:
equiv [Jumbled.swap1 ~ Jumbled.swap1 : x{1}=x{2} /\ y{1}=y{2} ==> res{1} = res{2}].
proof.
    proc.
    simplify.
    auto.
qed.
\end{easycrypt}
The proof for this lemma is quite straightforward and since there isn't much to reason \ec{auto} is strong enough to complete the proof. Next we prove that \ec{swap1} is equivalent to \ec{swap2}. Now we have different programs, and the way we work with them is by using similar tactics that we used for HL. The only difference now is that we have to add identifiers to the tactics for them to target specific sides and lines of code. For instance, for the sake of a demonstration, we use the \ec{wp} in an asymmetric way.
\ec{wp n1 n2} will try to consume code up to the $\texttt{n1}^\texttt{th}$ line from the left program, up to the $\texttt{n2}^{\texttt{th}}$ line from the right program and will modify the postconditions depending on the instructions that have been consumed. The logic is similar to what we saw in HL.
\begin{easycrypt}{}{}
lemma swaps_equivalent:
equiv [Jumbled.swap1 ~ Jumbled.swap2 : ={x, y} ==> ={res}].
proof.
    proc.
    simplify.
    wp 2 3.
    wp 2 2.
    wp 0 1.
    wp 0 0.
    skip.
    trivial.
qed.
\end{easycrypt}
Since we will never really use \ec{wp} the way we did above, we can replace the large block of different calls to \ec{wp n1 n2.} with just \ec{wp.} and EasyCrypt accomplishes the same automatically. Further, we also notice that the proof only uses \ec{wp, skip} and \ec{trivial} tactics, so we can use \ec{auto} instead. This gives us a fairly trivial proof for the lemma of the swap functions being equivalent.
\begin{easycrypt}{}{}
lemma swaps_equivalent_clean:
equiv [Jumbled.swap1 ~ Jumbled.swap2 : ={x, y} ==> ={res}].
proof.
    proc.
    auto.
qed.
\end{easycrypt}

\subsubsection{Abstract modules and adversaries}
Now let us take a small detour here and build on the module types that we saw earlier when modelling the abstract IND-RoR game. When working with cryptography, we generally don't know about the inner workings of an adversary or an oracle. In order to model these in EasyCrypt, we have the module types.

\begin{easycrypt}{}{}
module type Adv = {
  proc eavesdrop_one(): bool
  proc eavesdrop_two(): bool
}.
\end{easycrypt}

By defining the module type Adv, we are instructing EasyCrypt that any concrete module which is of the \ec{Adv} type has to, at the very least, implement \ec{eavesdrop_one} and \ec{eavesdrop_two} procedures. What is interesting is that EasyCrypt allows us to reason with the abstract module types as well. For example, let us define a module which expects an Adv as input.
\begin{easycrypt}{}{}
module Abstract_game(A:Adv) = {
  proc one(): bool = {
      var x;
      x <- A.eavesdrop_one();
      return x;
  }
}.
\end{easycrypt}
At this stage, we don't know what \ec{A.eavesdrop_one} does and neither does EasyCrypt. However, we can still prove certain facts related to it. Just for a demonstration, we provide a reflexivity example.
Notice that we have a new term \ec{glob A} in the precondition. It stands for the global variables of the module \ec{A}. So in this following lemma, we claim that if the global state of the \ec{A} which is of type \ec{Adv} is equal at the beginning of the program, then running the same program yields us the same result. Quite a simple lemma, however the point to note here is that we haven't defined what the function is.
\begin{easycrypt}{}{}
lemma eavesdrop_reflex(A<:Adv):
equiv [Abstract_game(A).one ~ Abstract_game(A).one :
      ={glob A} ==> res{1} = res{2} ].
proof.
  proc.
  call (_: true).
  auto.
qed.
\end{easycrypt}
\ec{call} does a few complicated things under the hood, but at this point of time, we can think that \ec{call (_: true)}, knocks off a call to the same abstract function on both sides.

Let us also define a concrete instantiation of \ec{Adv} called \ec{A} and work with it. Module \ec{A} is quite basic, and either always returns true or always returns false.
\begin{easycrypt}{}{}
module A : Adv = {
  proc eavesdrop_one() = {
    return true;
  }

  proc eavesdrop_two() = {
    return false;
  }
}.

module Games = {
  proc t(): bool = 
  { var x; x <- A.eavesdrop_one(); return x; }
  proc f(): bool = 
  { var x; x <- A.eavesdrop_two(); return x; }
}.
\end{easycrypt}
Now we can reason with these concrete instances with the tactics that we've seen so far. For instance, since we know that \ec{Games.t} and \ec{Games.f} return different values, we can make a claim like the following and prove it. In this proof, we use \ec{inline *}, which simply fills in (or \enquote{inlines}) the concrete code of \ec{Games.t} and \ec{Games.f}. The \ec{*} in the tactic is a selector to select everything that can be inlined.
\begin{easycrypt}{}{}
lemma games_quadruple (A<:Adv): equiv [Games.t ~ Games.f :
    ={glob A} ==> res{1} <> res{2} ].
proof.
  proc.
  inline *.
  wp.
  simplify.
  trivial.
qed.
\end{easycrypt}
The key takeaway of this detour is that when we work with cryptographic proofs, we will be dealing with both concrete and abstract adversaries. We can now go back to working with some more challenging Hoare quadruples.

\subsubsection{Advanced Hoare quadruples}
As we discussed earlier, one of the use cases of RHL is to ensure that compiler optimizations preserve program behaviour. Let us take a look at an example of this with a simple compiler optimization called \textit{invariant hoisting}. Take a look at the programs defined below.
\begin{easycrypt}{}{}
module Compiler = {
  proc unoptimized (x y z: int) : int*int = {
    while (y < z){
      y <- y + 1;
      x <- z + 1;
    }
    return (x,y);
  }
  proc optimized (x y z: int) : int*int = {
    if(y < z){
      x <- z + 1;
    }
    while (y < z){
      y <- y + 1;
    }
    return (x,y);
  }
}.
\end{easycrypt}
As you can observe, if the condition of the \ec{while} loop in \ec{unoptimized} holds for even one iteration the \ec{x} is set to \ec{z+1}. However, the subsequent iterations of the loop don't change \ec{x}. Hence to save on computation, the compiler hoists that line out of the scope of the \ec{while} loop, giving us \ec{optimized}.

Now let us try to prove the fact that the behaviour of both the programs is equivalent. At this point, there can be two possibilities:
\begin{enumerate}
    \item \ec{!(y < z) => (y = z) \/ (z < y)}:\\
    In this case, neither the \ec{while} loop nor the \ec{if} condition is satisfied. So, both the programs effectively do nothing to the variables.
    \item \ec{(y < z)}:\\
    The \ec{while} loop and the \ec{if} condition are executed at least once. In this case, the variables are modified.
\end{enumerate}
So to prove that the optimization is correct, we can break our proof into these two cases, work on them independently and then put them back together.

Let us work with the first part in which the loops are never executed. In this proof, we will use the \ec{seq} tactic. It does the following:

$$
\dfrac{
\{P\} A1; A2; A3 \sim B1; B2; B3 \{Q\}
}{
\{P\} A1; \sim B1; B2; \{R\} \; /\textbackslash \; \{R\} A2; A3; \sim B3; \{Q\}
}\; seq \; 1 \; 2:(R)
$$
   
The idea behind using the \ec{seq} is to break the programs into manageable chunks and deal with them separately. In our program, we have an \ec{if} condition in \ec{optimized} that we can deal with and then work with the \ec{while} conditions. In this part of the proof, we know that the code inside the conditions is not executed. Hence, we know that we can pass the precondition itself as $R$. With this we can knock off the \ec{if} from \ec{optimized} using \ec{seq}. Then we use \ec{rcondf} to deal with the \ec{while} loops since we know that they won't be executed.

\begin{easycrypt}{}{}
lemma optimization_correct_a:
equiv [Compiler.unoptimized ~ Compiler.optimized:
      ={x, y ,z} /\ (z{1}=y{1} \/ z{1}<y{1}) ==> ={res}  ].
proof.
  proc.
  simplify.
  
  (* Dealing with the if on the right *)
  seq 0 1: ( ={x, y ,z} /\ (z{1}=y{1} \/ z{1}<y{1}) ).
  auto.
  smt().

  (* Knocking off while loop from the left *)
  rcondf {1} 1.
  auto.
  smt().
  
  (* Knocking off while loop from the right *)
  rcondf {2} 1.
  auto.
  smt().
  
  (*  *)
  auto.
qed.
\end{easycrypt}
In the proof above, we have used \ec{smt().} instead of \ec{smt.}. \ec{smt().} simply sends only the goal (conclusion and hypothesis) to the external solvers. While \ec{smt.} tries to pick an extra set of lemmas to send as well. If this process of picking what to send fails, the tactic will send all lemmas of all the theories in the context. This can be a massive number of lemmas and ultimately inefficient. For smaller proofs, like ours, using either works fine. However, in the interest of efficiency, using \ec{smt().} is recommended. Often, if we know a certain lemma will be used for a proof, we can send the specific lemmas to the external solvers like so: \ec{smt(lemma_1,lemma_2,...,lemma_n).}

Now let us work with the second part of the proof that deals with the part where the loops are executed. The only complex part of this proof is the \ec{while} loop and figuring out the invariant. In this case, we know that after every iteration of the loop \ec{y} and \ec{z} on both sides are equal, and \ec{x\{2\} = z\{2\} + 1} since we already dealt with the \ec{if} condition. In \ec{unoptimized}, the loop invariant is that \ec{ (y\{1\}<z\{1\} or x\{1\} = z\{1\} + 1)}. The rest of the proof is quite straightforward.

\begin{easycrypt}{}{}
lemma optimization_correct_b: 
equiv [Compiler.unoptimized ~ Compiler.optimized:
      ={x, y ,z} /\ y{1}<z{1} ==> ={res}  ].
proof.
  proc.
  (* Dealing with the if condition in optimized *)
  seq 0 1: (={y,z} /\ y{1}<z{1} /\ x{2} = z{2} + 1).
  simplify.
  auto.
  (* Dealing with the while loops in both *)
  while (={y,z} /\ x{2} = z{2} + 1 /\ 
  (y{1}<z{1} \/ x{1} = z{1} + 1)).
  auto.
  auto.
  smt().
qed.
\end{easycrypt}

Now we can put these both together. In this proof, we use \ec{proc*}, which modifies the goal in a way similar to \ec{proc} but without losing the fact that the code is a procedure call. Then we split on the boolean expression of the \ec{while} loop.

\begin{easycrypt}{}{}
lemma optimization_correct:
equiv [Compiler.unoptimized ~ Compiler.optimized:
      ={x, y ,z} ==> ={res}  ].
proof.
  proc*.
  
  (* Branching on the boolean *)
  case (y{1}<z{1}).
  
    (* y{1}<z{1} *)
    call optimization_correct_b. simplify. auto.
    (* ! y{1}<z{1} *)
    call optimization_correct_a. simplify. auto.
    
  smt().
qed.
\end{easycrypt}
