Working through `ambient-logic.ec` should give you a good grasp of the ambient logic and tactics for reasoning with simple math. Up until now, we were working with mathematical proofs that only used logical reasoning. However, when working with programs and procedures we need a way to reason with what the programs do.

For instance, let us think about an exponentiation program for integers like so:

```
exp(x, n):
    r = 1
    i = 0
    while (i < n):
        r = r * x
        i = i + 1
    return r
```

When presented with a program like this, our objective is to figure out if the program behaves correctly. At first glance, this program seems correct. However, a glaring mistake here is that the program will always return $1$ as a result if we pass any negative integer as the second argument. That isn't the behaviour we expect from an exponentiation function. So saying that the program is correct would be a false claim. So to make claims about the behaviour of the program, mathematically, we would say something like:

$$ \text{Given } \underbrace{x \in \mathbb{Z}, n \in \mathbb{Z} \text{ and } n \ge 0 }_a \ \ \ \underbrace{exp(x, n)}_b \text{  returns  } \underbrace{r = x ^{n}}_c $$

$$ \text{Where } a \text{ is the precondition}, b \text{ is the program}, c \text{ is the postcondition} $$

# The Hoare triple
As marked in the statement above, claims that we make generally have three distinct parts: preconditions, the program and postconditions. Hoare logic formalises these three parts and introduces them as a **Hoare triple**.

A Hoare triple is denoted like so:

$$  \\{ P \\} \  C \  \\{ Q \\} $$

Here $P,Q$, are conditions on the program variables used in $C$. Conditions on program variables are written using standard mathematical notations together with logical operators like $\wedge$ (‘and’), $\vee$ (‘or’), $\neg$ (‘not’) and $\implies$ (‘implies’). Additionally, we have special conditions $true$ or $T$ which always holds, and $false$ or $F$ which never holds.

$C$ is a program in some specified language.

We say that a Hoare triple, $\\{P\\} \ C \ \\{Q\\}$, holds if whenever $C$ is executed from a state satisfying $P$ and if the execution of $C$ terminates, then the state in which $C$’s execution terminates satisfies $Q$. We will limit our discussion to programs which terminate.

## Examples
1. $\\{ x = n \\} \  x:= x+1 \ \\{ x = n+1 \\}$ holds. ( $:=$ is the assignment operator)
2. $\\{ x = n \\} \ x:= x+1 \ \\{ x = n+ 2 \\}$ doesn't hold.
3. $\\{ true \\} \ C \ \\{ Q \\}$ is a triple in which the precondition always holds. So we'd say that this triple holds for every $C$ that satisfies the postcondition $Q$.
4. $\\{ P \\} \ C \ \\{ true \\}$, similarly, this triple holds for every precondition $P$ that is satisfied, and every program $C$.
5. $\\{ false \\} \ C \ \\{ Q \\}$, is an interesting triple which, according to our definitions, doesn't hold since false is a statement that never holds. However, this is a slightly special case, as we will see in EasyCrypt.

## Exercises
1. Does $\\{x=1\\} \ x:=x+2 \ \\{x=3\\}$ hold?
2. How about $\\{true\\} \ exp(x,a) \ \\{r=x^a\\}$? Why?
3. What about $\\{2=3\\} \ x:=1 \  \\{x=1\\}$?

# Strength of statements
Informally, if a statement can be deduced from another, then the statement that was deduced is a weaker statement.

Mathematically if we have $P \implies Q$, we say that $P$ is a stronger statement than $Q$.

For example,

$$ x = 5 \implies x \ge 5$$

$$ x = 5 \text{ is a stronger statement than } x \ge 5$$

As discussed earlier, we have two special statements, $true$, which always holds, and $false$, which never holds. These are the weakest and the strongest statements there are, respectively.

Since any statement that holds can imply that $true$ holds. The reason is that it always holds, $true$ is the weakest statement there is.

Similarly, $false$ never holds. So, no statement can imply $false$; hence, it is the strongest statement there is.

# Proof trees
So far, we looked at Hoare triples for simple statements, these can be thought of "programs" with a single instruction as well. However, we need to be able to work with multiple statements and more complex statements. We achieve this by formalizing a set of axioms that we believe to be true, and then we combine these axioms to make claims about complex statements. We often visualize these series of steps in which we put the axioms together into *schemas* or *proof trees*.

For example: For a statement $S$, we say it is or provable by denoting it with a turnstile ($\vdash$) symbol like so $\vdash S$, and its proof can be denoted by:

$$ \dfrac{\vdash S_1, \vdash S_2, \dots ,\vdash S_n}{\vdash S} $$

This says the conclusion $S$ may be deduced from the $S_1, \dots, S_n$ which are the hypotheses of the rule. The hypotheses can either all be theorems or axioms of Hoare Logic or mathematics.

Now, we will take a look at some of the axioms of Hoare logic  with examples to give you a flavour of how they work. One of the reasons we cover these is because these axioms form the basis for the tactics we use in Hoare logic in EasyCrypt. Of course, the main idea is to familiarize the reader with the basics since the main goal is for the machine to take care of the specifics.

# Axioms of Hoare logic

1. **Assignment**:

    $$ \vdash \\{P[E/V ]\\} \ V :=E \\\{P\\} $$

    Where $V$ is any variable, $E$ is any expression, $P$ is any statement, and the notation $P[E/V]$ denotes the result of substituting the term $E$ for all occurrences of the variable $V$ in the statement $P$.

2. **Precondition strengthening**: When we have a Hoare triple $\\{P'\\}\ C \ \\{Q\\}$, where $P'$ is a statement that follows from a stronger statement, $P$. Then we can say,

    $$ \dfrac{\vdash P \implies P', \vdash \\{P'\\}\ C \ \\{Q\\}} {\vdash \\{P\\} \ C \ \\{Q\\}} $$

    Example:  Let

    $$C = [x:=x+2]  $$

    $$P = \\{x = 5\\}$$

    $$P' = \\{x \ge 5\\} \text{ , and}$$ 

    $$Q = \\{x \ge 7\\}$$

    Using the precondition strengthening axiom we have,

    $$ \dfrac{\vdash \\{x = 5\\}  \implies \\{x \ge 5\\} ,\ \vdash \\{x \ge 5\\} \ x:=x+2 \ \\{x \ge 7\\} } {\vdash \\{x=5\\} \ x:= x + 2 \ \\{x \ge 7\\}} $$
    
3. **Postcondition weakening**: Similarly, when we have a Hoare triple ${P}\, C \,{Q'}$, where $Q'$ is a strong statement, and if $Q$ follows from $Q'$. Then we can say,

    $$ \dfrac{\vdash \\{P\\}\ C \ \\{Q'\\}, \ \vdash Q' \implies Q}{ \vdash \\{P\\} \ C \ \\{Q\\}} $$

    Example:  Let
    
    $$C = [x:=x+2]  $$
    
    $$P = \\{x = 5\\}$$
    
    $$Q' = \\{x = 7\\} \text{ , and}$$ 
    
    $$Q = \\{x \ge 7\\}$$

    With the postcondition weakening axiom, we have,  

    $$ \dfrac{\vdash \\{x = 5\\}\ x:=x+2 \ \\{x =7\\}, \ \vdash x = 7  \implies x \ge 7 } {\vdash \\{x=5\\} \ x:= x + 2 \ \\{x \ge 7\\}} $$

    Together the precondition strengthening and postcondition weakening axioms are known as the \textbf{consequence rules}.

4. **Sequencing**: For two programs $C_1, C_2$, we have

    $$ \dfrac{ \vdash \\{P\\}\ C_1 \ \\{Q'\\}, \ \vdash \\{Q'\\}\ C_2 \ \\{Q\\}, }{ \vdash \\{P\\}\ C_1;C_2 \ \\{Q\\} } $$

    Example: Let

    $$C_1 = [x:=x+2] $$
    $$C_2 = [x:=x*2] $$
    $$P = \\{x = 5\\}$$
    $$Q' = \\{x = 7\\}  \text{ , and}$$ 
    $$Q = \\{x = 14\\}$$
    Using the sequencing axiom, we have,

    $$ \dfrac{ \vdash \\{x = 5\\} \ x:=x+2 \ \\{x =7\\}, \ \vdash \\{x = 7\\}\ x:=x * 2  ,\\{x =14\\} } {\vdash \\{x=5\\} \ x:= x + 2, x:= x * 2 \ \\{x =14\\}} $$

We go through these examples to get a sense of what formal proof trees look like and the theory that formal verification is based on. The proof trees that we've used are already simplified to exclude the assignment axiom and steps that we as humans can easily understand and gloss over. Proof trees get quite large and unwieldy as soon as we do anything non-trivial. This is exactly where formal verification tools come into the picture. So, let us now switch to EasyCrypt and work with Hoare triples.

Note that Hoare logic by itself is often referred to as classical Hoare logic. It has been studied quite extensively, and there are plenty of good textbooks ([Textbook 1](https://dl.acm.org/doi/10.5555/975331), [Texbook 2](https://mitpress.mit.edu/books/foundations-programming-languages)) that one can refer to for mathematical rigour and completeness. The objective here is to give the reader an intuitive understanding of the math, and enough working knowledge required to work with EasyCrypt.

# HL in EasyCrypt
With a basic understanding of HL, we can now proceed to work with it in EasyCrypt. We will work through the file `hoare-logic.ec`. As before, it is recommended to work with the file in the Proof General + Emacs environment. However, reading through this section provides the basic ideas developed in the practice file.

## Basic Hoare triples
Let us start small and first work with some examples that we saw earlier. We first define a module to define two procedures for the programs.

```
module Func1 = {
  proc add_1 (x:int) : int = { return x+1; }
  proc add_2 (x: int) : int = { x <- x + 2; return x; }
}.
```
A Hoare triple denoted by $\\{P\\} \ C\ \\{Q\\}$ in theory is expressed as `hoare [C : P ==> Q ]` in EasyCrypt, with the usual definitions. Additionally, the return value of the program, $C$, is stored in a special keyword called `res`.

So the triple, $\\{x=1 \\} \  \text{Func1.add}\textunderscore\text{1} \  \\{x=2\\}$, would be expressed in EasyCrypt like so:
```
lemma triple1: hoare [ Func1.add_1 : x = 1 ==> res = 2].
```
When working with Hoare logic or its variants, the goal will be different from what a goal in ambient logic looks like. For instance, evaluating the `lemma triple1` produces the following goal.
```
Current goal
Type variables: <none>
---------------------------------------------
pre = x = 1

    Func1.add_1
    
post = res = 2
```
We need to start stepping through the procedure or program that is being reasoned about and change the preconditions and postconditions according to axioms and lemmas that we have.

To make progress here, we first need to tell EasyCrypt what `Func1.add_1` is. The way to do that is by using the `proc` tactic. It simply fills in the definitions of the procedures that we define. Since `Func1.add_1` is made up of only a return statement, `proc` replaces `res` with the return value. This leaves us with an empty program. This is what we want to work towards; using different tactics we would like to change the preconditions and postconditions depending on what the programs that we are reasoning with do. Once we have consumed all the program statements, we can transform the goal from a HL goal to a goal in ambient logic using the `skip` tactic. `skip` does the following:

$$ \dfrac{\\{P\\} \ \ \ \ \ \\{Q\\}}{ P \implies Q} \texttt{skip} $$

This puts us back in the familiar territory of ambient logic, and we can use all the tactics that we learnt in `ambient-logic.ec`. The only difference is that transitioning a goal from Hoare logic to ambient logic introduces some qualifiers about the memory that the program works on. Hence, we need to handle those as well. In this example, the goal after evaluating `skip` will simply read: `forall &hr, x{hr} = 1 => x{hr} + 1 = 2`. The proof for which follows pretty trivially. The only difference is that we need to move the memory into the assumption by prepending the \& character in the `move => ` tactic.

So the full proof for this simple example looks like so:
```
lemma triple1: hoare [ Func1.add_1 : x = 1 ==> res = 2].
proof.
    proc.
    skip.
    move => &m H1. (* &m moves memory to the assumption *)
    subst. (* Substitutes variables from the assumptions *)
    trivial.
qed.
```

Now let us work with a program where the body is not empty.

```
lemma triple2: hoare [ Func1.add_2 : x = 1 ==> res = 3 ].
```
Using `proc` produces the following goal.
```
Current goal
Type variables: <none>
---------------------------------------------
Context : Func1.add_2

pre = x = 1

(1)  x <- x + 2               

post = x = 3
```

When we are faced with $\\{P\\} S1; S2; S3; \\{Q\\}$ with the usual definitions, applying the `wp` tactic consumes as many ordinary statements as possible from the end. Then it replaces the postcondition $Q$, with a precondition $R$. $R$ is chosen such that it holds in conjunction with the consumed statements and the original postcondition and it is as weak as possible (*w*eakest *p*recondition). It is easier to visualize this in a proof tree. 

For instance, when we have $\\{P\\} S1; S2; S3; \\{Q\\}$ and $S2; S3;$ are statements that can be dealt with some axioms or logical deductions, then `wp` does the following:

$$ \dfrac{ \dfrac{ \\{P\\} S1; S2; S3; \\{Q\\}}    {\\{P\\} S1; \\{R\\} /\textbackslash \\{R\\} S2; S3; \\{Q\\}}\texttt{wp} } {\\{P\\} S1; \\{R\\}} $$


