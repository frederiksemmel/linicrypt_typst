#import "@preview/commute:0.2.0": node, arr, commutative-diagram
#import "@preview/algo:0.3.3": algo, i, d, comment, code

#import "lib/template_fs.typ": *
#import "lib/linicrypt.typ": *

#show: fs-article.with(
  title: [Ideas on a characterization for Collision Resistance in Linicrypt without nonces],
  authors: (
    (
      name: "Frederik Semmel",
      location: [Zurich],
      email: "semmelf@student.ethz.ch",
    ),
  ),
  bibliography-file: ("../bib/crypto_custom.bib", "../lib/references.bib"),
  abstract: [
    TODO
  ],
)

= Definitions and building blocks <definitions-and-building-blocks>
#remark("Notation")#linicrypt_notation_summary

Additionally, I want to note these facts about basis change.
- We can apply a basis change #B to a program #PIOC.
  If $#B in F^(d times d)$ is invertible then $#P#B$ is defined as the program corresponding to $(#I#B, #O#B, #C#B)$.
  There is a formal framework to show that this represents the same Linicrypt program.

The main idea for tackling Linicrypt programs in the no-nonces setting is to use basis change and generalize it to any non-square, non-invertible matrices.
This was the driving reason for the generalizations we defined in my master's thesis.

We have to allow for the "algebraic representations" #PIOC to be much freer.
Essentially anything with consistent dimensions should be allowed,
and all definitions and theorems should still be applicable.
A triple $(#I, #O, #C)$ is called a "pseudo-algebraic representation" if all the rows of the matrices are in $F^(1 times d)$.
Then we can use a core lemma that relates the solution spaces $#sol[#C]$
between transformed constraints,
which follows essentially from the associativity of the matrix product.

I want to state the definition of collision structure for these pseudo-algebraic representations.

#definition("Collision structure")[
  Let $#P = lr((#I , bold(O) , #C))$ be a "pseudo-algebraic representation".
  We say #C has a collision structure if we can split #C as $#C = #Ccs union.sq #Cfix$ and find a non-trivial subspace $#Fixing subset.eq #F^(1 times d)$ such that
  // #set enum(numbering: "(a)")
  $
    #Ccs #text[is deterministically solvable fixing] (rowsp(Cfix) + rowsp(O)) plus.circle #Fixing.
  $
]

#remark[
  - The fixed constraints #Cfix and the backwards solvable constraints #Ccs are equivalent to the constraints before and after $i^*$ in the original collision structure definition.
  - Degeneracy is a natural edge case of this defintion, i.e. $#Ccs = {}$.
  - The subspace #Fixing corresponds to the variables in #P which we can set freely and still solve the constraints.
    It plays the same role as the $#q _(i^*)$, which is not in the span of previously fixed variables.
]

The attack follows from the definition of the collision structure:
We are given a $#vv in #sol[#C]$.
In particular, it also solves $#Cfix$.
We fix the values for all the dual vectors contained in $rowsp(Cfix) + rowsp(O)$.
Then we choose any other value than $bold(f)#vv$ for $bold(f) != 0 in #Fixing$.
By the lemma on the structure of $#sol[#C]$,
we have a deterministic Linicrypt program computing a solution $#vv'$ for $Ccs$ taking these fixed values as input.
This solution is our collision,
as we have $#I#vv != #I#vv'$ (injectivity of #I on the solutions),
$#vv' in #sol[#C] = #sol[#Ccs] sect #sol[#Cfix] $ (by the definitions)
and $#O#vv = #O#vv'$ (by the choice of $#vv'$).

We can therefore state the following theorem, which combines all the previously described attacks for both the random oracle model, and the ideal cipher model.

#theorem[
  Let $(#I , bold(O) , #C)$ be a pseudo-algebraic representation with a collision structure
  $#C = #Ccs union.sq #Cfix$.
  Assume we already know a $#vv$ in $#sol[#C]$.

  Then there is a Linicrypt program that can output a $#vv'$ in $#sol[#C]$ with $#vv != #vv'$ and
  $#O#vv = #O#vv'$ by making $|#Ccs|$ queries to $H$.
]<theorem-collision-structure>

The definition of the solution set (in the ROM) is the following.
#definition("Solution of constraints")[
  Let $#C$ be a set of constraints of dimension $d$.
  We say a vector $#vv in #F^d$ #strong[solves] $#C$ if
  $#a #vv = H(#Q #vv)$ for all $#Q arrow.r.bar #a$ in $#C$.
  Such a vector $#vv$ is called a #strong[solution] of $#C$.
  The set of all solutions to $#C$ is denoted by $#solH(C)$.
]

The definition works for any function $H$,
and we will just write $#sol[#C]$ and omit the $H$ from the notation.

TODO: maybe I should put here the definition for deterministically solvable,
and the lemma about the structure of $#sol[#C]$.

The central lemma that is used in the conjecture below is:

#lemma("Transformation of constraints")[
  Let #C be a set of constraints of dimension $d$ and
  let $#T$ be a matrix in $F^(d times d')$ where $d'$ can be arbitrary.
  Then we have
  $
    #vv in #sol[#C#T] <==> #T#vv in #sol[#C]
  $
]<lemma-sol-commutes>

#proof[
  Let #C and #T be as in the lemma.
  The following equivalences prove the lemma:
  $
    &#vv in #sol[#C#T] \
<=> &(#a') #vv = H((#Q') #vv) quad forall (#Q', #a') in #C#T \
<=> &(#a#T) #vv = H((#Q#T) #vv) quad forall (#Q, #a) in #C \
<=> &#a (#T #vv) = H(#Q (#T #vv)) quad forall (#Q, #a) in #C \
<=> &#T#vv in #sol[#C]
  $
]

The equivalence between lines 2 and 3 looks strange,
because $#C'$ could have fewer constraints than #C,
but it is correct.
This lemma holds for _any_ function $H$.

= Conjecture

I am sure that the conjecture still needs tweaking.
But in this form, the attack side already kind of works, and it explains all the examples I have found.
The next step would be to try to break the conjecture by finding more complicated counter examples.

#conjecture("Formulation version 1")[
  Let #P = (#I, #O, #C) be a Linicrypt program.
  and assume there is an injective #T in $M^(d times d')$ such that
  #set enum(numbering: "(a)")
  + $#P#T$ has a collision structure, or
  + There exists a basis change $#B != bb(1)$ in $M^(d' times d')$ with $#C#T#B = #C#T$ and $#O#T#B = #O#T$ and $#I#T != bb(0)$

  Then there exists an attack on collision resistance against #P. If both (a) and (b) are not the case for any injective #T, then #P is collision-resistant.
]<conjecture-no-nonces>

With this formulation there are these issues:
+ For (a), we need that $#C#T$ is solvable,
  so that we can actually find any #vv in #sol[#C#T]
+ For (b), we need to be able to find a #vv in #sol[#C#T] with $#B#vv != #vv$
+ Also, #I#T needs to be injective on #sol[#C#T]

The last two issues are not issues if #T is the identity.
Then 2. is satisfied because $H$ is assumed to look random,
and cannot fulfill a linear relationship.
And 3. is satisfied anyways by the Lemma on the structure of a solvable #C.

#conjecture("Formulation version 2")[
  Let #P = (#I, #O, #C) be a pseudo algebraic representation of a Linicrypt program.
  #P is not collision resistant if and only if at least one of these conditions hold:
  #set enum(numbering: "(a)")
  + $#P$ has a collision structure.
  + There exists a basis change $#B != bb(1)$ with $#C#B = #C$ and $#O#B = #O$.
  + There is an injective map #T in $#F^(d' times d)$ and a submatrix $#I'$ of #I
    such that $#P' = (#I'#T, #O#T, #C#T)$ is a pseudo algebraic representation for which (a) or (b) hold.
]<conjecture-no-nonces-v2>

= Attack Side

The attack side works for this conjecture.
The conjecture is enough to explain all CR-insecure examples that I tried.
But the security proof still has a few "holes" in the argumentation,
even though a lot of things seem to go right.
Here I want to prove the direction: If (a), (b) or (c) is true
then there is a collision resistance attack on #P.

#proof[
  == Case (a)
  This is given by #ref(<theorem-collision-structure>)

  == Case (b), the permutation attack
  Assume that we have $#C#B = #C$ and $#O#B = #O$ for a non-trivial basis change #B.
  Note, that this is only possible due to there being no nonces in the constraints.
  Because $#C$ is an unordered set of constraints,
  #C#B can be equal to #C if #B manages to permute the constraints in #C.

  Then let #vv be in $sol(#C )$ such that $#B #vv != #vv$.
  It is possible to find such a #vv with very high probability simply by choosing any #vv randomly out of #sol[#C].
  If #sol[#C] was contained to any subspace of $#F^d$ like the eigenspace of #B,
  then $H$ is definitively not independently random.

  #remark[
    This can be made precise by switching to the canonical algebraic representation,
    where the input and the answer vectors are all orthogonal.
    Then #sol[#C] is a graph on top of $X := #ker[#I]^tack.t$.
    Because $H$ is a random oracle, any point above $X$ is equally likely,
    so the probability that the graph lies in a subspace is negligible.
  ]

  By the #ref(<lemma-sol-commutes>) we have $#vv in #sol[#C ] = #sol[#C  #B] <=> #B#vv in #sol[#C ]$.
  Finally, as we have assumed that $#O#B = #O$ we get that:
  $
    #O#B#vv = (#O#B) #vv = #O#vv
  $
  By choice of #vv we have $#B#vv != #vv$,
  therefore $#I#B#vv != #I#vv$ are a collision for #P.

  == Case (c), the collapse of queries
  Assume that $#P' = (#I'#T, #O#T, #C#T)$ is a pseudo algebraic representation for which (a) or (b) hold.
  Now by the attack proofs for case (a) and case (b) we get a $#vv != #vv'$ in #sol[#C#T]
  such that $(#O#T)#vv = (#O#T)#vv'$.
  We have $#I'#T#vv != #I'#T#vv'$ by the bijection between #sol[#C#T] and $#I'#T$ because $#P'$ is a pseudo algebraic representation.

  Now we can apply #ref(<lemma-sol-commutes>) which gives us in this context the following equivalence:
  $
    #vv in #sol[#C #T] <==> #T #vv in #sol(C)
  $

  Putting it all together we have $#T#vv != #T #vv'$, which are both in $#sol(C)$ and fulfill the equation $#O (#T#vv) = #O (#T#vv')$.
  So #I#T#vv and $#I#T#vv'$ are collisions for #P.

  #remark("Unsolvable constraints")[
    Something that could be interesting to look at is what algebraic conditions does #T need to fulfill so that #C#T is still solvable.
    Intuitively #T should not create loops in the constraints,
    where we need the output of some queries to determine the inputs to exactly these queries.
    This plays into the same problem of trying to better understand unsolvable set of constraints.
    Sometimes properties of $H$ can also make unsolvable #C actually easy to solve,
    for example if $H$ has fixed points, then the "point loop" $#C = {#q |-> #q}$ has a solution.
  ]

]

= Examples for the attack side

== Collapsing program from McQuoid, Swope, Rosulek
This is the example that the authors of @TCC:McQSwoRos19 used to highlight why
the plain collision structure characterization fails in the setting without nonces.

#align(center + horizon)[
  #grid(
    columns: 2,
    gutter: 2em,
    algo(
      // title: [$#P _sans("collapse")$], parameters: ($x$, $y$),
      header: $underline(#P (x,y))$,
      line-numbers: false, inset: 0.7em, fill: none, block-align: left,
    )[
      $a_1 &:= H(x)$ \
      $a_2 &:= H(y)$ \
      $a_3 &:= H(a_1)$ \
      return $a_3 - a_2$
    ],
    algo(
      header: $underline(sans("Algebraic Representation of ") #P (x,y))$,
      line-numbers: false,
      inset: 0.7em,
      fill: none,
      stroke: 0pt,
      block-align: left,
    )[
      #v(0.5em)
      $bold(O) &:= mat(0,0,0,-1,1) \
        bold(I) &:= mat(1,0,0,0,0;
                       0,1,0,0,0)$ \
      $#C = {
        &mat(1,0,0,0,0) &|-> mat(0,0,1,0,0), \
        &mat(0,1,0,0,0) &|-> mat(0,0,0,1,0), \
        &mat(0,0,1,0,0) &|-> mat(0,0,0,0,1)
      }$
    ],
  )
]

The attack for this program is to input $(x, H(x))$ for any $x in #F$ because $#P (x, H(x)) = 0$.

What happens is that $#a _2$ and $#a _3$ collapse during the execution of #P on these inputs.
This can be represented by the matrix #T defined as:
#let myT = $mat(
  1,0,0;
  0,1,0;
  0,1,0;
  0,0,1;
  0,0,1;
  )$
$
  #T = #myT
$

Then the program #P#T is specified by $(#I'#T, #O#T, #C#T)$ with $#I'$ being only the first row of #I and
#align(center)[
  #grid(
    columns: 3,
    gutter: 2em,
    [$#C#T = {mat(1,0,0) |-> mat(0,1,0), mat(0,1,0) |-> mat(0,0,1)}$],
    [$#I'#T = mat(1,0,0)$],
    [$#O#T = mat(0,0,0)$.],
  )
]

Note, that $#C#T$ is not deterministically solvable fixing $rowsp(#I#T)$.
But it is solvable fixing only $rowsp(#I' #T)$.
The key thing is that #P#T now has a collision structure!

We can split $#C#T = #Ccs#T union.sq #Cfix#T$ with $#Ccs#T = #C#T$ and $#Cfix#T = {}$.
If we set $#Fixing = rowsp(mat(1,0,0))$ then we get that #Ccs#T is detereminstically solvable fixing
$
  (rowsp(#Cfix#T) + rowsp(#O#T) plus.circle #Fixing = rowsp(mat(1,0,0)).
$

Therefore case (c) of #ref(<conjecture-no-nonces-v2>) is fulfilled.

Here I write out exactly what happens in the proof for this concrete example.
By solving #Ccs#T (i.e. running the attacking Linicrypt program) in two different ways by fixing a different value for $mat(1,0,0)#vv$,
we get two distinct #vv and $#vv'$ in $#sol[#C#T]$.
They have the form:
$
  #vv = mat(x;H(x);H(H(x))) != mat(x';H(x');H(H(x'))) = #vv'
$

Now, by the #ref(<lemma-sol-commutes>) we get the solutions for #C by applying #T from the other side.
$
  #T#vv = #myT #vv = mat(
  x;
  H(x);
  H(x);
  H(H(x));
  H(H(x));
  )
$

These lead to the expected colliding inputs to #P: $#I#T#vv = mat(x; H(x))$ and $#I#T#vv' = mat(x'; H(x'))$.

== Collapse Attack: One of the 5 broken PGV compression functions in the rate-2 setting

This example should work for any of the 5 compression functions listed in @C:BlaRogShr02 in
the section "Fatal Attacks on Five of PGV’s B-Labeled Schemes".

I will choose the compression function they call $hat(f)_39$ and call it $f$.
$
  f(h,m) = E(h+m, h+m) + m
$
The Merkle-Damgard like construction that I will use starts with the IV = 0.
This constant could also be passed in as another input and output, or it could be set to IV = H(0).
I believe all three approaches are equivalent in the end.

#import "@preview/fletcher:0.4.2" as fletcher: node, edge

#let icc(x, k, y) = [
  #fletcher.diagram(
    cell-size: 8mm,
    $
      #x edge(#k, <->)  & #y \
    $,
  )
]

#align(center + horizon)[
  #grid(
    columns: 2,
    gutter: 2em,
    algo(
      // title: [$#P _sans("collapse")$], parameters: ($x$, $y$),
      header: $underline(H^2_f (m_1,m_2))$,
      line-numbers: false, inset: 0.7em, fill: none, block-align: left,
    )[
      $h_0 := 0$ \
      $y_1 := E(h_0 + m_1, h_0 + m_1)$ \
      $h_1 := y_1 + m_1$ \
      $y_2 := E(h_1 + m_2, h_1 + m_2)$ \
      $h_2 := y_2 + m_2$ \
      return $h_2$
    ],
    algo(
      header: $underline(sans("Algebraic Representation of ") #P (x,y))$,
      line-numbers: false,
      inset: 0.7em,
      fill: none,
      stroke: 0pt,
      block-align: left,
    )[
      #v(0.5em)
      $bold(I) &:= mat(1,0,0,0;
                       0,1,0,0) \
        bold(O) &:= mat(0,1,0,1)$ \
      $#C = lr({
        &#icc($mat(1,0,0,0)$, $mat(1,0,0,0)$, $mat(0,0,1,0)$),\
        &#icc($mat(1,1,1,0)$, $mat(1,1,1,0)$, $mat(0,0,0,1)$)
      }, size: #50%)$
    ],
  )
]

The goal is now to find a $#T'$ such that the two queries collapse.
I first try to find a $#T'$ in $#F^(4 times 4)$ and then I remove the zero columns to make it an injective matrix.
I write down the equations to make the second query collapse onto the first query:

$
  mat(1,0,0,0) #T' &= mat(1,0,0,0) \
  mat(0,0,1,0) #T' &= mat(0,0,1,0) \
  mat(1,1,1,0) #T' &= mat(1,0,0,0) \
  mat(0,0,0,1) #T' &= mat(0,0,1,0)
$

This system of equations has a solution:
$
  #T' = mat(
  1,0,0,0;
  0,0,-1,0;
  0,0,1,0;
  0,0,1,0;
  )
$
And if we remove the second and fourth column, we get a #T as in #ref(<conjecture-no-nonces>):
$
  #T = mat(
  1,0;
  0,-1;
  0,1;
  0,1;
  )
$

#remark[
  I don't have an algorithm for finding these $#T$ yet.
  Also, I believe that such an algorithm has to be in NP-hard in the number of constraints,
  because in @hollenberg_complete_2022 they showed that finding the collapsing potential is NP-hard.
  This doesn't seem to be a problem to me,
  as exponential computation in the number of base variables is still doable.
  And if we had lots of base variables,
  we probably have a very specific structure (like in the MD-construction) which we can exploit for faster algorithms.
]

The collapsed program is then
#align(center)[
  #grid(
    columns: 3,
    gutter: 2em,
    [$#C#T = { (mat(1,0), mat(1,0), mat(0,1)) }$],
    [$#I'#T = mat(1,0)$],
    [$#O#T = mat(0,0)$.],
  )
]

This is the same case as the previous example,
the $#C#T$ is solvable fixing the output and fixing $mat(1,0)$.
Because this program has a collision structure (specifically it is degenerate) we get solutions in $#sol[#C#T]$,
i.e. any $#vv = (x,E(x,x))$ for $x$ in #F is in $#sol[#C#T]$.
We map it to collisions of #P via #I#T, so every
$#I#T #vv = (x, -E(x,x))$ for $x$ in #F
collides with each other.

This is the same result as in @C:BlaRogShr02,
except that they work in a field of characteristic 2 where $-1 = 1$ and hence they omit the minus sign.

This example highlights the power of the Linicrypt approach.
It seems to me that the original PGV paper did not find these attacks,
but here these attacks can be discovered by solving algebraic conditions on the algebraic representation of the program.

== Non example for the collapse attack: The 8 group-2 schemes
I tried the scheme $f(h,m) = E(m, h) + m$.
For it, the equations to make the constraints collapse are inconsistent,
so no #T can exist that collapses the queries.

#remark[
  It also doesn't work if one tries to collapse $y_2$ onto $x_1$.
  This "reverse and collapse" seems like an interesting attack.
  I want to check if this attack is possible for any of the PGV functions in the Merkle Damgard construction.
  But considering the amount of work that has been done on this topic,
  I don't think there will be a PGV compression function for which this attack is actually a new attack.
]

== Permuation attack: The compression functions marked as (P) in PGV
One of the compression functions that is attackable by the Permutation Attack in PGV is
$f(h,m) = E(m,m) + h$.

#align(center + horizon)[
  #grid(
    columns: 2,
    gutter: 2em,
    algo(
      // title: [$#P _sans("collapse")$], parameters: ($x$, $y$),
      header: $underline(H^2_f (m_1,m_2))$,
      line-numbers: false, inset: 0.7em, fill: none, block-align: left,
    )[
      $h_0 := 0$ \
      $y_1 := E(m_1, m_1)$ \
      $h_1 := y_1 + h_0$ \
      $y_2 := E(m_2, m_2)$ \
      $h_2 := y_2 + h_1$ \
      return $h_2$
    ],
    algo(
      header: $underline(sans("Algebraic Representation of ") #P (x,y))$,
      line-numbers: false,
      inset: 0.7em,
      fill: none,
      stroke: 0pt,
      block-align: left,
    )[
      #v(0.5em)
      $bold(I) &:= mat(1,0,0,0;
                       0,1,0,0) \
        bold(O) &:= mat(0,0,1,1)$ \
      $#C = lr({
        &#icc($mat(1,0,0,0)$, $mat(1,0,0,0)$, $mat(0,0,1,0)$),\
        &#icc($mat(0,1,0,0)$, $mat(0,1,0,0)$, $mat(0,0,0,1)$)
      }, size: #50%)$
    ],
  )
]

With these constraints #C we can do a collapse attack like before, which will lead to the collisions
$(x,x)$ for $x$ in #F.

But what is also possible is the permutation attack due to the symmetry in #C _and_ #O under #B for
$
  #B = mat(
    0,1,0,0;
    1,0,0,0;
    0,0,0,1;
    0,0,1,0;
  ).
$

We have $#C#B = #C$ as required in #ref(<conjecture-no-nonces>) with $#O#B = #O$.
So, if we take any $#vv$ in $#sol[#C]$, the chances are very high that it does not lie
in the eigenspace for 1 of $#B$ so that $#B#vv != #vv$.
Specifically, we can take any input $(x, y)$ to #P for $x != y$
and use #P to compute the corresponding #vv in $#sol[#C]$ by setting $#vv = mat(x,y,H(x),H(y))^(tack.b)$.

Then by #ref(<conjecture-no-nonces-v2>), we get the second preimage $#I#B#vv = (y,x)$.

== A more interesting permutation attack
Let $#P (x , y) = H(x) + H(y + H(x))$.
The algebraic representation has two constraints:
#align(center)[
  #grid(
    columns: 3,
    gutter: 2em,
    [$#C = { mat(1,0,0,0) |-> mat(0,0,1,0), quad mat(0,1,1,0) |-> mat(0,0,0,1) }$],
    [$#I = mat(1,0,0,0; 0,1,0,0)$],
    [$#O = mat(0,0,1,1)$],
  )
]

The only possible non-identity basis change leaving #C intact,
exchanges these two queries.
We can set up a system of 4 vector equations for #B so that the first query and answer row vector is exchanged with the second when we apply #B.
We find that this #B is the unique solution to the system of equations:
$ #B = mat(0, 1, 1, 0;1, 0, 0, -1;0, 0, 0, 1;0, 0, 1, 0) $

This #B leaves both #C and #O unchanged
(i.e. $#C#B = #C$ and $#O#B = #O$) so the conditions of the permutation attack are fulfilled.

An arbitrary vector from #sol[#C] is for example
$#vv = mat(x,y,H(x),H(y+H(x)))^tack.b$ for some $x != y$ in #F.
It is the execution vector for the input $(x,y)$ to #P.

By applying #I#B to #vv we get the second preimage
$
  #I #B #vv = (y + H(x), x - H(y + H(x))).
$

This is not just a permutation of the two inputs,
but a permutation between input and query base variables.
The combined symmetry in #C and #O enable this attack.
This symmetry and this attack are not obvious at first glance,
which makes the abstract formulation of the permutation attack from #ref(<conjecture-no-nonces-v2>) valuable.

= Merkle Dåmgard construction in Linicrypt

We want to see if the conjecture can correctly reproduce previous classifications of the PGV compression functions.
Linicrypt can explain most of the previous categorizations,
xcept for the Permutation attack and the 5 flawed backward attackable functions.
TODO add a summary of the last section of my master's thesis that goes into detail.

Now I will try to tackle these last missing functions with the help of #ref(<conjecture-no-nonces-v2>).
We use the variables $a,b,c,d,e,f in {0,1}$ as @C:BlaRogShr02:

$
  f(h,m) = E(c h + d m, e h + f m) + a h + b m
$

If we see this as a Linicryp program, this is its canonical representation:
#align(center)[
  #grid(
    columns: 3,
    gutter: 2em,
    [$#I = mat(1,0,0;0,1,0)$],
    [$#O = mat(a,b,1)$.],
    [$#C = { (mat(e,f,0), mat(c,d,0), mat(0,0,1)) }$],
  )
]

Now consider the Merkle Dåmgard construction with 2 calls to $f$.
We will pass in the IV called $h_0$ as the first argument to the program.

#align(center + horizon)[
  #grid(
    columns: 2,
    gutter: 2em,
    algo(
      // title: [$#P _sans("collapse")$], parameters: ($x$, $y$),
      header: $underline(H^2_f (h_0;m_1,m_2))$,
      line-numbers: false, inset: 0.7em, fill: none, block-align: left,
    )[
      $h_1 := f(h_0, m_1)$ \
      $h_2 := f(h_1, m_2)$ \
      return $h_2$
    ],
    algo(
      // title: [$#P _sans("collapse")$], parameters: ($x$, $y$),
      header: $underline(H^2_f (h_0;m_1,m_2))$,
      line-numbers: false, inset: 0.7em, fill: none, block-align: left,
    )[
      $y_1 := E(c h_0 + d m_1, e h_0 + f m_1)$ \
      $h_1 := y_1 + a h_0 + b m_1$ \
      $y_2
      &:= E(c h_1 + d m_2, e h_1 + f m_2) \
      &=  E(c y_1 + c a h_0 + c b m_1 + d m_2, e y_1 + e a h_0 + e b m_1 + f m_2)
      $ \
      $h_2
      &:= y_2 + a h_1 + b m_2 \
      &:= y_2 + a y_1 + a^2 h_0 + a b m_1 + b m_2
      $ \
      return $h_2$
    ],
  )
]

On the right I spelled out the Linicrypt program in the canonical basis $(h_0, m_1, m_2, y_1, y_2)$.
In this case, the canonical basis is not the most pretty basis to work in for this program.
If we were to add more calls to the compression functions the expressions get more and more complicated.

This is the algebraic representation of $H^2_f$ in this basis:
#align(center)[
  #table(columns: 3, gutter: 2em,stroke:0pt,align:horizon,
    [$#I = mat(
      1,0,0,0,0;
      0,1,0,0,0;
      0,0,1,0,0;
    )$],
    [$#O = mat(1,0,0,0,0;a^2,a b,b,a,1)$.],
    // [$#C#T = {
    //   (mat(e,f,0), mat(c,d,0), mat(0,0,1)),
    //   (mat(e,f,0), mat(c,d,0), mat(0,0,1))
    // }$],
    $#C = mat(delim:"{",gap:#1em,
      (mat(e,f,0,0,0), mat(c,d,0,0,0), mat(0,0,0,1,0));
      (mat(e a,e b,f,e,0), mat(c a,c b,d,c,0), mat(0,0,0,0,1));
    )$
  )
]

In this basis, it is very hard to see the originally very clean structure of the construction.
This is due to two issues.
First, we need to sort the basis variables in a way that mimics the structure of the construction.
This would be $(h_0, m_1, y_1, m_2, y_2)$.
In this basis (we switched $y_1$ and $m_2$) we have:

#align(center)[
  #table(columns: 3, gutter: 2em,stroke:0pt,align:horizon,
    [$#I = mat(
      1,0,0,0,0;
      0,1,0,0,0;
      0,0,0,1,0;
    )$],
    [$#O = mat(1,0,0,0,0;a^2,a b,a,b,1)$.],
    // [$#C#T = {
    //   (mat(e,f,0), mat(c,d,0), mat(0,0,1)),
    //   (mat(e,f,0), mat(c,d,0), mat(0,0,1))
    // }$],
    $#C = mat(delim:"{",
      (mat(e,f,0,0,0), mat(c,d,0,0,0), mat(0,0,1,0,0));
      (mat(e a,e b,e,f,0), mat(c a,c b,c,d,0), mat(0,0,0,0,1));
    )$
  )
]

Now we can start to see the pattern that these matrices follow.

But, because we are allowed to represent the Linicrypt program in any basis,
we can also just directly choose the basis $(h_0, m_1, h_1, m_2, h_2)$.
Here the basis change idea really shines,
because it helps to simplify the algebraic representation.

#align(center)[
  #table(columns: 3, gutter: 2em,stroke:0pt,align:horizon,
    [$#I = mat(
      1,0,0,0,0;
      0,1,0,0,0;
      0,0,0,1,0;
    )$],
    [$#O = mat(1,0,0,0,0;0,0,0,0,1)$.],
    // [$#C#T = {
    //   (mat(e,f,0), mat(c,d,0), mat(0,0,1)),
    //   (mat(e,f,0), mat(c,d,0), mat(0,0,1))
    // }$],
    $#C = mat(delim:"{",
      (mat(e,f,0,0,0), mat(c,d,0,0,0), mat(-a,-b,1,0,0));
      (mat(0,0,e,f,0), mat(0,0,c,d,0), mat(0,0,-a,-b,1));
    )$
  )
]

The pattern is now clear,
and we can easily see what the algebraic representation of $H^n_f$ would be like for $n$ arbitrarily high.

== Implementation of the permutation attack in SymPy

I used SymPy to find permutation matrices that attack these programs,
the code is here @semmel2024linicrypt.
I implemented only the permutation attack on $H^2_f$ for now.
That is, we set up all the equations so that $c_1$ and $c_2$ are switched when we apply #B.
$
  c_1 #B = c_2 quad "and" quad c_2 #B = c_1
$
Because #C is an *unordered* set, any solution #vv to #C implies that #B#vv is a solution to #C as well.
If we add the constraints to #B that the output matrix is untouched:
$
  #O #B = #O
$
and solve for such a #B with any linear constraints solver (here I use SymPy),
we can list out all the programs $H^2_f$ where such an attack is possible.

I tried to solve these equations by hand.
It looks like it should be possible to find a nice characterization for what $H^n_f$ are susceptible to this attack,
but I just failed to solve the linear equations parametrized by $a,b,c,d,e,f$.
The task is not to find a solution,
but to find the conditions on $a,b,c,d,e,f$ such that there is either no solution,
one solution or many solutions.

There are 12 such programs.
As a sanity check: The 5 programs that are marked with (P) in @C:PreGovVan93 and with (f) in @C:BlaRogShr02 are contained in these 12.
These are the permutation attacks where one can switch $m_1$ with $m_2$ in the input and get the same output.
But the other seven additional permutation attacks can be broken down like this:
+ 3 degenerate programs (2 of type (-) and (a) and one of type (D) but it should be classified as (-))
+ 2 programs of type (D) and (b)
+ 2 programs of type (B) and (g)

#remark("On the degenerate programs")[
  One of the programs is marked as (D) in @C:PreGovVan93,
  but the compression function doesn't use the inputs independently,
  so it is essentially susceptible to the same attack as when it just uses one of the two inputs.

  The permutation attack matrix #B is not unique, there is a high dimensional subspace of possible matrices.
  This is a phenomenon I don't fully understand,
  but kind of what happens is that the matrix #B maps one of the inputs to all its equivalent inputs.
  As the inputs to a degenerate program are not used independently,
  there is a subspace of inputs that "looks the same" to the program.
  The matrix #B then kind of maps one of these inputs to the rest of them.
  Interestingly, this is kind of a "hack",
  as the matrix kind of misuses some non-zero value from the solution vector to achieve this affine transformation with just a linear transformation.

  I found multiple such examples during my master's thesis.
  I think it would be super interesting to allow for affine transformations,
  these would then easily capture degeneracy via this symmetry idea.
  But this means that one has to extend Linicrypt to work with affine combinations of its variables,
  not linear combinations.
  But it seems that essentially the same theory can be built.
]
#remark("On the programs of type (D) and (b)")[
  These are not marked as (P) in @C:PreGovVan93 because the authors specified an order of attacks,
  and (D) is higher up the list than (P).
]
#remark("New fatal attacks on the programs of type (B) and (g)")[
  This is what I find most interesting!
  The paper @C:BlaRogShr02 described new 5 fatal attacks on the schemes previously classified as (B).
  These attacks all work in the same way,
  i.e. they cause two independent queries to $E$ to collapse.
  The algorithmic implementation of #ref(<conjecture-no-nonces-v2>) found a *different* attack on two of them.
  This attack instead causes the two queries to happen in reversed order.
  By the conjecture, we get a single second-preimage to almost every possible input.
]

== New attack on 2 of the 5 (B) and (g) labeled schemes

The two compression functions of type (B) and (g) which are susceptible to a permutation attack are:
$
  f_43 (h,m) &= E(h+m, 0) + h \
  f_59 (h,m) &= E(h+m, h+m) + h
$

As the attack is the same for both, let $f$ be any of those two in the following.
The basis change matrix with the properties for the permutation attack ($c_1 #B = c_2, c_2#B = c_1, #O#B=#O$) is for $H^2_f$:
$
  #B = mat(
   1,0, 0,0, 0;
  -1,0, 1,1, 0;
   1,0,-1,0, 1;
   0,1, 1,0,-1;
   0,0, 0,0, 1;
)
$

Let $(h_0, m_1, m_2)$ be any input to $H^2_f$.
The conjecture says it should have a second preimage:
$
  (h'_0, m'_1, m'_2) := (h_0, -h_0 + h_1 + m_2, m_1 + h_1 - h_2)
$
Note, that $h'_0 = h_0$ is a side effect of putting this IV in the input and output of $H^2_f$.

Here we do the lengthy calculation for $f_43$ to convince ourselves that it is indeed a second preimage.
Everything cancels out and we get the same output.

#algo(
  header: $underline(H^2_f_43 (h_0, -h_0 + h_1 + m_2, m_1 + h_1 - h_2))$,
  line-numbers: false,
  inset: 0.7em,
  fill: none,
  block-align: center,
  row-gutter: 14pt,
)[
  $y'_1
    &:= &E(h'_0 + m'_1, 0) \
    &= &E(h_0 -h_0 + h_1 + m_1,0)\
    &= &E(h_1 + m_1,0) = y_2$ \
  $h'_1
    &:= &y'_1 + h'_0 = &y_2 + h_0$ \
  $y'_2
    &:= &E(h'_1 + m'_2, 0) \
    &= &E(y_2 + h_0 + m_1 + h_1 - h_2, 0)\
    &= &E(y_2 + h_0 + m_1 - y_2, 0)\
    &= &E(h_0 + m_1, 0) = y_1$ \
  $h'_2
    &:= &y'_2 + h'_1 \
    &= &y_1 + y_2 + h_0 = &h_2$ \
  return $h'_2$
]

Now, what are these second preimages? When are they proper second preimages, and not the same preimage again?
If we solve this equation for $m_1$ and $m_2$
$
  (h_0, m_1, m_2) := (h_0, -h_0 + h_1 + m_2, m_1 + h_1 - h_2),
$
we get exactly the collisions that @C:BlaRogShr02 found.
They found that all the inputs of this form
$
  (h_0, h_0 + c, E(c, c) + h_0 + c),
$
for $c in #F$ arbitrary,
will collapse the queries and lead $H^2_f_43$ to output $h_0$.
That leads to the following conclusion,
which is still very puzzling to me:
For the program $H^2_f_43$ every input is either:
+ In the set of collisions found by @C:BlaRogShr02,
+ or it has a single second preimage generated by the permutation matrix #B.

This means we broke second-preimage resistance for every input now,
not only for the inputs in the specific subspace described by the attack in @C:BlaRogShr02.
But there is no freedom in choosing the second preimage for $H^2_f$.

This also hints towards some missing deeper theory that explains this.
My guess is that these things are explained by something like the orbit and stabilizer from some kind of representation.
And I hope that by formulating the Linicrypt theory in some way making use of the language from group actions and representations
we can
- simplify the attack proofs,
- simplify the formulation of all possible attacks (i.e. optimize the conjecture),
- better understand the core of what a Linicrypt program is
- and hopefully find an easy proof for the security side.

=== More inputs to $H$

I checked with the SymPy program that this attack holds up for dimensions up to 6 (checking all combinations of $a,b,c,d,e,f$ takes a couple of seconds then already...).
The attack is a permutation of the $n$ constraints like this:
$
  c_1 -> c_2 -> ... -> c_n -> c_1,
$
where the arrows represent the application of the permutation matrix #B.

Therefore each input $#i _1$ to $H^n_f_43$ has $n-1$ second preimages described by:
$
  #i _2 = #B^1#i \
  #i _3 = #B^2#i \
  ... \
  #i _n = #B^n#i = #B^0#i = #i \
$

= Security Side

== Ideas for the proof
Just some random notes.

General proof idea of #ref(<conjecture-no-nonces-v2>):
- (a), (b) or (c) $=>$ attack is done
- Reverse: Assume adversary finds collisions $#vv != #vv'$ in #sol[#C] under $#O$ ($#O#vv = #O#vv'$),
  then (a), (b) or (c)

We have:
- Protocol of $#Att$ interacting with orcale $H$ (or $E$ or $Pi$) with $N$ queries
- From #vv and #vv' and the protocol we can extract $T, T': #C -> [N]$ when each constraint was determined.
- We define $#fin (c) = sans("max")(#Ti (c), #Ti' (c))$ for each $c$ in #C.
- We define #Cfix to be the maximal subset such that $#Ti = #Ti'$ on #Cfix and $#Ccs = #C \\ #Cfix$

=== Base case
$#Ti$ and $#Ti'$ are each injective and $#Ti (#Ccs) sect #Ti' (#Ccs) = {}$

This is the case that they have in the unique nonces paper.
Then $#fin$ is injective.

=== Case: Collapse of queries

==== Easy case first: simultaneous collapse

Assume $T$ and $T'$ is not injective,
so there is a $i != j$ such that $T(c_i) = T(c_j)$ and $T'(c_i) = T'(c_j)$.
By definition of $T$ and $T'$ we have $c_i #vv = c_j #vv$ and $c_i#vv' = c_j#vv'$.

Here $c#vv$ just means $(#Q#vv, #a#vv)$ in the random oracle case.

Now I want to find an injective matrix #T in $#F^(d' times d)$
through which $c_i$ and $c_j$ collapse.
And the $#P#T$ (meaning $(#I#T, #O#T, #C#T)$) should then be a
pseudo-algebraic representation for which we can build an attack by using $#Att$.

The natural injective matrix $#T$ which collapses $c_i$ and $c_j$
is a matrix for which the columns are a basis of $ker(c_i - c_j)$.
This matrix is injective because the columns for a basis of the subspace.
In the following we use the basis $#vv _1, ..., #vv _d'$.

The previous idea of taking #vv and $#vv'$ as the columns is a much smaller matrix in general.

The key with this #T is that we can easily translate the attack on $#P$ to an attack on $#P#T$.
First, it collapses $c_i$ and $c_j$:
$
  c_i#T = c_i mat(#vv _1, ..., #vv _d') = c_j mat(#vv _1, ..., #vv _d') = c_j #T
$

So $#C#T$ has at least one constraint less, as these two have collapsed.
Also, #vv and $#vv'$ are in the image of #T, because its columns form a basis of $ker(c_i - c_j)$.

So there are preimages $ww$ and $ww'$ to $vv$ and $vv'$ means by #ref(<lemma-sol-commutes>)
$
  ww in #sol[#C#T] <==> #T ww in #sol[#C],
$
that $#ww$ and $#ww'$ are in $#sol[#C#T]$.
The reason for finding these

Now we have reduced the attack $#Att$ to an attack on $#P#T$:
- $#ww != #ww'$ in $#F^d'$ are solutions to $#C#T$
- Also $#O#T#ww = #O#T#ww'$
- We can apply the conjecture for the lower dimensional case $#P#T$

The key thing that is missing here is that $#P#T$ should be an algebraic representation up to basis change
of some program, so that we can apply the conjecture for a lower dimension by induction.

Key issue:
- $#C#T$ needs to also be solvable (for the examples it always is)

Ideas:
- If $#C#T$ is not solvable, then it would have been hard for the attacker to collapse those two queries.
- This only works if we look at the whole set of collapsed queries.
  It might be hard to collapse $c_i$ and $c_j$ without collapsing some other queries,
  but easy once you do.
- My guess nr 1: The pairs of constraints that $#Att$ could collapse need to be "independent" (to be defined).
- Guess nr 2: When they are independent there would also exist a matrix $#B$ permuting these queries.
  So maybe that is a line of attack.


Lets assume $#C#T$ is not solvable.

*New idea*:
But the attacker has already computed the states $#ww$ and $#ww'$ in $#sol[#C#T]$.
If we can prove that it is hard to find solutions to unsolvable constraints,
then we can use that to complete this step of the proof.

== Unsolvability of constraints

I want to reformulate the definition of solvable constraints to make it nicer to work with.

#definition("Solvable constraints")[
  <def_solvable>
  Let $#C$ be a finite set of constraints of dimension $d$,
  and let $#Fixing _0$ be a subspace of #Vd.
  $#C$ is #strong[solvable fixing] $#Fixing _0$ if there exists an ordering
  $(c_1, ... , c_n)$ of $#C$ such that the condition below is fulfilled.
  We define for all $i = 1 , ... , n$ the spaces $Fixing_i = Fixing_(i-1) + span(c_i)$.

  Solvability condition: $aa_i in.not Fixing_(i-1) + span(#Q _i) quad$ where $(QQ_i, aa_i) := c_i$
]

We call $(c_1 , ... , c_n)$ a solution ordering of $#C$ fixing $Fixing_0$.
If $Fixing_0 = {0}$ we just say $CC$ is solvable, dropping the "fixing" notation.

In the ideal cipher model,
we only have to change the solvability condition.
It will allow either $mat(kk; xx)$ or $mat(kk; yy)$ to be the query $QQ$.

#definition("Deterministically solvable")[
  <def_det_solvable>
  Let $#C$ be a solvable set of constraints with solution ordering $(c_1, ..., c_n)$.
  $#C$ is #strong[deterministically solvable fixing] $Fixing_0$ if $Vd = Fixing_0 plus.circle #span[$aa_1, ..., aa_n$]$.
  In other words, we require $d = dim(Fixing_0) + n$ in addition to the solvability condition.
]

This dimension condition forces $span(QQ_i) in Fixing_(i-1)$,
which is the condition we previously used in the definition.

Deterministically solvable is closest to the definition of collision structure in @TCC:McQSwoRos19.
Collision structure is more complicated because it also includes splitting up the constraints into a fixed part and a deterministically solvable part.
Also, deterministically solvable constraints are in a one-to-one relationship with Linicrypt programs,
up to basis change.
That means every Linicrypt program has a deterministically solvable set of constraints fixing $Fixing_0 = rowsp(II)$.
On the contrary, for every solvable set of constraints,
there exists a basis such that the set of constraints is the algebraic representation of a Linicrypt program.

=== Solvable security game

Now we can define a security game for finding solutions to a set of constraints #CC.
The adversary #Att gets access to the constraints $CC$ of dimension $d$,
a description of the space $Fixing_0$ and the oracle $H$.
Then the game randomly samples a #ii in #Vp and passes it to #Att.
This vector represents the input to a Linicrypt program.
It wins the game by outputting a $vv in sol(CC)$ with $vv - ii in ker(Fixing_0)$.

The probability of #Att winning this game is written as $SolAdv[Att, CC, Fixing_0]$.

A useful fact is that we can avoid working with $Fixing_0$ because of the following proposition.

#proposition("Collapse of input")[
  Let #C be a set of constraints of dimension $d$ and $Fixing_0$ a subspace of #Vd.
  We define the embedding map $LL: ker(Fixing_0) arrow.hook Vp$.
  Then the following are equivalent:
  1. #C is solvable fixing $Fixing_0$
  2. $|CC LL| = |CC|$ and $CC LL$ is solvable (fixing ${0}$)
]

In Linicrypt program terms,
this proposition relates a Linicrypt program with its corresponding inputless Linicrypt program where all inputs are set to 0.

#proof[
  We define #C, $Fixing_0$, and $LL$ as in the proposition statement.
  #remark[
    The linear map $LL$ induces corresponding map on the dual spaces $LL^*: Vd -> (ker(Fixing_0)^*)$.
    With a bit of abuse of notation, we can extend this map $LL^*$ to act on constraints.
    Constraints are tuples of matrices.
    The rows of the matrices are in $Vd$,
    so we can let $LL^*$ act on these structures elementwise.
    Then $LL^* ((QQ, aa)) = (QQ LL, aa LL)$.

    TODO: This is useful in multiple places, so it should be discussed outside this proof.
  ]

  We will first prove a useful fact.
  Let $CC = (c_1, ..., c_n)$ be an ordering and $CC LL = (c_1 LL, ..., c_n LL)$ the corresponding ordering.
  Regardless of whether the solvability condition is fulfilled,
  we can define the sequence of subspaces $Fixing_i$ from the ordering of $CC$ and $Fixing'_i$ from the ordering of $CC LL$.
  We set $Fixing'_0 = LL^*(Fixing_0) = {0}$.
  Then we have $Fixing'_i = LL^*(Fixing_i)$ by the following inductive argument:
  $
    Fixing'_i &= Fixing'_(i-1) + span(c_i LL) \
    &= LL^*(Fixing_(i-1)) + span(c_i LL) \
    &= LL^*(Fixing_(i-1) + span(c_i)) \
    &= LL^*(Fixing_i)
  $


  We first assume $CC LL$ has a solution ordering $CC LL = (c_1 LL, ..., c_n LL)$.
  This is a well-defined ordering because $LL$ didn't collapse any constraints by $|CC LL| = |CC|$.
  // We can view this as a bijective map $phi: CC LL <-> [n]$.
  // Take the induced map $LL^*: CC -> CC LL$.
  // Because of $|CC LL| = |CC|$ this is a bijection.
  // When we take the concatenation $LL^* compose phi$ we get an ordering of $CC$,
  // i.e. $CC = (c_1, ..., c_n)$.
  This gives us the ordering $CC = (c_1, ..., c_n)$.
  Assume towards a contradiction that there is an $i$ with $aa_i in Fixing_(i-1) + span(QQ_i)$.
  We can apply $LL^*$ to this equation to get
  $
    aa_i LL in Fixing'_(i-1) + span(QQ_i LL),
  $
  a contradiction with the assumed solution ordering of $CC LL$.

  Now we prove the reverse direction and assume $CC$ is solvable fixing $Fixing_0$ with ordering $(c_1, ..., c_n)$.
  First, we show that $|CC| = |CC LL|$.
  Assume $c_i LL = c_j LL$ for an $i <j$.
  This implies in particular that $0 = (aa_i - aa_j)LL ww$ for all $ww in ker(Fixing_0)$.
  Therefore $ker(Fixing_0) subset.eq ker(aa_i - aa_j)$.
  It follows that $aa_i - aa_j in Fixing_0$ and $aa_j in Fixing_0 + span(aa_i)$.
  This directly contradicts with the solvability condition $aa_j in.not Fixing_(j-i) + span(QQ_j)$ because $Fixing_0 + span(aa_i) subset.eq Fixing_(j-1)$.

  Now that we have $|CC| = |CC LL|$ we get a well-defined ordering $CC LL = (c_1 LL, ..., c_n LL)$.
  Let us assume this is not a solution ordering and we have for some $i$ that
  $aa_i LL$ is contained in $Fixing'_(i-1) + span(QQ_i LL)$.
  It follows that $LL^*(aa_i) = LL^*(bb)$ for some $ bb in Fixing_(i-1) + span(QQ_i)$.
  As before, we can move the equations around to get this sequence of implications:
  $
    & (aa_i - bb)LL ww = 0 quad "for any" quad ww in ker(Fixing_0) \
    ==> & ker(Fixing_0) subset.eq ker(aa_i - bb) \
    ==> & aa_i - bb in Fixing_0 \
    ==> & aa_i in Fixing_(i-1) + span(QQ_i)
  $
  The last equation would be a contradiction to the solution ordering $(c_1, ..., c_n)$.
]

This proposition is useful because we can then translate statements about solvability fixing ${0}$ to the more general version.
In some sense,
we only need to understand inputless Linicrypt programs to understand all Linicrypt programs.

#theorem("Unsolvable constraints -- wrong")[
  Let #C be a set of constraints of dimension $d$ which are not solvable.
  Every program #Att making $N$ request to the oracle
  has a winning probability bounded by
  $
    SolAdv[Att, CC] < N / (|#F|).
  $
]

#remark[
  This is why I thought it could work:
  The key idea of why this should work is that the condition of being unsolvable
  is one of the form "vector is contained in subspace".
  This cannot be broken by a linear map, even when it is not injective.
  The vector after the mapping stays in the subspace after the mapping.

  *UPDATE:* Yes, but, if the linear map collapses the problematic constraints,
  then it doesn't matter that it stays in the subspace.
]

#remark[
  *Good news and bad news.*
  Bad news:
  It does not work like this.
  Counterexample:
  $
    CC = {mat(1,0,0) |-> mat(0,0,1), mat(0,1,0) |-> mat(0,0,1)}
  $
  is unsolvable.
  But with $LL = mat(1,0; 1,0; 0,1)$,
  the set $CC LL = { mat(1,0) |-> mat(0,1)}$ is solvable.
  So solutions of $CC LL$ can be mapped to solutions of $CC$,
  i.e. vectors of the form $mat(x;x;H(x))$ for $x in FF$.

  The good news is, that it means we still have room for an NP problem.

  *Idea to try to save it:*
  Call a set of constraints $CC$ completely unsolvable if $CC LL$ is unsolvable for all linear maps $LL$.
  Then we might be able to prove the Theorem for completely unsolvable sets.
  This is surprisingly similar in structure to the original conjecture.

  Caveat: This means we still need at least an algorithm for determining if a set of constraints
  is completely unsolvable.
  I would guess this problem is then NP-hard.
]


#definition("Completely unsolvable")[
  A set of constraints $CC$ is called *completely unsolvable* if $CC LL$ is unsolvable for every linear map $LL$.
]

The relevant maps are those which collapse constraints.
It is probably enough to consider only the maps $LL: ker(c_i - c_j) arrow.hook Vp$
recursively.

#theorem("Unsolvable constraints -- not yet useful")[
  Let #C be a set of constraints of dimension $d$ which are completely unsolvable.
  Every program #Att making $N$ request to the oracle
  has a winning probability bounded by
  $
    SolAdv[Att, CC] < N / (|#F|).
  $
]<theorem-unsolvable>



I want to try to refine this theorem further,
because like this it is not fully useful.
The issues are:
- In the proof of the conjecture, we have $CC LL$, which we want to be either solvable or very hard to solve
- If it is not solvable, it might still not be completely unsolvable as in the theorem
- What we want is for it to be solvable in a subspace (the one where a solution was found),
  or to be difficult to solve in that subspace

We refine the solvability definition.

#definition("solvable -- fixing and outside")[
  #C is solvable outside of a subspace $W$ of #Vp fixing a subspace #Fixing of #Vd
  if there exists a linear map $f: #F^(d') -> Vp$ with $im(f) subset.eq.not W$ s.t.
  $f^*(#C)$ is solvable fixing $f^*(Fixing)$.
]

If $W = {0}$ we will just say #C is solvable fixing #Fixing.
If $Fixing = {0}$ we will just say #C is solvable outside of $W$.

This language of being solvable outside of a subspace is useful in describing collision resistance.
There we are looking for solutions $vv$ and $vv'$ of constraints,
under the extra condition that $vv != vv'$.
This condition can be encoded with this new definition.

TODO more explicit.

Now we can define a security game for finding solutions to a set of constraints #CC.
The adversary #Att gets access to the constraints $CC$ of dimension $d$,
the subspaces $Fixing$ and $W$ of #Vd and #Vp respectively.
The adversary #Att also gets acces to the oracle $H$ such that we can record its queries.
Then the game randomly samples a vector #ii in #Vp (representing the Linicrypt program input) and passes it to #Att.
It wins the game by outputting a $vv in sol(CC)$ which fulfills $vv - ii in ker(Fixing)$
and $vv in.not W$.

The probability of #Att winning this game is written as $SolAdv[Att, CC, Fixing, W]$.

#theorem("Unsolvable constraints V2")[
  Let #C be a set of constraints of dimension $d$ and $W$ a subspace of #Vp.
  Assume $CC$ is not solvable outside of $W$.
  Every program #Att making $N$ request to the oracle
  has a winning probability bounded by
  $
    SolAdv[Att, CC, {0}, W] < N / (|#F|).
  $
]<theorem-unsolvable-2>

#sketch[
  We record the queries by #Att in the function $T: #C -> [N]$ which maps
  each constraint onto the time when it was determined by a call to $H$.
  We assume #Att is successful,
  and outputs a #vv in $sol(CC)$ with $vv in.not W$.

  This $T$ might not be injective.
  We attempt an inductive proof over $n$ the number of constraints in $CC$.
  So we assume the theorem holds for all sets $CC$ with $|CC| < n-1$.

  When $T$ is injective, we can do the core step of the main proof from @TCC:McQSwoRos19.
  This is the one where we show the result of a call to $H$ was already determined beforehand,
  via an equation where the left is randomly chosen,
  and the right is a linear combination of known values.
  This means that #Att was very lucky if we assume $H$ is a random oracle.
  This equation can be derived from assuming #C is not solvable outside of $W$.
  Because this means, in particular, #C is not solvable itself.
  No matter what ordering of #C we choose,
  for some $i$ the negated solvability condition implies a linear equation with $aa_i #vv$ on the left side,
  and previously determined values on the right side.

  Now assume $T$ is not injective.
  Then let $c_i$ and $c_j$ be two different constraints that are determined at the same time,
  i.e. $T(c_i) = T(c_j)$.
  Then $vv$ is in $ker(c_i - c_j)$.
  Also, because $vv in.not W$, we know that $ker(c_i - c_j)$ is not contained in $W$.

  We can define the linear map $f: ker(c_i - c_j) arrow.hook Vp$ which is just the embedding.
  So this map goes from a smaller state space to the state space of our constraints #C.

  This map induces a map on the dual spaces $f^*: Vd -> ker(c_i - c_j)^*$,
  i.e. a map acting on variables of a Linicrypt program, or here, the components of the constraints.
  So we can use it to map our constraints to a different set of constraints of smaller dimension $f^*(CC) = CC f$.
  Because the $i$'th and $j$'th constraint collapse under $f$ we have $|f^*(CC)| <= |CC| - 1$

  Because $vv$ is in the image of $f$ and outside of $W$,
  the adversary #Att has thus found a solution $ww$ to $f^*(CC)$ where $f ww = vv$
  and also $ww in.not f^(-1)(W)$.

  But $f^*(CC) := CC f$ is not solvable outside of $f^(-1)(W)$.

  Assume it was, i.e.
  there is a $g: U -> ker(c_i - c_j)$ such that $CC f g$ is solvable and $im(g) subset.eq.not W$.
  Then $f g$ is a map as in the definition of $CC$ being solvable outside of $W$.
  We assumed this was not the case in the theorem statement.


  By induction, we can apply the Theorem for $f^*(CC)$ and $f^(-1)(W)$ to get
  $
    SolAdv[Att,CC] <= SolAdv[Att, f^*(CC)] <= N / (|FF|).
  $

  #remark[
    Here the actual factor on the right-hand side has to be different I think.
  ]

  The base case for the induction is a set of constraints with just a single unsolvable constraint
  $CC = {c} = {(QQ, aa)}$.
  No matter the dimensionality of $c$,
  this set is completely unsolvable.
  This is because $a in span(QQ)$ implies $aa LL in span(QQ LL)$ for any linear map $LL$.
  For this singleton set any map $T: CC -> [N]$ is injective and we can use the original proof for that case.
]


Maybe we can use a general theorem like the unsolvability theorem to replace the proofs
for collision structure and second preimage characterization.
The key step in the proof of unsolvability is the same as in those proofs.

Let $#P$ be a Linicrypt program.
We can duplicate its algebraic representation such that the vectors are completely separate.
One copy has all zeros on the right of the row vectors,
and the other has all zeros on the left.
Then we can merge the algebraic representations,
by doing a union on the constraints,
adding the input spaces,
and concatenating the output matrix.
Call this program $#P _"join"$.
We can look at a map $f$ that has as its image the states in $FF^(2d)$ where the output
of $#P _"join"$ has both halves equal. i.e.:
$
  OO_"join" = mat(OO_1; OO_2), quad Cjoin = CC_1 union CC_2, quad Fixing_"join" = Fixing_1 + Fixing_2 \
  f: ker(OO _1 - OO _2) arrow.hook FF^(2d)
$
We define $Proj_1$ and $Proj_2$ to be the projections from $F^(2d)$ to either the first n dimensions or the second n.
So $Proj_1$ and $Proj_2$ recover the solutions to $CC$ from the first $n$ variables, or the second $n$ variables respectively.

Then finding a $vv in sol(Cjoin f)$ with $vv in.not ker(Proj_1 - Proj_2)$ means finding collision for $#P$.

#corollary("Collisions in general")[
  $Cjoin f$ is solvable outside of $ker(Proj_1 - Proj_2)$
  is equivalent to $PP$ being susceptible to an easy attack against collision resistance.
]<corollary-cr>

Now that we have a formal definition of solutions outside of a subspace,
we can try to prove it.

#sketch[
  Assume that #Att finds a solution easily.
  Easy means with a higher probability than in the unsolvability theorem.
  Then that theorem gives us a map $g: U -> ker(OO_1 - OO_2)$ such that $Cjoin f g$
  is solvable and $im(g) subset.eq.not ker(Proj_1 - Proj_2)$.
  So a solution to $Cjoin f g$ is a solution to $Cjoin$ when mapped by $f g$.
  Let $vv$ be such a solution to $Cjoin$ with $vv in.not ker(Proj_1 - Proj_2)$.
  By construction then $Proj_1 vv$ and $Proj_2 vv$ are solutions to $CC$ with $Proj_1 vv != Proj_2 vv$.

  On the reverse side, assume there is such an $g$ as above because $Cjoin f$ is solvable outside of $ker(Proj_1 - Proj_2)$.
  Then computing solutions to $Cjoin$ takes at most $2n$ queries to $H$.
  As before, a solution outside of $ker(Proj_1 - Proj_2)$ leads to a collision.
  This means we have found an attack on collision resistance.
]

#remark[
  In this proof, in the last step, I need to actually find a solution outside of $W$ just given the solution ordering.
  There we need to be a bit careful.
  Maybe the oracle $H$ is not random, and actually causes all solutions to lie on the subspace $W$ again.
  But for a random $W$ the solution space is never contained in a subspace.
]

=== TODOs this section
- Write down lots of examples to see how this works in all the special cases
- Prove that a solution ordering like the above leads to a case from the conjecture
- Pederson Hash

=== Examples

See [https://github.com/frederiksemmel/linicrypt] for examples in the ideal cipher model and in the random oracle model.
That repository contains
- An implementation of the CR charaterization from #ref(<corollary-cr>)
- Building the Merkle Damgard construction from PGV compression functions
- It reproduces the CR and 2PR charaterization from BRS, including the secure & insecure functions of type 'B'
- It confirms that the example $P(x,y) = H(H(x)) - H(y)$ is not CR but it is 2PR

It gives a natural attack characerization: Each left-right symmetric set partition of $Cjoin$ is an attack type.
These attack types overlap mostly with previous categorizations, and for the differences this Lincicrypt characterization is arguably better.


TODO flesh out these ideas:
- All CR attacks on a Linicrypt program are given by considering the subspaces of $ker(OO_1 - OO_2)$
  in which the constraints of $f^*(Cjoin)$ collapse.
  For each subspace, if the 

== Notes and ideas, in random order
- Second preimage resistance and collision resistance loose their relationsship for unsolvable constraints.
  We can find unsolvable constraints where its easy to find a second solution, if we are given a solution.
  But its hard to find a solution in the first place.
  This is due to the permutation attack; where the symmetry of the constraints leads to a symmetry in the set of solutions.
  This is contrary to the solvable case, where finding second preimages is harder than finding collisions.
  Note: For the unique nonces case @TCC:McQSwoRos19 found that both notions are equivalent.
  It's interesting to see that in the more general no nonces case they split, but one is stronger that the other,
  and in the most general case they are unrelated.

- The set $sol(CC)$ has interesting structure.
  For matrices permuting constraints $CC BB = CC$ we get a well defined map $BB: sol(CC) -> sol(CC)$.

  For general matrices $LL: FF^(d') -> Vp$ for arbitray $d'$ we get a map $LL: sol(CC LL) -> sol(CC)$.

  It looks like the set of solutions contains "components",
  where each component is the solution set of the "derived" set of constraints mapped linearly into $Vp$.
  With derived constraints I mean the constraints that we can build by mapping them linearly.
  I think the only interesting cases are when we map them such that some constraints are collapsed and we are left with a solvable set.
  Then I would expect finding solutions to be easier (less constraints), and we can map them back.

- If the function $H$ allows for fixed points,
  that opens another can of (intersting) worms.
  Because then unsolvable sets become solvable in a limited way.
  $CC = {mat(1) |-> mat(1)}$ is then solvable (fixing ${0}$) because
  $sol(CC)$ are exactly the fixed points ${x | H(x) = x}$.
  This set of solutions can be used to find solutions to every? unsolvable set.

  E.g. $CC = {mat(1, 0) |-> mat(0,1), mat(0,1) |-> mat(1,0)}$ can be collapsed via
  $LL = mat(1;1)$ to ${mat(1) |-> mat(1)}$.
  Therefore solutions to

- Maybe it is cleaner to drop the idea of input matrix $II$ and of the fixing $Fixing_0$ space.
  We could model Linicrypt input as just another set of constraints.
  We already have random oracle constraints and ideal cipher constraints.
  Now we introduce input constraints $c = ii$ for $ii$ in $Vd$.
  They restrict the valid states of $PP$ in the dimension $ii$.
  We instantiate them with a concrete input $i in FF$: $ii vv = i$.
  This is structurally similar to the random oracle constraint,
  which is instantiated with a concrete orcle $H$: $H(QQ vv) = aa vv$.

  Benefits:
  - The collapse of the input matrix is now handled by collapse of constraints.
  - We allow extra freedom in the solution ordering which seems more general.
    Previously we kind of require the inputs to $PP$ to be fixed first.
    With lots of programs,
    it would be ok to start computing constraints without knowing all the input.
    This is the case for merkle damgard for example.

= Meeting Notes

== Meeting 28.08.2024
- Results from the experiments
  - PGV BRS categorization
  - Overview implementation, interesting parts
- Maximal attacks & set partitions
- Towards proof of original conjecture
  - Issue with collapse of different constraints in left and right program
  - Symmetric attacks, always present? Set partition join of attacks?
- Discuss possibel applications of corollary:
  - Better categorization of all PGV compression functions in MD construction
  - Model the fixed point weekness of the random oracle from PGV -> Aren't all programs then vulnerable?
    - Maybe some programs force collapse to $mat(0) |-> mat(0)$ ($H(0) = 0$) and some only $mat(1) |-> mat(1) $ ($H(x) = x$)
  - Start a search for best compression function from ideal ciphers

== Meeting 11.09.2024
- No work these two weeks, only lots of excuses :)
- Timeline paper. October 3 not possible...
  - Submission deadline Crypto 2025 in February seems good

- Formal conferences is TCC and Eurocrypt
  - TCC in deadline in May probably
  - Crypto is usually more real application focused, would need to find a really good application for that

= Next steps

== Attack side
=== Short term
- Try to model fixed point attacks like this.
  Additionally to the solvability rules we add: $mat(xx) -> mat(xx)$ is solvable fixing $Fixing$ if $xx$ is not in $Fixing$ 
- Apply this to the PGV compression functions and see which are insecure

== Longer term
- derive a linicrypt categorization of the pgv functions



== Security side
- Formalize proofs of unsolvability and the corollary
