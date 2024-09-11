// style
#set math.mat(delim: "[", )
#set math.equation(numbering: "(1)")

// operations
#let exec(x) = $sans("exec")(#x)$
#let sol(x) = $sans("sol")(#x)$
#let solH(x) = $sans("sol")_H (#x)$
#let ker(x) = $sans("ker")(#x)$
#let im(x) = $sans("im")(#x)$
#let rows(x) = $sans("rows")(#x)$
#let rowsp = $sans("rowsp")$
#let span(body) = $angle.l #body angle.r$
#let max(x) = $sans("max")(#x)$

// spaces, programs
#let F = $bb("F")$
#let FF = $bb("F")$
#let C = $cal("C")$
#let CC = $cal("C")$
#let P = $cal("P")$
#let PP = $cal("P")$
#let Fixing = $cal("F")$
#let Vp = $bb("F")^d$
#let Vd = $(bb("F")^d)^*$

#let Cjoin = $cal("C")_"join"$

// crypto
#let Att = $cal("A")$
#let Adv = $sans("adv")$
#let SolAdv = $serif("SOL")sans("adv")$
#let Ti = $T$
#let fin = $sans("finish")$

// matrix stuff
#let vv = $bold(v)$
#let ww = $bold(w)$
#let I = $bold(I)$
#let II = $bold(I)$
#let O = $bold(O)$
#let OO = $bold(O)$
#let B = $bold(B)$
#let BB = $bold(B)$
#let T = $bold(T)$
#let TT = $bold(T)$
#let L = $bold(L)$
#let LL = $bold(L)$
#let LLd = $bold(L)^*$
#let q = $bold(q)$
#let qq = $bold(q)$
#let Q = $bold(Q)$
#let QQ = $bold(Q)$
#let a = $bold(a)$
#let aa = $bold(a)$
#let bb = $bold(b)$
#let i = $bold(i)$
#let ii = $bold(i)$
#let kk = $bold(k)$
#let xx = $bold(x)$
#let yy = $bold(y)$
#let Proj = $bold(P)$
#let MM = $bold(M)$

// constraints shortcuts
#let cs = $italic("cs")$
#let fix = $italic("fix")$
#let crit = $italic("crit")$
#let Ccs = $#C _#cs$
#let Cfix = $#C _#fix$
#let Ccrit = $#C _#crit$
#let Ics = $#I _#cs$

#let equiv(v, c) = $[#v]_#c$
#let quotient(a, b) = $#move(dy: -0.1em, a) slash.big #move(dy: 0.1em, b)$


// convenience
#let PIOC = $#P = (#I, #O, #C)$


#let linicrypt_notation_summary = [
  This is a summary of the notation and definitions that I am using.
  - $d$ is the number of base variables of $#P$, $k$ the number of input variables, $l$ the number of output variables and $n$ the number of constraints.
  - The state space of the program #P is $#F^d$
  - The function going from the inputs of a deterministic #P to the values of the base variables (the state space) is called $b_(#P) : #F^k arrow #F^d$
  - Instead of $#vv _(sans("base"))$ I will just write $#vv$
  - The set of base variables one can get by executing a Linicrypt program #P on all of its inputs is called $#exec[#P]$
  - The set of solutions to a set of constraints #C is called $#sol[#P]$
  - The input matrix to #P is called #I and the output matrix is called #O so I will write #PIOC for a Linicrypt program and its algebraic representation
  - The function that a determinsitic #P computes is called $f_(#P) = bold(O) circle.tiny b_(#P)$
]
