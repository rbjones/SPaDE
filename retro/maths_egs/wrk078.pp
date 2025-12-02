=IGN
********************************************************************************
wrk078.doc: this file is supplementary material for the ProofPower system

Copyright (c) 2004 Lemma 1 Ltd.

This file is supplied under the GNU General Public Licence (GPL) version 2.

See the file LICENSE supplied with ProofPower source for the terms of the GPL
or visit the OpenSource web site at http:/www.opensource.org/

Contact: Rob Arthan < rda@lemma-one.com >
********************************************************************************
wrk078.doc,v 1.29 2010/03/03 11:35:32 rda Exp
********************************************************************************
=IGN
make -f maths_egs.mkf pdf
docsml wrk078
xpp wrk078.doc -d maths_egs -i wrk078 &
doctex wrk078 wrk078.th; texdvi -b wrk078; texdvi wrk078; texdvi wrk078
=TEX
\documentclass[11pt,a4paper,leqno]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}
\usepackage{url}
\tabstop=0.4in
\def\ThmsI#1{%
{\vertbarfalse#1}}

\def\ThmsII#1#2{%
{\vertbarfalse
\begin{minipage}[t]{0.48\hsize}
#1
\end{minipage}
\begin{minipage}[t]{0.48\hsize}
#2
\end{minipage}}}

\def\ThmsIII#1#2#3{%
{\vertbarfalse
\begin{minipage}[t]{0.32\hsize}
#1
\end{minipage}
\begin{minipage}[t]{0.32\hsize}
#2
\end{minipage}
\begin{minipage}[t]{0.32\hsize}
#3
\end{minipage}}}

\def\Hide#1{\relax}

\makeindex
\title{Mathematical Case Studies: \\ --- \\ Trees\thanks{
Added to repo 21 September 2010;
for full changes history see: \protect\url{https://github.com/RobArthan/pp-contrib}.
}}
\author{Rob Arthan}
\makeindex
\author{R.D. Arthan \\ Lemma 1 Ltd. \\ rda@lemma-one.com}
\date{\FormatDate{\VCDate}}

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This {\ProductHOL} script defines a type of labelled trees with arbitrary finite branching.
\end{abstract}

\vfill
\begin{centering}

\bf Copyright \copyright\ : Lemma 1 Ltd 2010--\number\year \\
Reference: LEMMA1/HOL/WRK078; Current git revision: \VCVersion
% Don't forget to restore the above to dollar Revision: dollar when editing, if necessary.
% (The makefile uses -kv when it checks documents out). 

\end{centering}
\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
\tableofcontents
%\newpage
%\subsection{Document cross references}

% \newpage
\subsection*{To Do}
A great deal of work remains.



{\raggedright
\bibliographystyle{fmu}
\bibliography{fmu}
} %\raggedright
%%%%
%%%%
%%%%
%%%%
\newpage
\section{INTRODUCTION}
%%%%
%%%%
%%%%
%%%%
This {\ProductHOL} script defines a type of labelled trees with arbitrary finite branching.
This material is included in the mathematical case studies because it
is needed to represent terms in the treatment of universal algebra in
\cite{LEMMA1/HOL/WRK080}.  The development has been
lifted wholesale from the FEF proofs where trees were used to model
information-flow security properties of structured data (an indication
of the wide range of application of the tree concept)!
While the material is of small mathematical interest in its own right,
it is noteworthy that the representations and proofs
developed {\em ad hoc} for the FEF work turn
out to be almost identical with those used for $\Omega$-word
algebras in Cohn's Universal Algebra \cite{Cohn81}.

The material has been packaged separately from
\cite{LEMMA1/HOL/WRK080} purely for technical convenience. (Separate packaging means that the principle of recursive definition by trees
can be invoked automatically while processing the specification paragraphs in \cite{LEMMA1/HOL/WRK080}.)


This document is a {\Product} literate script. It contains all the metalanguage (ML) commands required to create several theories, populate them with the formal definitions and prove and record all the theorems.
The descriptions include all the formal definitions in the Z-like concrete syntax for specification in {\ProductHOL}.
and a discussion of the theorems that have been proved about the objects specified.
There is an index to the formal definitions and the theory listings in section~\ref{index}.

%%%%
%%%%
%%%%
%%%%
\subsection{Technical Prelude}

First of all, we must give the the ML commands to  introduce the new theory ``trees'' as a child of the theory ``seq'' that introduces, {\it inter alia}, the function {\em Elems} that maps a list to the set of its elements.

=TEX
%%%%
%%%%
%%%%
%%%%
=SML
force_delete_theory"trees" handle Fail _ => ();
open_theory"seq";
new_theory"trees";
app new_parent ["set_thms"];
set_merge_pcs["basic_hol1", "'sets_alg"];
=TEX

\section{SIGNATURE}\label{SIGNATURE}
We will define an induction principle and a proof context
which we document here.
=SML
signature ⦏Trees⦎ = sig
=TEX
=DOC
	val ⦏tree_induction_tac⦎ : TERM -> TACTIC;
=DESCRIBE
This tactic implements induction over the type $'a\;TREE$ of $'a$-labelled trees with arbitrary finite branching defined in the
theory $trees$.
=FRULE 2 Tactic
tree_induction_tac ⌜x⌝
├
{ Γ } t 
├
strip{∀ x'⦁ x' ∈ Elems xs ⇒ t[x'/x], Γ}
t[(MkTree (l, xs))/x]
=TEX
where $x$ has type $\tau\;TREE$ for some type $\tau$.
The variables $l$ and $xs$ introduced by the tactic have types
$\tau$ and $\tau\;TREE\;LIST$ respectively.
=ENDDOC
=SML
end (* of signature Trees *);
=TEX
=DOC
(* Proof Context: ⦏'trees⦎ *)
=DESCRIBE
A proof context for the theory $trees$. 
\paragraph{Contents}

Rewriting:
=GFT
⊢ ∀x y⦁ MkTree x = MkTree y ⇔ x = y
=TEX
Stripping theorems:
=GFT
⊢ ∀x y⦁ MkTree x = MkTree y ⇔ x = y
=TEX
Stripping conclusions:
=GFT
⊢ ∀x y⦁ MkTree x = MkTree y ⇔ x = y
=TEX
Existential clausal definition theorems:
=GFT
tree_prim_rec_thm, tree_prim_rec_thm1
=TEX
Automatic proof procedures are respectively $basic\-\_prove\-\_tac$,
$basic\-\_prove\-\_conv$ and no existence prover.

\paragraph{Usage Notes}
Requires theory $trees$.
=ENDDOC

%%%%
%%%%
\section{A TYPE OF TREES}\label{TREES}
To represent terms in algebras we need a type of arbitrary branching trees with natural number labels on the nodes.

\subsection{Generalities on Recursive Types}
This section supplies some material which assist in defining recursive types.
We are concerned with providing guidelines supported by theorems rather than a fully automatic approach.
The point of view we take is more like that of \cite{Arthan91} than the universal-algebraic view of \cite{Melham89}.
Both of those references are mainly concerned with recursive types which arise from what are called finitary inductive definitions (this is explicit in \cite{Arthan91} and implicit in \cite{Melham89}).
The advantage of Melham's universal algebra point of view is that it leads directly to principles justifying definitions over the recursive type (indeed it begins from such principles);
however, the rules for introduction of new constants in HOL prohibit one from using a universal mapping property as a defining property, so one must use explicit abstraction and representation functions to define the constructors etc. even though their definitions are never needed later.

For the present treatment, we make full use of the assumption that the recursive type is defined by a finitary inductive definition.
Intuitively, finitariness implies that the follow process will eventually yield each element of the type: {\em(i)} start with an empty stock of elements; {\em(ii)} apply the constructor functions for the type to everything we have already and add the results to our stock; {\em(iii)} repeat {\em(ii)}.

To formulate the idea formally, we assume that we are given the data shown in the following diagrams:


{\def\normalisebaselines{\baselineskip20pt
  \lineskip3pt \lineskiplimit3pt}
\def\mapright#1{\smash{
    \mathop{\longrightarrow}\limits^{#1}}}
\def\mapdown#1{\Big\downarrow
    \rlap{$\vcenter{\hbox{$\scriptstyle#1$}}$}}

$$\matrix{%
	'D		& \mapright{k}	& 'T\cr
\mapdown{c}			&		& \mapdown{w}\cr
	'T\,SET		& 		& ℕ\cr
\ \cr
	('T \rightarrow\ 'y)	& \mapright{M}	& ('D \rightarrow\ 'Y)}$$}

In the first diagram, $k$ is intended to be the constructor function for the free type.
Thus $'T$ is the free type itself, and $'D$ is the domain type of the constructor function.
If we are concerned with free types given as disjoint unions, then $'D$ is to be the relevant disjoint union, so that there is just {\em one} constructor function.
In {\ProductML} terms, $k$ is analogous, for example, to the generalised constructor function $mk\_simple\_type$ rather than the pair of constructors $mk\_vartype$ and $mk\_ctype$.
$c$ is to be a function which maps an element, $x$ say, in the domain of the constructor function to the set of elements of $'a$ out of which $x$ is constructed
(cf. the function {\sf contents} used in \cite{Arthan91}).
In terms in the iterative construction of the free type described abov,
$w(t)$ tells us when we are going to acquire $t$.
We refer to $c$ and $w$ as the {\em content} and {\em weight} functions, respectively.

In the second diagram, $'y$ represents a type to serve as the codomain of a recursive function on $'T$.
In the applications, $'D$, will in fact be obtained from $'T$ by applying some combination of type constructors (typically, constant types, product, disjoint union and the list type constructor).
$'Y$ stands for the corresponding type construction applied to $'Y$.
$M$ is intended to be the functional which lifts a function, $f$, from $'T$ to $'y$ to the corresponding function $M(f)$, from $'D$ to $'Y$, where $M(f)$ works by applying $f$ to the $'T$ components of an element of $'D$. (N.B. in general, no appropriate $M$ need exist, however, there will be a suitable $M$ in the case of all the type constructors just listed).

In fact, the theory we will develop below does not very much on the fine tuning of the weight and content functions. For example, $c(x)$ may give either every constituent of $x$ or just the immediate constituents.
The following polymorphic set of quadruples describes what we will require:


ⓈHOLCONST
│	FinitaryRecType : (
│			('D → 'T)
│		×	('D → 'T SET)
│		×	('T → ℕ)
│		×	(('T → 'y) → ('D → 'Y))) SET
├──────────────
│	FinitaryRecType =
│	{	(k, c, w, M)
│	|	OneOne k
│	∧	(∀t:'T⦁ ∃x:'D⦁ c(x) ⊆ {z | w(z) < w(t)} ∧ t = k(x))
│	∧	(∀i g⋎1 g⋎2⦁ (∀y⦁ w(y) < i ⇒ g⋎1(y) = g⋎2(y))
│			⇒ ∀x⦁ c(x) ⊆ {y | w(y) < i} ⇒ M(g⋎1)(x) = M(g⋎2)(x))}
■

I.e., we require the constructor function to be one-to-one and that every element, $t$, of $'T$ can be obtained by applying the constructor function to some $x$ whose contents have strictly smaller weight than that of $t$.
We also require a kind of monotonicity property on $M$, telling us that if two functions agree on elements up to a certain weight then so does their lifting with $M$.
We will derive an induction principle from the above assumptions by course-of-values induction on the value of the weight function.

The condition on $M$ in the definition of $FinitaryRecType$ has been chosen to be the weakest condition for which the necessary proofs go through conveniently.
The following shows that a somewhat stronger condition which will often be easy to prove is also sufficient.
This condition has the advantage of only involving $c$ and $M$.
We say that $M$ is a {\em local functional} with respect to $c$ when the condition holds.
ⓈHOLCONST
│	LocalFunctional : ((('T → 'y) → ('D → 'Y)) × ('D → 'T SET)) SET
├───────────────────
│	LocalFunctional =
│	{	(M, c)
│	|	∀I g⋎1 g⋎2⦁ (∀y⦁ y ∈ I ⇒ g⋎1(y) = g⋎2(y))
│			⇒ ∀x⦁ c(x) ⊆ I ⇒ M(g⋎1)(x) = M(g⋎2)(x)}
■

\subsection{A Type of Trees}
We are now going to use the material of the previous section to construct a specific recursive type.
What we are going to construct is the HOL analogue of the type defined in ML as follows:

=GFT Standard ML Example
	datatype 'a TREE = MkTree of ('a * (('a TREE) list));
=TEX
The elements of the type may be thought of as trees.
At each node in one of these trees there is an element of the type parameter $'a$ and a list of sub-trees.
Alternatively, one can think of the trees as formal expressions formed using the elements of $'a$ as operator symbols.


We need a type in which to represent the type of trees.
Our choice is lists of number-$'a$ pairs.
Viewing the trees as formal expressions, an expression formed using an element $x:'a$ as an operator with $n$ operands will be represented by the list comprising $(n, x)$ followed by the representations of the operands.
This is essentially just the usual prefix way of writing the expression but with the arities of operators given to make the representation unambiguous.
For example, the expression $x(y, z(y))$ would be represented as:

=GFT ProofPower-HOL Example
[(2, x); (0, y); (1, z); (0, y)]
=TEX
Note that not every list corresponds to a tree; e.g. the empty list does not.
Given a list, $[l_1; \ldots; l_m]$ of lists representing trees, $t_1, \ldots, t_m$, and an element $x: 'a$, the representation of $x(t_1, \ldots, t_m)$ will  be the list $Cons\,(m, x)\,(Flat [l_1; \ldots; l_m])$.
We can formally define the set of those lists which do represent trees as the smallest set of lists which is closed under this construction of new representatives from old:

ⓈHOLCONST
│	Tree : (ℕ × 'a) LIST ℙ
├──────────────
│	Tree =
│	⋂{	A
│	|	∀lab : 'a; trees : (ℕ × 'a) LIST LIST⦁
│			Elems trees ⊆ A ⇒
│			Cons (Length trees, lab) (Flat trees) ∈ A}
■

=TEX
The following unparsing function is need to show that the representation
of the constructor of the type of trees is one-one.
The idea is that if $l$ is a list of number-$'a$ pairs which has a leading sub-list which is the concatenation of $i$ tree representatives, then  $Unparse\,l\,i$ will return the list comprising these $i$ tree representatives.

ⓈHOLCONST
│	Unparse : (ℕ × 'a) LIST → ℕ → (ℕ × 'a) LIST
├──────────────
│∀i nv more⦁
│	Unparse [] i = []
│∧	Unparse (Cons nv more) i =
│	if	i = 0
│	then	[]
│	else	Cons nv (Unparse more ((Fst nv + i) - 1))
■
=TEX
The following theorem shows that there are some trees (as required if we are to make a new type whose representation is the set of all trees).
=SML
set_goal([], ⌜∀x⦁[(0, x)] ∈ Tree⌝);
a(rewrite_tac[get_spec⌜Tree⌝] THEN REPEAT strip_tac);
a(POP_ASM_T (ante_tac o list_∀_elim[⌜x⌝, ⌜[]: (ℕ × 'a) LIST LIST⌝]));
a(PC_T1 "sets_ext" rewrite_tac(map get_spec [⌜Elems⌝, ⌜Flat⌝, ⌜Length⌝]));
val ⦏leaf_is_a_tree_thm⦎ = save_pop_thm"leaf_is_a_tree_thm";
=TEX
Now we can introduce the new type.
=SML
val ⦏tree_def⦎ = new_type_defn(["TREE", "tree_def"], "TREE", ["'a"],
	tac_proof( ([], ⌜∃tr⦁ (λt⦁ t ∈ Tree) tr⌝), 
		asm_tac leaf_is_a_tree_thm THEN asm_prove_tac[]));
=TEX
We now want to introduce the constructor function ($k$) as required to apply the theory developed above.
The weight function ($w$) we will use is not particularly useful and so the definition of the constructor function just asserts that a weight function exists.
The content function ($c$) will be $Elems\,o\,Snd$ and the mapping functional will be $\lambda f\bullet Map\,f\,o\,Snd$ (and so we do not need to introduce constants for them).

ⓈHOLCONST
│	MkTree : ('a × ('a TREE LIST)) → 'a TREE
├──────────────────
│	OneOne MkTree ∧
│	(∃w: 'a TREE → ℕ⦁
│		∀t⦁ ∃x⦁ (∀z⦁ z ∈ Elems(Snd x) ⇒ w z < w t) ∧ t = MkTree x)
■

%%%%
%%%%
%%%%
%%%%
\appendix
{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
{\makeatletter
\def\UP@char#1{{{}\sp{#1}}}
\makeatother
\include{wrk078.th}}
}  %\let

\twocolumn[\section*{INDEX}\label{index}]
\addcontentsline{toc}{section}{INDEX}
{\small\printindex}

\end{document}

{\HOLindexOff
%%%%
%%%%
%%%%
%%%%
\onecolumn
\section{THEOREMS}\label{THEOREMS}
=TEX
\newpage
\section{Lemmas About Lists}
=TEX
We will need a number of simple facts about lists.
These lemmas are collected together in this section.
=SML
set_goal([], ⌜∀l1 l2⦁ l1 @ l2 = [] ⇔ l1 = [] ∧ l2 = []⌝);
a(∀_tac);
a(list_induction_tac⌜l1⌝ THEN rewrite_tac[append_def]);
val ⦏append_eq_empty_thm⦎ = save_pop_thm"append_eq_empty_thm";

=TEX
=SML
set_goal([], ⌜∀ls⦁ Flat ls = [] ⇔ Elems ls ⊆ {[]}⌝);
a(∀_tac);
a(list_induction_tac⌜ls⌝ THEN
	asm_rewrite_tac(append_eq_empty_thm :: map get_spec[⌜Elems⌝, ⌜Flat⌝]));
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
val ⦏flat_empty_thm⦎ = save_pop_thm"flat_empty_thm";

=TEX
=SML
set_goal([], ⌜∀l1 l2 l3: 'a LIST⦁ (l1 @ l2) @ l3 = l1 @ l2 @ l3⌝);
a(∀_tac);
a(list_induction_tac⌜l1⌝ THEN asm_rewrite_tac(map get_spec[⌜Append⌝]));
val ⦏append_assoc_thm⦎ = save_pop_thm"append_assoc_thm";

=TEX
=SML
set_goal([], ⌜∀ls1 ls2⦁ Flat (ls1 @ ls2)  = Flat ls1 @ Flat ls2⌝);
a(∀_tac);
a(list_induction_tac⌜ls1⌝ THEN
	asm_rewrite_tac(append_assoc_thm :: map get_spec[⌜Flat⌝, ⌜Append⌝]));
val ⦏flat_append_thm⦎ = save_pop_thm"flat_append_thm";

=TEX
=SML
set_goal([], ⌜∀ls1 ls2⦁ Length (ls1 @ ls2)  = Length ls1 + Length ls2⌝);
a(∀_tac);
a(list_induction_tac⌜ls1⌝ THEN
	asm_rewrite_tac(plus_assoc_thm :: map get_spec[⌜Length⌝, ⌜Append⌝]));
val ⦏length_append_thm⦎ = save_pop_thm"length_append_thm";

=TEX
=SML
set_goal([], ⌜∀l1 l2⦁ Elems (l1 @ l2)  = Elems l1 ∪ Elems l2⌝);
a(∀_tac);
a(list_induction_tac⌜l1⌝ THEN
	asm_rewrite_tac(map get_spec[⌜Flat⌝, ⌜Elems⌝, ⌜Append⌝]));
a(PC_T1 "sets_ext" prove_tac[]);
val ⦏elems_append_thm⦎ = save_pop_thm"elems_append_thm";

=TEX
=SML
set_goal([], ⌜∀l⦁ l @ []  = l⌝);
a(∀_tac);
a(list_induction_tac⌜l⌝ THEN
	asm_rewrite_tac(map get_spec[⌜Append⌝]));
val ⦏append_empty_thm⦎ = save_pop_thm"append_empty_thm";

=TEX
=SML
set_goal([], ⌜∀l1 l2 l3 : 'a LIST⦁ l1 @ l2  = l1 @ l3 ⇔ l2 = l3⌝);
a(∀_tac);
a(list_induction_tac⌜l1⌝ THEN
	asm_rewrite_tac(map get_spec[⌜Append⌝]));
val ⦏append_cancel_thm⦎ = save_pop_thm"append_cancel_thm";
set_goal([], ⌜∀f g l⦁(∀x⦁x ∈ Elems l ⇒ f(g x) = x) ⇒ Map f(Map g l) = l⌝);
a(REPEAT ∀_tac);
a(list_induction_tac⌜l⌝ THEN PC_T1 "sets_ext1" asm_rewrite_tac(map get_spec
	[⌜Elems⌝, ⌜Map⌝]));
(* *** Goal "1" *** *)
a(contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜x⌝ THEN asm_rewrite_tac[]);
val ⦏map_map_id_thm⦎ = save_pop_thm"map_map_id_thm";

=TEX
=SML

val ⦏length_map_thm⦎ = save_thm("length_map_thm", (
set_goal([], ⌜∀f list⦁
	Length(Map f list) = Length list
⌝);
a(REPEAT strip_tac);
a(list_induction_tac⌜list⌝ THEN asm_rewrite_tac[length_def, map_def]);
pop_thm()
));

=TEX
=SML
set_goal([], ⌜∀ll l⦁ l ∈ Elems ll ⇒ Length l ≤ Length (Flat ll)⌝);
a(∀_tac);
a(list_induction_tac⌜ll⌝ THEN
	rewrite_tac(length_append_thm :: map get_spec[⌜Elems⌝, ⌜Flat⌝, ⌜Length⌝])
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏length_length_flat_thm⦎ = save_pop_thm"length_length_flat_thm";

=TEX
=SML
set_goal([], ⌜∀f l⦁Elems (Map f l) = {y | ∃x⦁ x ∈ Elems l ∧ f x = y}⌝);
a(REPEAT strip_tac);
a(list_induction_tac⌜l⌝ THEN PC_T1 "sets_ext1" asm_rewrite_tac(map get_spec
	[⌜Elems⌝, ⌜Map⌝]) THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN all_var_elim_asm_tac1 THEN asm_prove_tac[]);
val ⦏elems_map_thm⦎ = save_pop_thm"elems_map_thm";

=TEX
=SML
set_goal([], ⌜∀l⦁ Length l = 0 ⇔ l = []⌝);
a(∀_tac);
a(list_induction_tac⌜l⌝ THEN asm_rewrite_tac(map get_spec[⌜Length⌝]));
val ⦏length_0_thm⦎ = save_pop_thm"length_0_thm";

=TEX
\newpage
\subsection{Lemmas About Functions}
=TEX
We need a few lemmas about 1-1 and onto functions.
=SML
set_goal([], ⌜∀f⦁ OneOne f ⇒ ∃g⦁ ∀x⦁ g(f x) = x⌝);
a(rewrite_tac(map get_spec[⌜OneOne⌝]) THEN REPEAT strip_tac);
a(∃_tac⌜λy⦁ε x⦁ f x = y⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(ε_tac⌜ε x'⦁ f x' = f x⌝);
(* *** Goal "1" *** *)
a(prove_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[]);
val ⦏one_one_left_inv_thm⦎ = save_pop_thm"one_one_left_inv_thm";

=TEX
=SML
set_goal([], ⌜∀f⦁ Onto f ⇒ ∃g⦁ ∀y⦁ f(g y) = y⌝);
a(rewrite_tac(map get_spec[⌜Onto⌝]) THEN REPEAT strip_tac);
a(∃_tac⌜λx⦁ε y⦁ x = f y⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(ε_tac⌜ε y'⦁ y = f y'⌝);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
val ⦏onto_right_inv_thm⦎ = save_pop_thm"onto_right_inv_thm";

=TEX
=SML
set_goal([], ⌜∀f⦁ OneOne f ∧ Onto f ⇒
	∃g⦁ (∀x⦁ g(f x) = x) ∧ (∀y⦁ f(g y) = y)⌝);
a(rewrite_tac(map get_spec[⌜Onto⌝]) THEN REPEAT strip_tac);
a(all_fc_tac[one_one_left_inv_thm]);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac⌜∃z⦁ y = f z⌝ THEN asm_rewrite_tac[]);
val ⦏one_one_onto_inv_thm⦎ = save_pop_thm"one_one_onto_inv_thm";

=TEX
%%%%
%%%%


%%%%
%%%%
\subsection{Recursive Types}

=SML
set_goal([], ⌜∀k c w M⦁ (k, c, w, M) ∈ FinitaryRecType ⇒
	∀X: 'T SET⦁
		(∀x: 'D⦁ c(x) ⊆ X ⇒ k(x) ∈ X)
	⇒	∀t : 'T⦁ t ∈ X
⌝);
a(rewrite_tac[get_spec⌜FinitaryRecType⌝] THEN REPEAT strip_tac);
a(lemma_tac⌜∃i⦁ w(t) = i⌝ THEN1 prove_∃_tac);
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜t⌝, ⌜t⌝) THEN cov_induction_tac⌜i⌝);
a(REPEAT strip_tac);
a(spec_nth_asm_tac 5 ⌜t⌝ THEN all_var_elim_asm_tac1);
a(lemma_tac⌜c x ⊆ X⌝);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
a(spec_nth_asm_tac 4 ⌜w x'⌝);
a(spec_nth_asm_tac 1 ⌜x'⌝);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[]);
val ⦏fin_rec_type_induction_thm⦎ = save_pop_thm"fin_rec_type_induction_thm";

=TEX
For use with the HOL induction tactics we need the above formulated for properties rather than sets:
=SML
set_goal([], ⌜∀k c w M⦁ (k, c, w, M) ∈ FinitaryRecType ⇒
	∀P: 'T → BOOL⦁
		(∀x: 'D⦁ (∀t⦁ t ∈ c(x) ⇒ P t) ⇒ P(k(x)))
	⇒	∀t : 'T⦁ P(t)
⌝);
a(REPEAT strip_tac);
a(fc_tac[fin_rec_type_induction_thm]);
a(SPEC_NTH_ASM_T 1 ⌜{t | P t}⌝ ante_tac);
a(PC_T1 "sets_ext1" rewrite_tac[]);
a(REPEAT strip_tac);
a(ALL_ASM_FC_T rewrite_tac[]);
val ⦏fin_rec_type_induction_thm1⦎ = save_pop_thm"fin_rec_type_induction_thm1";

=TEX
Somewhat analogously to the proof of the induction principle, we can use the principle of definition by primitive recursion for the natural numbers to derive a definitional principle for the recursive type.
Let us assume that an arbitrary function $d$  from $'D × 'Y$ to $'y$ is given.
$d$ the data for a primitive recursive definition.
The claim is that for any such function there is a function $h$ from $'T$ to $'y$ satisfying the recursion equation:
=GFT
	∀x⦁ h(k(x)) = d(x, M h x)
■
We construct $h$ as follows.
First of all we observe that the constructor function, $k$, is both one-to-one and onto (by the second clause in the definition of $FinitaryRecType$).
Therefore $k$ has a two-sided inverse, $δ$ say.
That is to say we can assume the existence of a function
=INLINEFT
δ: 'T → 'D
=TEX
\ satisfying:
=GFT
	δ (k x) = x
	k (δ y) = y
■
for any $x$ and $y$.
Now we can use the principle of definition by primitive recursion for the natural numbers to construct a function
=INLINEFT
H: ℕ → 'T → 'y
=TEX
\ satisfying the equations:
=GFT
	H 0 y		= d(δ(y), M Arbitrary (δ y)))
	H(i + 1) y	= if w(y) ≤ i then H(i)(y) else d(δ(y), M (H i) (δ y))
■
The idea here is that, for each $i$, $H(i)$ is an approximation to the desired function $h$, and, in fact, agrees with $h$ for all elements of weight no greater than $i$.
We can prove (by induction on $j$) that $H$ enjoys the following monotonicity property.
=GFT
	H (w y + j) y = H (w y) y
■
We then define $h$ by
=GFT
	h y = H (w y) y
■
\ and check, using the monotonicity properties of $H$ and $M$ that $h$ has the required property.

To formalise the above, we first prove the lemma that there exists $δ$ and $H$ satisfying the salient conditions.

=SML
set_goal([], ⌜∀k c w⦁ (k, c, w, M) ∈ FinitaryRecType ⇒
	∃δ⦁
	(∀ x⦁ δ (k x) = x)
∧	(∀ y⦁ k (δ y) = y)
∧	∀d: 'D  ×'Y → 'y⦁
	∃ H : ℕ → 'T → 'y ⦁
	(∀y⦁	H 0 y = d(δ(y), M Arbitrary (δ y)))
∧	(∀i y⦁	H(i + 1) y = if w(y) ≤ i then H(i)(y) else d(δ(y), M (H i) (δ y)))
∧	(∀j⦁ ∀ y⦁ H (w y + j) y = H (w y) y)⌝);
a(rewrite_tac[get_spec⌜FinitaryRecType⌝] THEN REPEAT strip_tac);
a(lemma_tac⌜Onto k⌝ THEN1 (rewrite_tac[get_spec⌜Onto⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a(spec_nth_asm_tac 2 ⌜y⌝);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(all_fc_tac[one_one_onto_inv_thm]);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
a(lemma_tac⌜∃H⦁∀y⦁
	H 0 y = d(g(y), M Arbitrary (g y)) ∧
∀i⦁	H(i + 1) y = if w(y) ≤ i then H(i)(y) else d(g(y), M (H i) (g y))⌝
	THEN1 prove_∃_tac);
a(∃_tac⌜H⌝ THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a(induction_tac ⌜j⌝);
(* *** Goal "2.1" *** *)
a(PC_T1 "hol2" rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(asm_rewrite_tac[plus_assoc_thm1]);
val ⦏fin_rec_type_prim_rec_lemma1⦎ = save_pop_thm"fin_rec_type_prim_rec_lemma1";

=TEX
Using this lemma we can prove the existence part of the principle of definition by primitive recursion.
Note that goals 1 and 2 here come from a case split, not a proof by induction: induction would actually be harmful here because it would introduce an irrelevant equation into the assumptions.
=SML
set_goal([], ⌜∀k c w M⦁ (k, c, w, M) ∈ FinitaryRecType ⇒
	∀d: 'D  ×'Y → 'y⦁
	∃ h : 'T → 'y ⦁ ∀x:'D⦁ h(k(x)) = d(x, M h x)
⌝);
a(REPEAT strip_tac THEN all_fc_tac[fin_rec_type_prim_rec_lemma1]);
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜d⌝));
a(DROP_ASM_T ⌜(k, c, w, M) ∈ FinitaryRecType⌝
	(strip_asm_tac o rewrite_rule[get_spec⌜FinitaryRecType⌝]));
a(∃_tac⌜λy⦁H (w(y)) y⌝ THEN rewrite_tac[] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜k x⌝);
a(POP_ASM_T (strip_asm_tac o eq_sym_rule));
a(lemma_tac⌜OneOne k ⇒ k x' = k x ⇒ x' = x⌝ THEN1 prove_tac[get_spec⌜OneOne⌝]);
a(var_elim_nth_asm_tac 1);
a(strip_asm_tac(∀_elim⌜w (k x)⌝ ℕ_cases_thm));
(* *** Goal "1" *** *)
a(asm_rewrite_tac[]);
a(SPEC_NTH_ASM_T 3 ⌜0⌝ ante_tac);
a(PC_T1 "hol2" rewrite_tac[]);
a(lemma_tac⌜c x ⊆ {z|w z < w (k x)} ⇒ c x = {}⌝
	THEN1 (LIST_GET_NTH_ASM_T [1] (PC_T1 "hol2" prove_tac)));
a strip_tac;
a(LIST_SPEC_NTH_ASM_T 1 [⌜Arbitrary: 'T → 'y⌝, ⌜λ y⦁ H (w y) y⌝, ⌜x⌝] ante_tac);
a(GET_NTH_ASM_T 2 rewrite_thm_tac THEN STRIP_T rewrite_thm_tac);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
a(LEMMA_T ⌜M (H i) x = M (λ y⦁ H (w y) y) x⌝ rewrite_thm_tac);
a(LIST_SPEC_NTH_ASM_T 3 [⌜w(k x)⌝, ⌜H i⌝, ⌜λ y⦁ H (w y) y⌝] ante_tac);
a(LEMMA_T⌜∀ y⦁ w y < w (k x) ⇒ H i y = (λ y⦁ H (w y) y) y⌝ rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(TOP_ASM_T rewrite_thm_tac THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule(map get_spec[⌜$<⌝, ⌜$≤⌝])));
a(POP_ASM_T (asm_rewrite_thm_tac o eq_sym_rule));
(* *** Goal "2.2" *** *)
a strip_tac;
a(spec_nth_asm_tac 1 ⌜x⌝);
val ⦏fin_rec_type_prim_rec_exists_thm⦎ = save_pop_thm"fin_rec_type_prim_rec_exists_thm";

=TEX
It is fairly straightforward to show that the functions $h$ whose existence is given by the principle of definition by primitive recursion are uniquely determined by their recursion equations.
Note that, perhaps a little inelegantly, it seems to be easier to prove this using course-of-values induction for the natural numbers rather than by dint of the induction principle for the recursive data type.
=SML
set_goal([], ⌜∀k c w M⦁ (k, c, w, M) ∈ FinitaryRecType ⇒
	∀d: 'D  ×'Y → 'y⦁
	∀ h⋎1 h⋎2 : 'T → 'y ⦁
		(∀x:'D⦁ h⋎1(k(x)) = d(x, M h⋎1 x)) ∧
		(∀x:'D⦁ h⋎2(k(x)) = d(x, M h⋎2 x)) ⇒
		h⋎1 = h⋎2
⌝);
a(rewrite_tac[get_spec⌜FinitaryRecType⌝] THEN REPEAT strip_tac);
a(PC_T1 "hol2" REPEAT strip_tac);
a(lemma_tac⌜Onto k⌝ THEN1 (rewrite_tac[get_spec⌜Onto⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a(spec_nth_asm_tac 4 ⌜y⌝);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(all_fc_tac[one_one_onto_inv_thm]);
a(lemma_tac⌜∃i⦁ w x = i⌝ THEN1 prove_∃_tac);
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜x⌝, ⌜x⌝) THEN cov_induction_tac⌜i⌝);
a(lemma_tac⌜∀ y⦁ w y < i ⇒ h⋎1 y = h⋎2 y⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜w y⌝ THEN spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2.2" *** *)
a(list_spec_nth_asm_tac 8 [⌜i⌝, ⌜h⋎1⌝, ⌜h⋎2⌝] THEN1 all_asm_fc_tac[]);
a(REPEAT strip_tac);
a(spec_nth_asm_tac 11 ⌜x⌝);
a(all_var_elim_asm_tac1);
a(spec_nth_asm_tac 2 ⌜x'⌝);
a(asm_rewrite_tac[]);
val ⦏fin_rec_type_prim_rec_unique_thm⦎ =
	save_pop_thm"fin_rec_type_prim_rec_unique_thm";

=TEX
The previous two theorems may now be fitted together to give the principle of definition by primitive recursion in its final form.
To interface nicely with the {\Product} interfaces for automatic consistency proofs, we state the theorem in terms of a data function with a pair of arguments rather than an argument pair.
=SML

val _ = push_pc"hol";
set_goal([], ⌜∀k c w M⦁ (k, c, w, M) ∈ FinitaryRecType ⇒
	∀d: 'D  → 'Y → 'y⦁
	∃⋎1 h : 'T → 'y ⦁ ∀x:'D⦁ h(k(x)) = d x (M h x)
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[fin_rec_type_prim_rec_exists_thm]);
a(spec_nth_asm_tac 1 ⌜λ(x, y)⦁ d x y⌝);
a(∃⋎1_tac⌜h⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o once_rewrite_rule[
	prove_rule[] ⌜∀u v⦁d u v = (λ (x, y)⦁ d x y) (u, v)⌝]));
a(all_fc_tac[fin_rec_type_prim_rec_unique_thm]);
val ⦏fin_rec_type_prim_rec_thm⦎ =
	save_pop_thm"fin_rec_type_prim_rec_thm";

=TEX
=SML
set_goal([], ⌜∀c w M⦁
	(M, c) ∈ LocalFunctional ⇒
	∀i g⋎1 g⋎2⦁ (∀y⦁ w(y) < i ⇒ g⋎1(y) = g⋎2(y))
		⇒ ∀x⦁ c(x) ⊆ {y | w(y) < i} ⇒ M(g⋎1)(x) = M(g⋎2)(x)
⌝);
a(rewrite_tac [get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜{y | w y < i}⌝);
a(list_spec_nth_asm_tac 1 [⌜g⋎1⌝, ⌜g⋎2⌝] THEN1 all_asm_fc_tac[]);
a(spec_nth_asm_tac 1 ⌜x⌝);
val ⦏local_functional_thm⦎ = save_pop_thm "local_functional_thm";

=TEX
We can now show that for various useful values of $c$ and $M$, $M$ is local with respect to $c$.
=SML
set_goal([], ⌜((λf⦁ f), (λx⦁{x})) ∈ LocalFunctional⌝);
a(rewrite_tac[get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
a(lemma_tac⌜{x} ⊆ I ⇒ x ∈ I⌝ THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(all_asm_fc_tac[]);
val ⦏i_local_thm⦎ = save_pop_thm "i_local_thm";

=TEX
=SML
set_goal([], ⌜((λf⦁ (λx⦁ {})), (λx⦁{x})) ∈ LocalFunctional⌝);
a(rewrite_tac[get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
val ⦏k_local_thm⦎ = save_pop_thm "k_local_thm";

=TEX
=SML
set_goal([], ⌜ ∀ M⋎1 c⋎1 M⋎2 c⋎2⦁
	(M⋎1, c⋎1) ∈ LocalFunctional ∧ 
	(M⋎2, c⋎2) ∈ LocalFunctional ⇒
	((λf⦁λ(x, y)⦁ (M⋎1 f x, M⋎2 f y)), (λ(x, y)⦁ c⋎1 x ∪ c⋎2 y)) ∈ LocalFunctional
⌝);
a(rewrite_tac[get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜c⋎1 (Fst x) ∪ c⋎2 (Snd x) ⊆ I ⇒ c⋎1 (Fst x) ⊆ I⌝ THEN1
	PC_T1 "sets_ext" prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜c⋎1 (Fst x) ∪ c⋎2 (Snd x) ⊆ I ⇒ c⋎2 (Snd x) ⊆ I⌝ THEN1
	PC_T1 "sets_ext" prove_tac[]);
a(all_asm_fc_tac[]);
val ⦏×_local_thm⦎ = save_pop_thm "×_local_thm";

=TEX
=SML
set_goal([], ⌜ ∀ M⋎1 c⋎1 M⋎2 c⋎2⦁
	(M⋎1, c⋎1) ∈ LocalFunctional ∧ 
	(M⋎2, c⋎2) ∈ LocalFunctional ⇒
	((λf⦁λx⦁ if IsL x then M⋎1 f (OutL x) else M⋎2 f (OutR x)),
	(λx⦁ if IsL x then c⋎1 (OutL x) else c⋎2 (OutR x))) ∈ LocalFunctional
⌝);
a(rewrite_tac[get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN strip_asm_tac(∀_elim⌜x⌝ sum_cases_thm)
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
val ⦏sum_local_thm⦎ = save_pop_thm "sum_local_thm";

=TEX
=SML
set_goal([], ⌜ ∀ M c⦁
	(M, c) ∈ LocalFunctional  ⇒
	((λf⦁ Map (M f)),(λx⦁ ⋃(Elems (Map c x)))) ∈ LocalFunctional
⌝);
a(rewrite_tac[get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN list_induction_tac⌜x⌝ THEN
	rewrite_tac(map get_spec[⌜Map⌝, ⌜Elems⌝]));
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b c⦁ ¬⋃ a ⊆ b ⇒ ¬⋃(c ∪ a) ⊆ b⌝]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜c x' ⊆ ⋃ ({c x'} ∪ Elems (Map c x))⌝ THEN
	PC_T1 "sets_ext" REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(∃_tac⌜c x'⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b c⦁ a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]);
a(all_asm_fc_tac[]);
val ⦏list_local_thm⦎ = save_pop_thm "list_local_thm";

=TEX
=SML
set_goal([], ⌜ (Map, Elems) ∈ LocalFunctional ⌝);
a(rewrite_tac[get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN list_induction_tac⌜x⌝ THEN
	rewrite_tac(map get_spec[⌜Map⌝, ⌜Elems⌝]));
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b c⦁ ¬ a ⊆ b ⇒ ¬(c ∪ a) ⊆ b⌝]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜{x'} ∪ Elems x ⊆ I ⇒ x' ∈ I⌝ THEN1 PC_T1 "sets_ext" prove_tac[]);
a(all_asm_fc_tac[]);
val ⦏list_local_thm1⦎ = save_pop_thm "list_local_thm1";

=TEX
=SML
set_goal([], ⌜ ∀ M c⦁
	(M, c) ∈ LocalFunctional  ⇒
	((λf⦁ M f o Snd),(c o Snd)) ∈ LocalFunctional
⌝);
a(rewrite_tac[get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
val ⦏o_snd_local_thm⦎ = save_pop_thm "o_snd_local_thm";

=TEX
=SML
set_goal([], ⌜ ∀ M c⦁
	(M, c) ∈ LocalFunctional  ⇒
	((λf⦁ M f o Fst),(c o Fst)) ∈ LocalFunctional
⌝);
a(rewrite_tac[get_spec⌜LocalFunctional⌝] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
val ⦏o_fst_local_thm⦎ = save_pop_thm "o_fst_local_thm";
val _ = pop_pc();

=TEX

\subsection{Theorems on Trees}
%%%%
%%%%
=TEX
To develop a recursive type represented by the above set of trees, we first derive an induction principle.
We do this in three steps.
=SML

val _ = push_pc "hol";
set_goal([], ⌜∀X⦁
	(∀x ts⦁ (Elems ts ⊆ X)
			⇒ (Cons (Length ts, x) (Flat ts)) ∈ X)
	⇒	Tree ⊆ X
⌝);
a(PC_T1 "sets_ext" rewrite_tac[get_spec⌜Tree⌝] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜X⌝);
a(list_spec_nth_asm_tac 4 [⌜lab⌝, ⌜trees⌝]);
a(all_asm_fc_tac[]);
val ⦏tree_induction_lemma1⦎ = save_pop_thm"tree_induction_lemma1";

=TEX
=SML
set_goal([], ⌜
	∀x ts⦁ Elems ts ⊆ Tree ⇒ Cons (Length ts, x) (Flat ts) ∈ Tree
⌝);
a(PC_T1 "sets_ext" rewrite_tac[get_spec⌜Tree⌝] THEN REPEAT strip_tac);
a(list_spec_nth_asm_tac 1 [⌜x⌝, ⌜ts⌝]);
a(all_asm_fc_tac[]);
val ⦏tree_induction_lemma2⦎ = save_pop_thm"tree_induction_lemma2";

=TEX
=SML
set_goal([], ⌜∀X⦁
	(∀x ts⦁ Elems ts ⊆ Tree ∩ X ⇒ (Cons(Length ts, x) (Flat ts)) ∈ X)
	⇒	Tree ⊆ X
⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜Tree ∩ X⌝ tree_induction_lemma1));
(* *** Goal "1" *** *)
a(lemma_tac⌜Elems ts ⊆ Tree ∩ X ⇒ Elems ts ⊆ Tree⌝ THEN1 
	PC_T1 "sets_ext" prove_tac[]);
a(all_fc_tac[tree_induction_lemma2] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext" prove_tac[]);
val ⦏tree_induction_lemma⦎ = save_pop_thm"tree_induction_lemma";

=TEX
It is convenient to recast the above in terms of properties for use with the induction tactic generating function.
=SML
set_goal([], ⌜∀P⦁
	(∀x ts⦁ (∀t⦁ t ∈ Elems ts ⇒ t ∈ Tree ∧ P t)
		⇒ P (Cons(Length ts, x) (Flat ts)))
	⇒	∀t⦁t ∈ Tree ⇒ P t
⌝);
a(strip_tac);
a(ante_tac(∀_elim⌜{t | P t}⌝ tree_induction_lemma));
a(PC_T1 "sets_ext" rewrite_tac[]);
val ⦏tree_induction_tac_lemma⦎ = save_pop_thm"tree_induction_tac_lemma";

=TEX
We now use the induction principle to give the analogue of $ℕ\_cases\_thm$ for trees for trees and to show that the empty list is not a tree.
=SML
set_goal([], ⌜∀t⦁ t ∈ Tree ⇒
	∃x; ts⦁ Elems ts ⊆ Tree ∧ t = Cons (Length ts, x) (Flat ts)⌝);
a(∀_tac THEN gen_induction_tac1 tree_induction_tac_lemma);
a(∃_tac⌜x⌝ THEN ∃_tac⌜ts⌝ THEN PC_T "sets_ext" contr_tac THEN all_asm_fc_tac[]);
val ⦏tree_cases_lemma⦎ = save_pop_thm"tree_cases_lemma";

=TEX
=SML
set_goal([], ⌜¬ [] ∈ Tree⌝);
a(lemma_tac⌜∀t⦁t ∈ Tree ⇒ ¬t = []⌝ THEN_LIST[id_tac, asm_prove_tac[]]);
a(∀_tac THEN gen_induction_tac1 tree_induction_tac_lemma);
a(rewrite_tac[]);
val ⦏¬_empty_list_tree_lemma⦎ = save_pop_thm"¬_empty_list_tree_lemma";


=TEX

The key result about $Unparse$ is the following formal statement of our informal description of its purpose.
The proof is by list induction on the first operand to $Unparse$.

=SML
set_goal([], ⌜∀ts more⦁
	Elems ts ⊆ Tree ⇒
	Unparse (Flat ts ⁀ more) (Length ts) = Flat ts
⌝);
a(REPEAT ∀_tac);
a(lemma_tac⌜∃tm⦁ Flat ts ⁀ more = tm⌝ THEN_LIST [prove_∃_tac, all_asm_ante_tac]);
a(intro_∀_tac(⌜ts⌝, ⌜ts⌝) THEN list_induction_tac⌜tm⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[append_eq_empty_thm, flat_empty_thm] THEN REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜ts⌝ list_cases_thm) THEN all_var_elim_asm_tac1
	THEN rewrite_tac(map get_spec[⌜Unparse⌝, ⌜Length⌝, ⌜$Append⌝, ⌜Flat⌝]));
a(i_contr_tac THEN all_asm_ante_tac);
a(PC_T1 "sets_ext1" rewrite_tac(map get_spec[⌜Elems⌝]) THEN REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜x⌝);
a(∃_tac ⌜x⌝ THEN asm_rewrite_tac[¬_empty_list_tree_lemma]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜ts⌝ list_cases_thm) THEN all_var_elim_asm_tac1
	THEN rewrite_tac(map get_spec[⌜Unparse⌝, ⌜Length⌝, ⌜$Append⌝, ⌜Flat⌝]));
(* *** Goal "2.1" *** *)
a(strip_asm_tac(∀_elim⌜more⌝ list_cases_thm) THEN all_var_elim_asm_tac1
	THEN rewrite_tac(map get_spec[⌜Unparse⌝]));
(* *** Goal "2.2" *** *)
a(lemma_tac⌜Elems (Cons x' list2) ⊆ Tree ⇒ x' ∈ Tree⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[get_spec⌜Elems⌝]);
a(all_fc_tac[tree_cases_lemma]);
a(var_elim_nth_asm_tac 1);
a(all_asm_ante_tac THEN
	rewrite_tac(map get_spec[⌜$Append⌝, ⌜Flat⌝, ⌜Elems⌝, ⌜Unparse⌝]));
a(rewrite_tac[prove_rule[flat_append_thm]
	⌜Flat ts ⁀ Flat list2 = Flat(ts ⁀ list2)⌝]);
a(REPEAT strip_tac);
a(lemma_tac⌜Elems(ts ⁀ list2) ⊆ Tree⌝
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[elems_append_thm]);
a(all_asm_fc_tac[]);
a(POP_ASM_T ante_tac THEN rewrite_tac[plus_assoc_thm1, length_append_thm]);
val ⦏unparse_thm⦎ = save_pop_thm"unparse_thm";

=TEX
In what follows we only use the special case of the above for which the second argument of $Unparse$ is $1$.
This case has the following consequence.
=SML
set_goal([], ⌜∀t more⦁ t ∈ Tree ⇒ Unparse (t ⁀ more) 1 = t⌝);
a(REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜[t]⌝, ⌜more⌝] unparse_thm));
a(rewrite_tac(append_empty_thm :: map get_spec[⌜Elems⌝, ⌜Length⌝, ⌜Flat⌝]));
a(PC_T1 "sets_ext1" asm_prove_tac[]);
val ⦏unparse_thm1⦎ = save_pop_thm"unparse_thm1";

=TEX
Now we can prove the uniqueness of the decomposition of a tree given to us by $tree\_cases\_lemma$.
=SML
set_goal([], ⌜∀t⦁ t ∈ Tree ⇒
	∃⋎1(x, ts)⦁ Elems ts ⊆ Tree ∧ t = Cons (Length ts, x) (Flat ts)⌝);
a(REPEAT strip_tac THEN all_fc_tac[tree_cases_lemma]);
a(∃⋎1_tac⌜(x, ts)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(REPEAT all_var_elim_asm_tac1);
a(REPEAT strip_tac);
(* *** Goal "2" *** *)
a(REPEAT all_var_elim_asm_tac1);
a(REPEAT_N 4 (POP_ASM_T ante_tac) THEN POP_ASM_T discard_tac);
a(intro_∀_tac(⌜ts⌝, ⌜ts⌝) THEN list_induction_tac⌜ts'⌝);
(* *** Goal "2.1" *** *)
a(rewrite_tac[get_spec⌜Length⌝, length_0_thm]);
a(prove_tac[]);
(* *** Goal "2.2" *** *)
a(REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜ts⌝ list_cases_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "2.2.1" *** *)
a(GET_NTH_ASM_T 2 ante_tac THEN rewrite_tac[get_spec⌜Length⌝, length_0_thm]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜x = x'⌝ THEN all_asm_ante_tac
	THEN rewrite_tac(
		pc_rule1"sets_ext1" prove_rule[]
			⌜∀z a b⦁ {z} ∪ a ⊆ b ⇔ z ∈ b ∧ a ⊆ b⌝ ::
		map get_spec[⌜Flat⌝, ⌜Elems⌝, ⌜Length⌝])
	THEN REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a(LEMMA_T ⌜Unparse(x ⁀ Flat ts') 1 = Unparse(x' ⁀ Flat list2) 1⌝ ante_tac THEN1
		asm_rewrite_tac[]);
a(ALL_FC_T rewrite_tac[unparse_thm1]);
(* *** Goal "2.2.2.2" *** *)
a(var_elim_nth_asm_tac 1);
a(POP_ASM_T ante_tac THEN rewrite_tac[append_cancel_thm] THEN strip_tac);
a(all_asm_fc_tac[]);
val ⦏tree_cases_lemma1⦎ = save_pop_thm"tree_cases_lemma1";

=TEX
Now we prove the consistency of the above on the basis of the natural witness for the constructor function (which takes the representatives of its operand, performs the construction in the representation type and then abstracts the result).
=SML
push_consistency_goal⌜MkTree⌝;
a((strip_asm_tac o rewrite_rule[]) (⇒_match_mp_rule type_lemmas_thm tree_def));
a(∃_tac⌜λ(x, ts)⦁ abs(Cons (Length ts, x) (Flat (Map rep ts)))⌝
	THEN rewrite_tac[get_spec⌜OneOne⌝] THEN REPEAT strip_tac);

=TEX
The proof that the constructor function is one-to-one is a fairly mechanical use of the equations provided by the theorem $type\_lemmas\_thm$ which we used to introduce the abstraction and representation functions.
=SML
(* *** Goal "1" *** *)
a(lemma_tac⌜∀l⦁ Elems (Map rep l) ⊆ Tree⌝ THEN1 strip_tac);
(* *** Goal "1.1" *** *)
a(list_induction_tac ⌜l⌝ THEN
	rewrite_tac(map get_spec[⌜Elems⌝, ⌜Map⌝]));
a(strip_tac THEN asm_rewrite_tac[
	pc_rule1"sets_ext" prove_rule[]⌜∀a b c⦁a ∪ b ⊆ c ⇔ a ⊆ c ∧ b ⊆ c⌝]);
a(PC_T1 "sets_ext" REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(spec_nth_asm_tac 1 ⌜Snd x2⌝);
a(spec_nth_asm_tac 2 ⌜Snd x1⌝);
a(all_fc_tac[tree_induction_lemma2]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[length_map_thm] o ∀_elim⌜Fst x2⌝));
a(all_fc_tac[tree_cases_lemma1]);
a(DROP_NTH_ASM_T 7
	(strip_asm_tac o rewrite_rule[length_map_thm] o ∀_elim⌜Fst x1⌝));
a(LIST_GET_NTH_ASM_T [12] all_fc_tac);
a(LEMMA_T⌜rep(abs (Cons (# (Snd x1), Fst x1) (Flat (Map rep (Snd x1)))))
             = rep(abs (Cons (# (Snd x2), Fst x2) (Flat (Map rep (Snd x2)))))⌝
	ante_tac THEN1 LIST_GET_NTH_ASM_T [13] rewrite_tac);
a(LIST_GET_NTH_ASM_T [1,2] rewrite_tac THEN strip_tac);
a(GET_NTH_ASM_T 7 (ante_tac o list_∀_elim[⌜Fst x2⌝, ⌜Map rep (Snd x2)⌝]));
a(DROP_NTH_ASM_T 7 (ante_tac o list_∀_elim[⌜Fst x1⌝, ⌜Map rep (Snd x1)⌝]));
a(asm_rewrite_tac[length_map_thm] THEN REPEAT strip_tac);
a(LEMMA_T⌜Map abs(Map rep (Snd x1)) = Map abs(Map rep (Snd x2))⌝
	ante_tac THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜
	(∀x⦁x ∈ Elems (Snd x1) ⇒ abs(rep x) = x) ∧
	(∀x⦁x ∈ Elems (Snd x2) ⇒ abs(rep x) = x)⌝ THEN1 asm_rewrite_tac[]);
a(ALL_FC_T rewrite_tac [map_map_id_thm]);
a(asm_ante_tac⌜Fst x1 = Fst x2⌝ THEN PC_T1 "prop_eq_pair" prove_tac[]);

=TEX
The witness for the weight function is the function giving the length of a tree representative.
That this works is fairly straightforward to prove using $tree\_cases\_lemma$ and a little work with lists and arithmetic.
=SML
(* *** Goal "2" *** *)
a(∃_tac⌜λt⦁ Length(rep t)⌝ THEN rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac⌜rep t ∈ Tree⌝ THEN1 asm_rewrite_tac[]);
a(all_fc_tac[tree_cases_lemma]);
a(∃_tac⌜(x, Map abs ts)⌝ THEN rewrite_tac[length_map_thm]);
a(DROP_ASM_T ⌜Elems ts ⊆ Tree⌝ ante_tac THEN PC_T1 "sets_ext1" asm_rewrite_tac[]);
a(strip_tac THEN ALL_FC_T rewrite_tac[map_map_id_thm]);
a(GET_NTH_ASM_T 2 (rewrite_thm_tac o eq_sym_rule));
a(GET_NTH_ASM_T 5 rewrite_thm_tac);
a(rewrite_tac[elems_map_thm]);
a(REPEAT strip_tac);
a(var_elim_nth_asm_tac 1);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
a(rewrite_tac[get_spec⌜Length⌝]);
a(all_fc_tac[length_length_flat_thm]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val _ = save_consistency_thm ⌜MkTree⌝ (pop_thm());

=TEX
The above consistency result gives us that $MkTree$ satisfies its defining property.
Thus we have half of the data required by the material in section \ref{RECURSIVETYPES}.
The rest, i.e., the contents function and mapping functional, is determined fairly mechanically from the domain type of the constructor function.
=SML
set_goal([], ⌜((λf⦁ Map f o Snd), (Elems o Snd)) ∈ LocalFunctional⌝);
a(bc_tac[o_snd_local_thm]);
a(rewrite_tac[list_local_thm1]);
val ⦏tree_local_thm⦎ = save_pop_thm "tree_local_thm";

=TEX
We must now show that our choice of constructor, contents and weight functions and mapping functional satisfy the conditions of sectio \ref{RECURSIVETYPES}.
The proof is straightforward:
=SML
set_goal([], ⌜∃w⦁ (MkTree, Elems o Snd, w, (λf⦁ Map f o Snd)) ∈ FinitaryRecType⌝);
a(strip_asm_tac(get_spec⌜MkTree⌝));
a(∃_tac⌜w⌝ THEN rewrite_tac[get_spec⌜FinitaryRecType⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(spec_nth_asm_tac 1 ⌜t⌝ THEN var_elim_nth_asm_tac 1);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(strip_asm_tac (list_∀_elim[
	⌜Elems o (Snd :  'a × 'a TREE LIST → 'a TREE LIST)⌝, ⌜w⌝,
	⌜λf:'a TREE → 'b⦁ Map f o (Snd :  'a × 'a TREE LIST → 'a TREE LIST)⌝]
	local_functional_thm));
(* *** Goal "2.1" *** *)
a(all_fc_tac[tree_local_thm]);
(* *** Goal "2.2" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[]));
a(all_asm_fc_tac[]);
val ⦏tree_fin_rec_thm⦎ = save_pop_thm "tree_fin_rec_thm";

=TEX
The following inference rule allows us to discharge the antecedent of the implication in the conclusion of a theorem such as $fin\_rec\_type\_prim\_rec\_thm$ using an existentially quantified theorem such as $tree\_fin\_rec\_thm$.
The main advantage of having the rule do this is that it works out what the answer should be; whereas if one tries a backwards proof one has to figure out and write down the types of things like $Elems\,o\,Snd$.
=SML
fun  ⦏simple_∃_⇒_match_rule⦎ (thm1 : THM) (thm2 : THM) : THM = (
	let	val (v, b) = dest_∃ (concl thm2);
		val thm3 = asm_rule b;
		val thm4 = ⇒_match_mp_rule thm1 thm3;
	in	simple_∃_elim v thm2 thm4
	end
);

=TEX
=SML

val ⦏tree_induction_thm⦎ = save_thm("tree_induction_thm",
	rewrite_rule[]
	(simple_∃_⇒_match_rule fin_rec_type_induction_thm1 tree_fin_rec_thm));
val ⦏tree_prim_rec_thm⦎ = save_thm("tree_prim_rec_thm",
	rewrite_rule[]
	(simple_∃_⇒_match_rule fin_rec_type_prim_rec_thm tree_fin_rec_thm));

=TEX
=SML

val ⦏tree_induction_thm1⦎ = save_thm("tree_induction_thm1", (
set_goal([], ⌜∀ P⦁ (∀ l ts ⦁ (∀ t⦁ t ∈ Elems ts ⇒ P t) ⇒ P (MkTree (l, ts))) ⇒ (∀ t⦁ P t) ⌝);
a(REPEAT_N 2 strip_tac);
a(bc_thm_tac tree_induction_thm THEN REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule[]⌜x = (Fst x, Snd x)⌝]);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN POP_ASM_T accept_tac);
pop_thm()));

=TEX
=SML

val ⦏tree_prim_rec_thm1⦎ = save_thm("tree_prim_rec_thm1", (
set_goal([], ⌜∀ d⦁ ∃⋎1 h⦁ ∀ l  ts⦁ h (MkTree (l, ts)) = d l ts (Map h ts)⌝);
a(REPEAT strip_tac);
a(ante_tac (∀_elim⌜Uncurry d⌝ tree_prim_rec_thm));
a(rewrite_tac[uncurry_def] THEN REPEAT strip_tac);
a(∃⋎1_tac ⌜h⌝ THEN1 asm_rewrite_tac[] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
a(LEMMA_T ⌜x' = (Fst x', Snd x')⌝ pure_once_rewrite_thm_tac THEN1 rewrite_tac[]);
a(POP_ASM_T pure_rewrite_thm_tac THEN rewrite_tac[]);
pop_thm()));

=TEX
=SML

val ⦏mk_tree_def⦎ : THM = get_spec⌜MkTree⌝;

=TEX
=SML

val ⦏mk_tree_one_one_thm⦎ =save_thm("mk_tree_one_one_thm", (
set_goal([], ⌜∀x y⦁ MkTree x = MkTree y ⇔ x = y⌝);
a(REPEAT strip_tac THEN_LIST [id_tac, asm_rewrite_tac[]]);
a(all_fc_tac[rewrite_rule[one_one_def](get_spec⌜MkTree⌝)]);
pop_thm()));

=TEX
=SML
val _ = pop_pc();
=TEX
Create the promised proof context:
=SML
val _ = new_pc"'trees";
val _ = add_∃_cd_thms[tree_prim_rec_thm] "'trees";
val _ = add_∃_cd_thms[tree_prim_rec_thm1] "'trees";
val _ = set_rw_eqn_cxt (cthm_eqn_cxt initial_rw_canon mk_tree_one_one_thm) "'trees";
val _ = set_st_eqn_cxt (cthm_eqn_cxt initial_rw_canon mk_tree_one_one_thm) "'trees";
val _ = set_sc_eqn_cxt (cthm_eqn_cxt initial_rw_canon mk_tree_one_one_thm) "'trees";
val _ = set_pr_tac basic_prove_tac "'trees";
val _ = set_pr_conv basic_prove_conv "'trees";
val _ = commit_pc "'trees";
=TEX
Define the structure:
=SML
structure ⦏Trees⦎ : Trees = struct
	val tree_induction_tac : TERM -> TACTIC =
		gen_induction_tac tree_induction_thm1;
end (* of structure Trees *);
open Trees;
=TEX
\subsection{Epilogue}\label{END}
} % matches turning off of HOL index entries.
=TEX
%%%%
%%%%
=SML
open_theory"trees";
output_theory{out_file="wrk078.th.doc", theory="trees"};
=TEX
\end{document}
=SML
(*
set_merge_pcs["'tree", "hol"];
ⓈHOLCONST
│	W : 'a TREE → ℕ
├──────────────────
│	∀x⦁ W(MkTree x) = Fold ($+) (Map W (Snd x)) 0
■
=SML
*)

