=IGN
********************************************************************************
wrk073.doc: this file is supplementary material for the ProofPower system

Copyright (c) 2004 Lemma 1 Ltd.

This file is supplied under the GNU General Public Licence (GPL) version 2.

See the file LICENSE supplied with ProofPower source for the terms of the GPL
or visit the OpenSource web site at http://www.opensource.org/

Contact: Rob Arthan < rda@lemma-one.com >
********************************************************************************
$Id: wrk073.doc,v 1.36 2011/02/11 17:47:01 rda Exp rda $
********************************************************************************
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\usepackage{A4}
\usepackage{url}

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
\def\N{\mathbb{N}}
\def\D{\mathbb{D}}
\def\B{\mathbb{B}}
\def\C{\mathbb{C}}
\def\R{\mathbb{R}}
\def\Z{\mathbb{Z}}
\def\Q{\mathbb{Q}}

\def\EnumerateName{\mbox{{\sf enumerate}}}
\def\Enumerate#1{\EnumerateName_{#1}}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}

\def\LogName{\mbox{{\sf log}}}
\def\Log#1{\LogName(#1)}

\def\SinName{\mbox{{\sf sin}}}
\def\Sin#1{\SinName(#1)}

\def\CosName{\mbox{{\sf cos}}}
\def\Cos#1{\CosName(#1)}

\def\Abs#1{|#1|}

\def\ElemsName{\mbox{{\em Elems}}}
\def\Elems#1{\ElemsName(#1)}

\def\SizeName{\#}
\def\Size#1{\#\left(#1\right)}

%\def\Binomial#1#2{\left(\begin{array}{c}#1\\#2\end{array}\right)}
\def\Binomial#1#2{C_{#2}^{#1}}

\title{Mathematical Case Studies: Some Finite and Infinite Combinatorics\thanks{
First posted 22 November 2005;
for full changes history see: \protect\url{https://github.com/RobArthan/pp-contrib}.
}}
\author{Rob Arthan\\{\tt rda@lemma-one.com}}
\date{\FormatDate{\VCDate}}
\makeindex
\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}

This document presents some definitions and theorems from elementary finite and infinite combinatorics.
The definitions include a ``fold'' operator for finite sets and the operation that sums a real-valued function on a finite indexed set.
The theorems include: more facts about finiteness and the size of finite sets; algebraic properties of indexed sums; induction over finitely-supported functions; the inclusion/exclusion principle;
the binomial coefficients and their basic properties, including the formula for the number of combinations and the binomial theorem.
The theory is applied to give proofs of Bertrand's ballot theorem and the two-square theorem.
The main theorems in infinite combinatorics are the infinite versions of the pigeon-hole principle and
of Ramsey's theorem.

\end{abstract}
\vfill
\begin{centering}

\bf Copyright \copyright\ : Lemma 1 Ltd 2005--\number\year \\
Reference: LEMMA1/HOL/WRK073; Current git revision: \VCVersion%


\end{centering}
\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
\tableofcontents
\newpage

\section{INTRODUCTION}
This document is one of a set of documents containing mathematical case studies in  {\ProductHOL}.
It deals with some finite and infinite combinatorics.
Notable results include the inclusion/exclusion principle, the formula for the number of combinations,
the binomial theorem, Bertrand's ballot theorem and the infinite version of Ramsey's theorem.

Section~\ref{theory-fincomb} and~\ref{theory-infcomb} below give an overview of the material on finite and infinite combatorics respectively, including all the specifications
and a guide to the theorems proved.
Section~\ref{listing-fincomb} and \ref{listing-infcomb} contain listings of all the theorems proved
in the theories. An index to the specifications and the theorems is given at the end of the document.

\section{THE THEORY {\em fincomb}}\label{theory-fincomb}

\subsection{Preliminaries}
The following commands set up a theory to hold the definitions, theorems, etc.,  and a proof context that is convenient for the work.
The theory is a child of the theory ``analysis'' (defined in~\cite{LEMMA1/HOL/WRK066}) from which we use several definitions, in particular, the characteristic function $\chi_A$ of a set $A$.

=SML
force_delete_theory"fincomb" handle Fail _ => ();
open_theory"analysis";
new_theory"fincomb";
new_parent "set_thms";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=IGN
open_theory "fincomb";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=TEX
\subsection{Folding Binary Operators over Finite Sets}

The following definition of a ``fold'' operation for finite sets is parametrised by three things: an associative and commutative binary operator, $p$, with identity element, $e$, and a ``valuation'' function $v$; the operation maps the valuation function over a set combining the resulting values with the product operation.


ⓈHOLCONST
│ ⦏SetFold⦎ : 'a → ('a → 'a → 'a) → ('b → 'a) → 'b SET → 'a
├──────
│ ∀e p v⦁
│	(∀x⦁ p x e = x)
│ ∧	(∀x y⦁ p x y = p y x)
│ ∧	(∀x y z⦁ p (p x y) z = p x (p y z))
│ ⇒	SetFold e p v {}  = e
│ ∧	∀x a⦁	a ∈ Finite ∧ ¬x ∈ a
│	⇒	SetFold e p v ({x} ∪ a) = p (v x) (SetFold e p v a)
■
The parametrisation of {\em SetFold} is as recommended by Nipkow and Paulson and works nicely. An alternative would be to combine $p$ and $v$ into a single function, say $f = \lambda x y \bullet p(v x) y$
but then the algebraic laws that $f$ must satisfy have an unfamiliar form. The two approaches are interdefinable.

The theorems in the theory begin by with some lemmas about finite sets and their sizes.
These are then used to prove two lemmas needed to prove the consistency of the definition of {\em SetFold}.

\ThmsIII{%
=GFT
∪_finite_thm
elems_finite_thm
list_finite_size_thm1
=TEX
}{%
=GFT
list_finite_size_thm
set_fold_consistent_lemma1
set_fold_consistent_lemma2
=TEX
}{%
=GFT
SetFold_consistent
set_fold_def
=TEX
}

\subsection{Further Theorems About Finiteness}
The first block of theorems extends the repertoire of lemmas about finite sets and their sizes.
The approach to this topic in the {\ProductHOL} library tends to characterise a finite set, $A$, as one that can be written as $\Elems{L}$ for some list $L$ and the size $\Size{A}$ as the length $\Size{L}$ where $L$ is a list of distinct elements with $\Elems{L} = A$.

The first few theorems are aimed at an alternative characterisation of a finite set $A$ as one that is in one-one correspondence with an initial subset of the natural numbers, $\{i | i < m\}$ for some $m$.
{\em En route} are proved various useful facts, e.g., that finiteness and size are preserved under bijections.

\ThmsIII{%
=GFT
singleton_finite_thm
size_⊆_diff_thm
⊆_finite_size_thm
⊆_size_eq_thm
size_disjoint_∪_thm
∪_finite_size_≤_thm
=TEX
}{%
=GFT
range_finite_size_thm
length_map_thm
elems_map_thm
map_distinct_thm
nth_∈_elems_thm
elems_nth_thm
=TEX
}{%
=GFT
distinct_nth_thm
bijection_finite_size_thm
bijection_finite_size_thm1
range_bijection_finite_size_thm
surjection_finite_size_thm
range_finite_size_thm1
=TEX
}

The next block of theorems deal with the power set operator.
$\Zpset\,a$
 is defined in the {\ProductHOL} library by the bi-implication
$x \in \Zpset a \iff x \subseteq a$.
The first theorem below just recasts this as an equation.
There are then two trivial but quite useful lemmas about binary partitions of a power set.
This is followed by the theorem that, if $a$ is finite, then so is $\Zpset a$ and $\Size{\Zpset a} = 2^{\Size{a}}$

\ThmsII{%
=GFT
ℙ_thm
ℙ_split_thm
=TEX
}{%
=GFT
ℙ_split_thm1
ℙ_finite_size_thm
=TEX
}

\subsection{Sums over Finite Indexed Sets}
A useful application of the set fold operation is to define the following indexed sum operation. Given an index set, $a$, and a function, $f$, assigning a real number to each member of $a$,
=INLINEFT
IndSum a f
=TEX
\ is the indexed sum $\sum_{x\in a}f(x)$, and is defined for any set $a$ in which $f$ has finite support.


ⓈHOLCONST
│ ⦏IndSum⦎ : 'a SET → ('a → ℝ) → ℝ
├──────
│ ∀f⦁	IndSum {} f = ℕℝ 0
│ ∧	∀x a⦁	a ∈ Finite ∧ ¬x ∈ a
│	⇒	IndSum ({x} ∪ a) f = f x + IndSum a f
■

We will write $\sum\,a\,f$ as shorthand for
=INLINEFT
IndSum a f
=TEX
.
=SML
declare_alias("Σ", ⌜IndSum⌝);
=TEX

The consistency proof for {\em IndSum} is very simple given the set fold operation.
As with {\em SetFold}, the definition is intended to cover the two important cases where $a$ is finite ({\em ind\_sum\_def1}) or where $f$ has finite support ({\em ind\_sum\_def2}).

\ThmsII{%
=GFT
IndSum_consistent
=TEX
}{%
=GFT
ind_sum_def
=TEX
}

We now begin to develop the theory of indexed sums.
The first result is an example: if $A$ is finite,
then its size $\Size{A}$ may be calculated as the indexed sum $\sum_A\,1$.
The next few theorems show that the indexed sum operator $\sum_A\,f$ is linear in $f$ (i.e., it respects addition and multiplication by a constant) and give some useful consequences of this.

A principle that is applied almost unconsciously in informal reasoning is that the indexed sum $\sum_A f$ is a local property of $f$, in the sense that, if $f$ and $g$ are functions that agree on $A$, then $\sum_A f = \sum_A g$.
This block  of theorems concludes with one showing how indexed sums behave when the function is composed with a bijection: if $b$ is a bijection on the set $A$ and $B$ is the image of $A$ under $b$, then $\sum_B f = \sum_A (\lambda x\bullet f(b(x)))$

\ThmsIII{%
=GFT
ind_sum_size_thm
ind_sum_plus_thm
ind_sum_minus_thm
=TEX
}{%
=GFT
ind_sum_const_times_thm
ind_sum_0_thm
ind_sum_diff_0_thm
=TEX
}{%
=GFT
ind_sum_local_thm
ind_sum_0_bc_thm
bijection_ind_sum_thm
=TEX
}

We now have two lemmas for calculating the indexed sum in two cases where there is at most one non-zero value in the sum:

\ThmsII{
=GFT
ind_sum_χ_singleton_thm
=TEX
}{%
=GFT
ind_sum_singleton_thm
=TEX
}

Now we define the support of a real valued function.
ⓈHOLCONST
│ ⦏Supp⦎ : ('a → ℝ) → 'a SET
├──────
│ ∀ f⦁ Supp f = {x | ¬f x = ℕℝ 0}
■

Next comes an induction principle for functions of finite support, i.e., functions $f$ such that $f(x) \not= 0$ for at most finitely many $x$.
If $p$ is any property of functions that is true for the characteristic function, $\chi_{\{x\}}$, of any singleton set, $\{x\}$, and that is preserved under addition and multiplication by a constant (for operands of finite support), then $p(f)$ holds for any function $f$ of finite support.

In working with an indexed sum $\sum_A f$, one can always assume that $f$ has finite support (by adjusting it to be 0 outside $A$ if necessary). This induction principle gives a different line of attack on $\sum_A f$, which can be particularly useful if the internal structure of $A$ is complex.

\ThmsIII{
=GFT
fin_supp_induction_thm
=TEX
}{
=GFT
fin_supp_induction_thm1
=TEX
}{
=GFT
supp_clauses
=TEX
}

We will use the induction principle for functions of finite support to tackle the inclusion/exclusion principle.
The inclusion/exclusion principle deals with a family $U_i$ of sets where $i$ range over a finite and non-empty index set $I$.
The inclusion/exclusion principle is the following equation giving the size of the union of the $U_i$.
\begin{equation}
\Size{\bigcup_{i \in I} U_i} =
\sum_%
	{\begin{array}{c}J \in \Zpset I\\ J \not= \{\}\end{array}}%
		(-1)^{\Size{J} + 1}%
	\Size{\bigcap_{j \in J}U_j}
\end{equation}

This is a special case of a more general statement about indexed sums and the more general statement is actually rather simpler to prove.
The more general statement is the following, which holds for $U_i$ and $I$ above and any real-valued function $f$:
\begin{equation}
\sum_{x \in \bigcup_{i \in I} U_i} f(x)=
\sum_%
	{\begin{array}{c}J \in \Zpset I\\ J \not= \{\}\end{array}}%
		(-1)^{\Size{J} + 1}%
	\left(\sum_%
		{z \in \bigcap_{j \in J}U_j}%
			f(z)%
	\right)
\end{equation}

The statement about sizes follows immediately from the statement about indexed sums by applying it to the function $f(x) = 1$.
The statement about sums is better understood in the following more symmetric form in which $A = \bigcup_{i \in I}U_i$ is the range of the sum on the left-hand side of the above equation:
\begin{equation}
\sum_%
	{J \in \Zpset I}%
		(-1)^{\Size{J}}%
	\left(\sum_%
		{z \in A \cap \bigcap_{j \in J}U_j}%
			f(z)%
	\right) %
	= 0 \label{sym_inc_exc}
\end{equation}

Here, the intersections with $A$ in the range of the inner sum have no effect except when $J$ is empty.
The previous statement thus follows from the above simply by subtracting the sum over the non-empty $J$ from both sides of the equation.

It is quite natural to attempt to prove equation (\ref{sym_inc_exc}) by induction on $I$ (or on the size of $I$). This works, but the proof is somewhat complicated. Somewhat simpler is to work by induction on $A$, but it it still quite complex.
Instead, our proof of the inclusion/exclusion principle implements the above remarks together with the proof of equation (\ref{sym_inc_exc}) sketched below which works by induction on the structure of $f$.



Changing it to be identically 0 outside A if necessary, we may assume $f$ has finite support, and, as the left-hand side of (\ref{sym_inc_exc}) is easily seen to be linear in $f$, the principle of induction for functions of finite support means it is sufficient to prove (\ref{sym_inc_exc}) when $f = \chi_{\{x\}}$ is the characteristic function of a singleton set $\{x\}$.
For $f = \chi_{\{x\}}$, the summand $f(z)$ on the left-hand side of (\ref{sym_inc_exc}) is 1 or 0 according as $z = x$ or not.
Thus the inner sum is 1 if $x \in U_j$ for all $j \in J$ and vanishes otherwise.

So, if $x$ is not in any $U_j$, the left-hand side of (\ref{sym_inc_exc}) vanishes and we are done, and, if $x$ is in some $U_j$, (\ref{sym_inc_exc}) reduces to:
\begin{equation}
\sum_%
	{J \in \Zpset \{j \in I | x \in U_j\}}%
		(-1)^{\Size{J}}%
	= 0 \label{ind_sum_p}
\end{equation}

(Formally, we are appealing here to the special case of the inclusion/exclusion principle when $\Size{I}=2$, which states that $\sum_{B \cup C}f = \sum_B f + \sum_C f - \sum_{B \cap C}f$, with $B = \Zpset \{j \in I | x \in U_j\}$ and $C = \Zpset I \backslash B$.)

But now I claim that 
$
\sum_%
	{J \in \Zpset K}%
		(-1)^{\Size{J}}%
	= 0
$ for any non-empty indexed set $K$, which, taking $K=\{j \in I | x \in U_j\}$ in (\ref{ind_sum_p}) will complete the proof.

To see that $
\sum_%
	{J \in \Zpset K}%
		(-1)^{\Size{J}}%
	= 0
$ for any non-empty indexed set $K$, pick $k \in K$, then, as $J$ ranges over $\Zpset(K \backslash \{k\})$, the sets $J$ and $J \cup \{i\}$ range over $\Zpset K$ (with every member of $\Zpset K$ appearing exactly once).
As $(-1)^{\Size{J}} = -(-1)^{\Size{J \cup \{i\}}}$, the contributions of $J$ and $J \cup \{i\}$ cancel out and the sum is zero. (Formally, we are again using the special case of the principle for $\Size{I} = 2$ together with the result about indexed sums composed with a bijection.)

The above proof is captured in the following series of theorems, which give the main steps in the above argument in bottom-up order:

\ThmsIII{%
=GFT
ind_sum_∪_thm
ind_sum_ℙ_thm
=TEX
}{%
=GFT
ind_⋃_finite_thm
ind_sum_inc_exc_sym_thm
=TEX
}{%
=GFT
ind_sum_inc_exc_thm
size_inc_exc_thm
=TEX
}

A final block of theorems in this section are useful facts about supports and indexed sums of use elsewhere.



\ThmsIII{%
=GFT
supp_χ_thm
supp_plus_thm
=TEX
}{%
=GFT
ind_sum_supp_thm
ind_sum_transfer_thm
=TEX
}{%
=GFT
ind_sum_singleton_×_thm
ind_sum_×_thm
=TEX
}

\subsection{Binomial Coefficients}

We define the binomial coefficient $\Binomial{n}{m}$ by recursion equations in the usual way.
The consistency of the definition is proved automatically.

ⓈHOLCONST
│ ⦏Binomial⦎ : ℕ → ℕ → ℕ 
├──────
│	Binomial 0 0 = 1
│ ∧	(∀m⦁Binomial 0 (m+1) = 0)
│ ∧	(∀n⦁Binomial (n+1) 0 = 1)
│ ∧	(∀n m⦁ Binomial (n+1) (m+1) = Binomial n m + Binomial n (m+1))
■

After the inclusion/exclusion principle, we turn to something  a little simpler, proving that if $A$ is a set of size $n$, then $A$ has $\Binomial{n}{m}$ subsets of size $m$.
In a related vein we also prove the binomial theorem (but apart from the algebraic facts about the binomial function that are used, the proofs are separate).

We then have a couple of useful lemmas about the factorial function which are used to prove the formula $\Binomial{m+n}{m} = (n+m)!/m!*n!$.

\ThmsIII{%
=GFT
binomial_0_clauses
binomial_less_0_thm
binomial_eq_thm
=TEX
}{
=GFT
combinations_finite_size_thm
binomial_thm1
binomial_thm
=TEX
}{
=GFT
factorial_not_0_recip_thm
factorial_times_thm
binomial_factorial_thm
=TEX
}

\subsection{Sampling}

If $A$ is a finite set of size $s$ say, there are $s^n$ ways of taking an ordered sample of $m$ not necessarily distinct elements of $A$ (``sampling with replacement'').
If the samples are required to be distinct, then there are no samples unless $s = m + n \ge n$, say, and then the number of samples is $(m+n)(m+n-1)\ldots (m+1)$ (``sampling without replacement'').
The following function gives this quantity as a function of $m$ and $n$.
 
ⓈHOLCONST
│ ⦏DistinctSamples⦎ : ℕ → ℕ → ℕ
├──────
│ 	(∀n⦁ DistinctSamples n 0 = 1)
│ ∧	(∀m n⦁ DistinctSamples n (m+1) = (n+m+1) * DistinctSamples n m)
■

The following block of theorems help deal with sampling and provide some further useful combinatorial facts.
The first in the block proves the existence of a polymorphic enumeration function assigning to each finite set $A$,
a function $\Enumerate{A}$ which maps the set of natural numbers less than $\Size{A}$ bijectively onto $A$.
This is used to prove a theorem about ``coverings'': let us say a set $B$ {\em covers} another set $A$, if there is a function $f$ and a natural number $m$ mapping $B$ to $A$ such that the inverse images $f^{-1}(y)$ as $y$ ranges over $A$ are all finite and of size $m$; in these circumstances, then if $A$ is finite, so is $B$ and $\Size{B} = m \times \Size{A}$.

These facts (together with earlier counting principles) are then used to prove the statements made above about sampling, in which we use lists to represent ordered samples. This representation fits in nicely with earlier results connecting lists and finite sets.

\ThmsII{%
=GFT
enumerate_thm
covering_finite_size_thm
samples_finite_size_thm
=TEX
}{%
=GFT
distinct_samples_rw_thm
distinct_samples_up_thm
distinct_samples_finite_size_thm
=TEX
}

Determining probabilities in finite sample spaces is ``simply'' a matter of counting: if $S$ is finite sample space with $\Size{S} \not= 0$ and $X$ is a subset of $S$, then the probability that an event in $S$ belongs to $X$ is $\Size{X}/\Size{S}$.

The next theorem gives the well-known calculation that in a group of 23 people, the probability that at least two people have the same birthday is greater than $1/2$.
This is a simple consequence of the above theorems on sampling ($S$ and $S \ X$ being the set of samples of size 23 out of a set of size 365 with and without replacement respectively).
In section~\ref{ballot}, we do a harder example.

\ThmsIII{}{%
=GFT
birthdays_thm
=TEX
}{}

\subsection{Application: Bertrand's Ballot Theorem}\label{ballot}

In Bertrand's ballot problem a ballot is held between two candidates, North and South, say.
North beats South, the votes being counted one at a time by a single clerk.
The problem is to calculate the probability that at all times during the count, North had a majority over South.


The answer is the result of dividing the North's final majority by the total number of votes cast.
I.e., if the North receives $M$ votes and South $N$, the probability is $(M - N)/(M + N)$.

Following Feller~\cite{Feller68}, we represent the ballot problem using {\em walks} (also called ``paths'' in~\cite{Feller68}).
We define a {\em walk} of length $n$ starting at $x$ is a sequence of integers $s_i$ such that $s_0 = x$, $|s_{m+1} - s_m| = 1$ for $0 \le i < n$ and (for definiteness) $s_{m+1} = s_n$ for $m \ge n$.

ⓈHOLCONST
│ ⦏Walk⦎ : ℕ → ℤ → (ℕ → ℤ) SET
├──────
│ ∀n x s⦁
│	s ∈ Walk n x
│ ⇔	s 0 = x
│ ∧	(∀m⦁m < n ⇒ Abs(s(m+1) - s(m)) = ℕℤ 1)
│ ∧	(∀m⦁n ≤ m ⇒ s m = s n)
■

In talking about walks, we often identify a walk $s_i$ with the polygonal path obtained by joining the points $(i, s_i)$ in the plane. Under this identification a walk starting at $x$ of length $n$ begins at $(0, x)$, takes $n$ diagonal north-east or south-east steps and then heads directly east indefinitely.
The following definition captures the final $y$-value taken on by a walk.

ⓈHOLCONST
│ ⦏WalkTo⦎ : ℕ → ℤ → ℤ → (ℕ → ℤ) SET
├──────
│ ∀n x y s⦁
│	s ∈ WalkTo n x y
│ ⇔	s ∈ Walk n x ∧ s n = y
■

Walks satisfy a discrete version of the intermediate value theorem: if $x$, $y$ and $z$ are integers such that $z$ lies between $x$ and $y$ then any walk from $x$ to $y$ takes the value $z$ at some stage.



In the ballot problem, define $t_i$ to be the (possibly zero or negative) majority of North over South when the $i$-th vote is counted.
Then $t_i$ is a walk of length $M + N$ from $0$ to $M - N$ and any such walk corresponds to exactly one possible order in which to count the votes.

ⓈHOLCONST
│ ⦏BallotCounts⦎ : ℕ → ℕ → (ℕ → ℤ) SET
├──────
│ ∀m n⦁ BallotCounts m n = WalkTo (m + n) (ℕℤ 0) (ℕℤ m - ℕℤ n)
■

Thus the probability we have to calculate is $x/s$, where $s$ is the total number of walks, $t_i$, of length $M + N$ from $0$ to $M - N$, and where $x$ is the number of these that are {\em favourable}, i.e., that are such that $t_i > 0$ for $i > 0$.
For any $Q$, a walk of length $M + N$ from $Q$ to $Q + M - N$ is uniquely determined by the set of indices $i$ for which $t_{i+1} - t_i = 1$.
Thus the number of such walks is the number of ways of choosing $M$ numbers less than $M + N$, i.e., $s = \Binomial{M+N}{M}$.

To calculate the number of favourable walks, we use what Feller calls the {\em reflection principle}. This says that, if $i$ and $j$ are positive integers, then there is a one-to-one correspondence between walks of length $M+N$, $s_i$, from $i$ to $j$ which cross the $x$-axis and arbitrary walks of length $M+N$ from $-i$ to $j$. To see this one observes that, by the intermediate value theorem for walks, a walk, $t_i$, of the second sort must have $t_i = 0$ for some $i$; reflecting the initial negative segment of $t_i$ in the $x$-axis gives a walk $s_i$ of the first sort. This reflection defines the required one-to-one correspondence.

Now if $t_i$ is a favourable walk of length $M+N$ from $0$ to $M-N$ then $u_i = t_{i+1}$ defines a walk from $1$ to $M-N > 0$ which does not cross the $x$-axis.
From the reflection principle, we have that the number of such walks is $a = \Binomial{M+N-1}{M-1} - \Binomial{M+N-1}{M}$.
It then follows from a calculation using the expression of the binomial function in terms of factorials, that $x/s = (M-N)/(M+N)$.

The following block of theorems implements the proof sketched above.

\ThmsII{%
=GFT
walk_thm
walk_to_thm
walk_finite_size_thm
walk_to_finite_size_thm
walk_to_empty_thm
walk_to_finite_thm
walk_walk_to_thm
walk_shift_thm
walk_minus_thm
=TEX
}{%
=GFT
walk_to_minus_thm
walk_to_intermediate_value_thm
walk_to_reflection_thm
ballot_lemma1
ballot_lemma2
ballot_lemma3
ballot_lemma4
ballot_lemma5
ballot_thm
=TEX
}

\subsection{Involutions}

Involutions give some useful counting principles.

ⓈHOLCONST
│ ⦏Involution⦎ : 'a SET → ('a → 'a) SET
├──────
│ ∀f A⦁ f ∈ Involution A ⇔ (∀x⦁ x ∈ A ⇒ f x ∈ A ∧ f(f x) = x)
■
Fixed points are important:

ⓈHOLCONST
│ ⦏Fixed⦎ : ('a → 'a) → 'a SET
├──────
│ ∀x f⦁ x ∈ Fixed f ⇔ f x = x
■


We prove that every involution $f$ on a set $X$ has a fundamental region:
i.e., a subset $A$ such that $X$ decomposes as the disjoint
union of $A$, $f(A)$ and the fixed point set of $f$.
We use Zorn's lemma for this in the special case where the
ordered set comprises sets and inclusion.
The formulation of this case of Zorn's lemma in some versions
of {\Product} is hard to use directly, so we provide a more
convenient formulation.
After a few convenience lemmas, we then give the main
counting principles for involutions on finite sets:
if a set admits an involution with no fixed points, its size is even;
an involution on a set with an odd size has at least one fixed point;
if a set admits an involution with a unique fixed point, its size is odd.

\ThmsIII{%
=GFT
zorn_thm2
fund_region_thm
involution_one_one_thm
involution_def_thm1
=TEX
}{%
=GFT
involution_def_thm2
involution_size_thm
involution_even_size_thm
=TEX
}{%
=GFT
involution_odd_size_thm
involution_set_dif_fixed_thm
involution_fixed_singleton_thm
=TEX
}

\subsection{Application: the Two Squares Theorem}
We apply the theorems on involutions to do the combinatorial
part of Heath-Brown's ingenious proof of the theorem that
every prime congruent to 1 modulo 4 is the sum of two squares.
This requires a few preliminary lemmas on integer arithmetic.
Apart from variable names, the proof then follows closely the presentation of~\cite{Aigner00} (our sets $A$, $B$ and $C$ are Aigner \& G\"{u}nter's $S$, $T$ and $U$).
At each stage, rather than assume primality, we make the exact assumptions the combinatorial arguments require.
The proof is completed in ~\cite{LEMMA1/HOL/WRK074} where prime numbers are defined.

\ThmsIII{%
=GFT
ℤ_interval_finite_thm
ℤ_0_≤_square_thm
ℤ_0_less_0_less_times_thm
ℤ_0_less_times_thm
ℤ_0_less_times_thm1
ℤ_≤_square_thm
=TEX
}{%
=GFT
a_finite_thm
f_involution_a_thm
size_a_size_b_thm
size_a_size_c_thm
size_c_size_c_thm
=TEX
}{%
=GFT
g_involution_c_thm
size_c_thm
h_involution_b_thm
h_fixed_in_b_thm
two_squares_lemma
=TEX
}
\newpage
\section{THE THEORY {\em infcomb}}\label{theory-infcomb}
=SML
force_delete_theory "infcomb" handle Fail _ => ();
open_theory "fincomb";
new_theory "infcomb";
set_merge_pcs["basic_hol1", "'sets_alg"];
=TEX
The only definition we need is that of the class of infinite sets (which is simply to be
the complement of the class of finite sets):

ⓈHOLCONST
│ ⦏Infinite⦎ : 'a SET SET
├──────
│ Infinite = ~Finite
■

The theorems begin with a simple refactoring of the definition that characterizes
infinite sets as those admitting a one-to-one endofunction. This is used to show
that a set difference $a \mathop{\backslash} b$ where $a$ is infinite and $b$ is finite
is infinite and that a one-to-one image of an infinite set is infinite.
We then has some theorems about the natural numbers: they are infinite,
the minimum of an infinite subset of natural numbers is well-defined, an infinite
set of natural numbers is unbounded and an infinite set of natural numbers is the
range of an order-preserving function on the natural numbers.
With all this in hand we prove the infinite vefsions of the pigeon hole theorem and of
Ramsey's theorem. 
\ThmsII{%
=GFT
infinite_thm
infinite_diff_finite_thm
infinite_one_one_image_thm
ℕ_infinite_thm
min_infinite_thm
=TEX
}{%
=GFT
infinite_unbounded_thm
ordered_enumeration_thm
infinite_pigeon_hole_thm
infinite_ramsey_thm
=TEX
}

\newpage
\bibliographystyle{fmu}
\bibliography{fmu}

\appendix
{%\HOLindexOff
\let\Section\section
\let\subsection\Hide
\def\section#1{\Section{#1}\label{listing-fincomb}}
\let\subsection\Hide
\include{wrk0731.th}}

{%\HOLindexOff
\let\Section\section
\let\subsection\Hide
\def\section#1{\Section{#1}\label{listing-infcomb}}
\let\subsection\Hide
\include{wrk0732.th}}

=TEX

\twocolumn[\section*{INDEX}\label{INDEX}]
\addcontentsline{toc}{section}{INDEX}
{\small\printindex}

\end{document} %% COMMENT THIS LINE OUT TO TYPESET THE PROOF SCRIPTS
\section{PROOFS IN THE THEORY {\em fincomb}}
=TEX
%%%%
%%%%
=SML
open_theory"fincomb";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
val ⦏supp_def⦎ = get_spec ⌜Supp⌝;
val ⦏binomial_def⦎ = get_spec ⌜Binomial⌝;
val ⦏distinct_samples_def⦎ = get_spec ⌜DistinctSamples⌝;
val ⦏walk_def⦎ = get_spec ⌜Walk⌝;
val ⦏walk_to_def⦎ = get_spec ⌜WalkTo⌝;
val ⦏ballot_counts_def⦎ = get_spec ⌜BallotCounts⌝;
val ⦏ℕ_exp_def⦎ = get_spec ⌜1 ^ 2⌝;
val ⦏involution_def⦎ = get_spec ⌜Involution⌝;
val ⦏fixed_def⦎ = get_spec ⌜Fixed⌝;
=TEX
%%%%
%%%%

=SML
val ⦏ℕℝ_ℕ_exp_thm⦎ = save_thm ( "ℕℝ_ℕ_exp_thm", (
set_goal([], ⌜∀m n:ℕ⦁ℕℝ (m^n) = ℕℝ m ^ n⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝
	THEN  rewrite_tac[ℝ_ℕ_exp_def, ℕ_exp_def]);
a(asm_rewrite_tac[ℕℝ_times_homomorphism_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ℤ_abs_eq_1_thm⦎ = save_thm ( "ℤ_abs_eq_1_thm", (
set_goal([], ⌜∀x⦁ Abs x = ℕℤ 1 ⇔ x = ℕℤ 1 ∨ x = ~(ℕℤ 1)⌝);
a(∀_tac THEN PC_T1 "predicates" cases_tac⌜ℕℤ 0 ≤ x⌝
	THEN asm_rewrite_tac[ℤ_abs_def]
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_def1⦎ = save_thm("walk_def1", rewrite_rule[ℤ_abs_eq_1_thm] walk_def);
=TEX
The following three should definitely go in the finite sets theory soon. !!! TBD !!!
%%%%
%%%%
=SML
val ⦏∪_finite_thm⦎ = save_thm ( "∪_finite_thm", (
set_goal([], ⌜∀A B⦁
	 (A ∪ B) ∈ Finite ⇔ A ∈ Finite ∧ B ∈ Finite
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac ⌜A ⊆ A ∪ B⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
(* *** Goal "2" *** *)
a(lemma_tac ⌜B ⊆ A ∪ B⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
(* *** Goal "3" *** *)
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜B⌝, ⌜B⌝));
a(finite_induction_tac ⌜A⌝ THEN1 asm_rewrite_tac[]);
a(REPEAT strip_tac);
a(LEMMA_T⌜({x} ∪ A) ∪ B = {x} ∪ A ∪ B⌝
	rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(bc_thm_tac singleton_∪_finite_thm THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏min_∈_thm⦎ = save_thm ( "min_∈_thm", (
set_goal([], ⌜∀n a⦁ n ∈ a ⇒ Min a ∈ a⌝);
a(∀_tac THEN cov_induction_tac ⌜n:ℕ⌝ THEN REPEAT strip_tac);
a(cases_tac⌜∃m⦁ m < n ∧ m ∈ a⌝);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜Min a = n⌝ asm_rewrite_thm_tac);
a(bc_thm_tac(get_spec⌜Min⌝) THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜i⌝);
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏min_≤_thm⦎ = save_thm ( "min_≤_thm", (
set_goal([], ⌜∀n a⦁ n ∈ a ⇒ Min a ≤ n⌝);
a(∀_tac THEN cov_induction_tac ⌜n:ℕ⌝ THEN REPEAT strip_tac);
a(cases_tac⌜∃m⦁ m < n ∧ m ∈ a⌝);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜Min a = n⌝ rewrite_thm_tac);
a(bc_thm_tac(get_spec⌜Min⌝) THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜i⌝);
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏elems_finite_thm⦎ = save_thm ( "elems_finite_thm", (
set_goal([], ⌜∀list⦁ Elems list ∈ Finite⌝);
a(REPEAT strip_tac);
a(list_induction_tac ⌜list⌝
	THEN asm_rewrite_tac[elems_def, empty_finite_thm]);
a(ALL_FC_T rewrite_tac[singleton_∪_finite_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏list_finite_size_thm1⦎ = save_thm ( "list_finite_size_thm1", (
set_goal([], ⌜∀a⦁
	 a ∈ Finite
⇔	∃list⦁list ∈ Distinct ∧ Elems list = a ∧ #list = #a⌝);
a(REPEAT_UNTIL is_∧ strip_tac THEN strip_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN all_fc_tac[finite_distinct_elems_thm]);
a(∃_tac⌜list⌝ THEN REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[distinct_size_length_thm]);
(* *** Goal "2" *** *)
a(strip_tac THEN all_var_elim_asm_tac1 THEN rewrite_tac[elems_finite_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏list_finite_size_thm⦎ = save_thm ( "list_finite_size_thm", (
set_goal([], ⌜∀a m⦁
	 a ∈ Finite ∧ #a = m
⇔	∃list⦁list ∈ Distinct ∧ Elems list = a ∧ #list = m⌝);
a(REPEAT_UNTIL is_∧ strip_tac THEN strip_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN all_var_elim_asm_tac1 THEN POP_ASM_T ante_tac);
a(rewrite_tac[list_finite_size_thm1]);
(* *** Goal "2" *** *)
a(strip_tac THEN all_fc_tac[distinct_size_length_thm]
	THEN all_var_elim_asm_tac1
	THEN asm_rewrite_tac[elems_finite_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏set_fold_consistent_lemma1⦎ = save_thm ( "set_fold_consistent_lemma1", (
set_goal([], ⌜∀x list1 n⦁
	x ∈ Elems list1 ∧ list1 ∈ Distinct ∧ #list1 = n + 1 
⇒	∃list2⦁ list2 ∈ Distinct ∧ Elems list2 = Elems list1 \ {x}
	∧ #list2 = n⌝);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) list_finite_size_thm]);
a(REPEAT ∀_tac THEN ⇒_tac);
a(once_rewrite_tac[prove_rule[]⌜∀p q⦁p ∧ q ⇔ (p ∧ (p ⇒ q))⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ⊆_finite_thm);
a(∃_tac⌜Elems list1⌝ THEN rewrite_tac[elems_finite_thm]);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜#(Elems list1) = #list1⌝ ante_tac
	THEN1 (bc_thm_tac distinct_size_length_thm
		THEN REPEAT strip_tac));
a(LEMMA_T⌜Elems list1 = {x} ∪ Elems list1 \ {x}⌝ (fn th => conv_tac(LEFT_C(once_rewrite_conv[th])))
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(LEMMA_T⌜¬x ∈ Elems list1 \ {x}⌝ asm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏set_fold_consistent_lemma2⦎ = save_thm ( "set_fold_consistent_lemma2", (
set_goal([], ⌜∀e p v⦁
	(∀x⦁ p x e = x)
∧	(∀x y⦁ p x y = p y x)
∧	(∀x y z⦁ p (p x y) z = p x (p y z))
⇒	∀n list1 list2⦁
	list1 ∈ Distinct ∧ list2 ∈ Distinct
∧	#list1 = n
∧	Elems list1 = Elems list2
⇒	Fold (λ x y⦁ p (v x) y) list1 e
=	Fold (λ x y⦁ p (v x) y) list2 e⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN ∀_tac);
a(induction_tac⌜n⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜list1 = [] ∧ list2 = []⌝
	(fn th => rewrite_tac[th, fold_def]));
a(DROP_NTH_ASM_T 2 ante_tac);
a(strip_asm_tac (∀_elim⌜list1⌝ list_cases_thm)
	THEN asm_rewrite_tac[length_def]
	THEN all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac THEN rewrite_tac[elems_def]);
a(strip_asm_tac (∀_elim⌜list2⌝ list_cases_thm)
	THEN asm_rewrite_tac[elems_def]
	THEN all_var_elim_asm_tac1);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜#(Elems list1) = #list1⌝ ante_tac
	THEN1 (bc_thm_tac distinct_size_length_thm
		THEN REPEAT strip_tac));
a(TOP_ASM_T rewrite_thm_tac);
a(LEMMA_T⌜#(Elems list2) = #list2⌝ rewrite_thm_tac
	THEN1 (bc_thm_tac distinct_size_length_thm
		THEN REPEAT strip_tac));
a(GET_NTH_ASM_T 2 rewrite_thm_tac THEN strip_tac);
a(DROP_NTH_ASM_T 3 ante_tac);
a(strip_asm_tac (∀_elim⌜list1⌝ list_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[length_def]
	THEN strip_tac);
a(DROP_NTH_ASM_T 2 ante_tac);
a(strip_asm_tac (∀_elim⌜list2⌝ list_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[length_def]);
a(rename_tac[(⌜list2'⌝, "L1"), (⌜list2''⌝, "L2")]
	THEN strip_tac);
a(cases_tac⌜x' = x⌝
	THEN1 all_var_elim_asm_tac);
(* *** Goal "2.1" *** *)
a(LIST_DROP_NTH_ASM_T [3, 4]
	(MAP_EVERY (strip_asm_tac o rewrite_rule[distinct_def])));
a(DROP_NTH_ASM_T 6 ante_tac);
a(rewrite_tac[elems_def] THEN REPEAT strip_tac);
a(LEMMA_T⌜∀a b⦁¬x ∈ a ∧ ¬ x ∈ b ∧ {x} ∪ a = {x} ∪ b ⇒ a = b⌝ (fn th => all_fc_tac[th])
	THEN1 PC_T1 "sets_ext" REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(spec_nth_asm_tac 2 ⌜x'⌝ THEN all_var_elim_asm_tac1);
(* *** Goal "2.1.2" *** *)
a(spec_nth_asm_tac 2 ⌜x'⌝ THEN all_var_elim_asm_tac1);
(* *** Goal "2.1.3" *** *)
a(rewrite_tac[fold_def]);
a(bc_thm_tac(prove_rule [] ⌜∀a b ⦁a = b ⇒ p (v x') a = p (v x') b⌝));
a(DROP_NTH_ASM_T 8 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(LIST_DROP_NTH_ASM_T [4, 5]
	(MAP_EVERY (strip_asm_tac o rewrite_rule[distinct_def])));
a(LEMMA_T⌜x' ∈ Elems(Cons x L1)⌝ ante_tac
	THEN1 (DROP_NTH_ASM_T 7 rewrite_thm_tac
		THEN PC_T1 "sets_ext1" rewrite_tac[elems_def]));
a(PC_T1 "sets_ext1" rewrite_tac[elems_def]);
a(REPEAT strip_tac);
a(lemma_tac⌜¬#L1 = 0⌝
	THEN1 (strip_asm_tac (∀_elim⌜L1⌝ list_cases_thm)
		THEN all_var_elim_asm_tac1
		THEN all_asm_ante_tac
		THEN rewrite_tac[length_def, elems_def]));
a(LEMMA_T⌜1 ≤ #L1⌝ (strip_asm_tac o
	once_rewrite_rule[plus_comm_thm] o
		rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(POP_ASM_T (strip_asm_tac o eq_sym_rule));
a(all_fc_tac[set_fold_consistent_lemma1]);
a(rename_tac[(⌜list2⌝, "T1")]
	THEN rewrite_tac[fold_def]);
a(LEMMA_T⌜
	Fold (λ x'' y⦁ p (v x'') y) L1 e =
	Fold (λ x'' y⦁ p (v x'') y) (Cons x' T1) e⌝
	rewrite_thm_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 14 bc_thm_tac);
a(asm_rewrite_tac[distinct_def, elems_def]);
a(PC_T1 "sets_ext1" rewrite_tac[]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac);
(* *** Goal "2.2.2" *** *)
a(rewrite_tac[fold_def]);
a(GET_NTH_ASM_T 15 (rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(DROP_NTH_ASM_T 16 (fn th => conv_tac
(LEFT_C(RATOR_C(RAND_C(once_rewrite_conv[th]))))));
a(DROP_NTH_ASM_T 15 rewrite_thm_tac);
a(bc_thm_tac(prove_rule [] ⌜∀a b ⦁a = b ⇒ p (v x') a = p (v x') b⌝));
a(LEMMA_T⌜
	Fold (λ x'' y⦁ p (v x'') y) L2 e =
	Fold (λ x'' y⦁ p (v x'') y) (Cons x T1) e⌝
	(rewrite_thm_tac o rewrite_rule[fold_def]));
a(DROP_NTH_ASM_T 14 bc_thm_tac);
a(DROP_NTH_ASM_T 13 ante_tac);
a(asm_rewrite_tac[distinct_def, elems_def]);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 12 (strip_asm_tac o conv_rule(RAND_C eq_sym_conv)));
a(ALL_FC_T rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀x y a⦁ ¬x = y ⇒ {x} ∪ a \ {y} = ({x} ∪ a) \ {y}⌝]);
a(asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" rewrite_tac[]);
a(contr_tac THEN all_var_elim_asm_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜SetFold⌝;
a(lemma_tac⌜∃r⦁ ∀a:'b SET⦁ a ∈ Finite ⇒ r a ∈ Distinct
	∧ Elems(r a) = a
	∧ #(r a) = #a⌝);
(* *** Goal "1" *** *)
a(prove_∃_tac THEN strip_tac);
a(cases_tac⌜a' ∈ Finite⌝ THEN asm_rewrite_tac[]);
a(asm_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) list_finite_size_thm]);
(* *** Goal "2" *** *)
a(prove_∃_tac THEN REPEAT strip_tac);
a(∃_tac ⌜λa⦁ Fold (λx y⦁p' (v' x) y) (r a) e'⌝
	THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LEMMA_T⌜r{} = []⌝ (fn th => rewrite_tac[th, fold_def]));
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜{}:'b SET⌝));
a(strip_asm_tac (∀_elim⌜r{}⌝ list_cases_thm)
	THEN asm_rewrite_tac[]);
a(rewrite_tac[empty_finite_thm, size_empty_thm, length_def]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜{x} ∪ a ∈ Finite⌝ 
	THEN1 (bc_thm_tac singleton_∪_finite_thm
		THEN REPEAT strip_tac));
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(LEMMA_T⌜
	Fold (λ x y⦁ p' (v' x) y) (r ({x} ∪ a)) e' =
	(Fold (λ x y⦁ p' (v' x) y) (Cons x (r a)) e')⌝
	(rewrite_thm_tac o rewrite_rule[fold_def]));
a(ante_tac(list_∀_elim[⌜e'⌝, ⌜p'⌝, ⌜v'⌝]set_fold_consistent_lemma2));
a(PC_T1 "'propositions" asm_rewrite_tac[]);
a(STRIP_T bc_thm_tac);
a(∃_tac⌜#a + 1⌝ THEN asm_rewrite_tac[distinct_def, elems_def]);
a(bc_thm_tac size_singleton_∪_thm THEN REPEAT strip_tac);
val _ = save_consistency_thm ⌜SetFold⌝ (pop_thm());
val ⦏set_fold_def⦎ = save_thm("set_fold_def", get_spec ⌜SetFold⌝);
=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜IndSum⌝;
a(∃_tac ⌜λa f⦁SetFold (ℕℝ 0) ($ +) f a⌝);
a(∀_tac THEN rewrite_tac[] THEN bc_thm_tac(set_fold_def));
a(rewrite_tac[ℝ_plus_assoc_thm]);
val _ = save_consistency_thm ⌜Σ⌝ (pop_thm());
val ⦏ind_sum_def⦎ = save_thm("ind_sum_def", get_spec ⌜Σ⌝);
=TEX
%%%%
%%%%
=SML
val ⦏singleton_finite_thm⦎ = save_thm("singleton_finite_thm",
	rewrite_rule[empty_finite_thm]
		(∀_elim⌜{}⌝ singleton_∪_finite_thm));
=TEX
%%%%
%%%%
=SML
val ⦏size_⊆_diff_thm⦎ = save_thm ( "size_⊆_diff_thm", (
set_goal([], ⌜∀a b⦁ a ∈ Finite ∧ b ⊆ a ⇒ #a = #(a \ b) + #b⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜a \ b ⊆ a ∧ (a \ b) ∩ b = {} ∧ a = (a \ b) ∪ b⌝
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(DROP_NTH_ASM_T 3 (fn th => (conv_tac(LEFT_C(once_rewrite_conv[th])))));
a(ante_tac (list_∀_elim[⌜a \ b⌝, ⌜b⌝] size_∪_thm));
a(asm_rewrite_tac[size_empty_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏⊆_finite_size_thm⦎ = save_thm("⊆_finite_size_thm", (
set_goal([], ⌜∀a b⦁ a ∈ Finite ∧ b ⊆ a ⇒ b ∈ Finite ∧ #b ≤ #a⌝);
a(REPEAT strip_tac THEN1 all_fc_tac[⊆_finite_thm]);
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜b⌝, ⌜b⌝));
a(finite_induction_tac⌜a⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜b = {}⌝ rewrite_thm_tac);
a(PC_T1"sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜x ∈ b⌝);
(* *** Goal "2.1" *** *)
a(PC_T1 "predicates" lemma_tac⌜b \ {x} ⊆ a ∧ ¬x ∈ b \ {x}⌝
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(LEMMA_T⌜b = {x} ∪ (b \ {x})⌝ once_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜b ⊆ a⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2.2.1" *** *)
a(asm_fc_tac[] THEN all_var_elim_asm_tac);
(* *** Goal "2.2.2" *** *)
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(asm_fc_tac[] THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));
=TEX
%%%%
%%%%

=SML
val ⦏⊆_size_eq_thm⦎ = save_thm ("⊆_size_eq_thm", (
set_goal([],⌜∀a b⦁ a ∈ Finite ∧ b ⊆ a ∧ #b = #a ⇒ b = a⌝);
a(contr_tac);
a(lemma_tac⌜a \ b ⊆ a ∧ ¬a \ b = {}⌝ THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(LEMMA_T ⌜# (b ∪ (a \ b)) + # (b ∩ (a \ b)) = # b + # (a \ b)⌝ ante_tac THEN1
	(bc_thm_tac size_∪_thm THEN REPEAT strip_tac));
a(LEMMA_T ⌜b ∪ (a \ b) = a ∧ b ∩ (a \ b) = {}⌝ rewrite_thm_tac THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(rewrite_tac[size_empty_thm]);
a(lemma_tac ⌜¬ #(a \ b) = 0⌝ THEN_LIST
	[id_tac, PC_T1 "lin_arith" asm_prove_tac[]]);
a(ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[size_0_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏size_disjoint_∪_thm⦎ = save_thm ( "size_disjoint_∪_thm", (
set_goal([], ⌜∀a b c⦁
	a ∈ Finite
∧	a = b ∪ c
∧	b ∩ c = {}
⇒	#a = #b + #c
⌝);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(all_asm_ante_tac THEN rewrite_tac[∪_finite_thm]
	THEN REPEAT strip_tac);
a(LEMMA_T⌜# (b ∪ c) + # (b ∩ c) = # b + # c⌝ ante_tac
	THEN1 all_fc_tac[size_∪_thm]);
a(asm_rewrite_tac[size_empty_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏∪_finite_size_≤_thm⦎ = save_thm ( "∪_finite_size_≤_thm", (
set_goal([], ⌜∀a b⦁
	a ∈ Finite
∧	b ∈ Finite
⇒	a ∪ b ∈ Finite ∧ #(a ∪ b) ≤ #a + #b
⌝);
a(REPEAT strip_tac THEN1 asm_rewrite_tac[∪_finite_thm]);
a(LEMMA_T⌜# (a ∪ b) + # (a ∩ b) = # a + # b⌝ ante_tac
	THEN1 all_fc_tac[size_∪_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏range_finite_size_thm⦎ = save_thm ( "range_finite_size_thm", (
set_goal([], ⌜∀m⦁ {i | i < m} ∈ Finite ∧ #{i | i < m} = m⌝);
a(∀_tac THEN rewrite_tac[list_finite_size_thm]);
a(induction_tac⌜m⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜[]⌝ THEN rewrite_tac[distinct_def,
	elems_def, length_def]);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜Cons m list⌝ THEN asm_rewrite_tac[distinct_def,
	elems_def, length_def]);
a(DROP_ASMS_T discard_tac
	THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏length_map_thm⦎ = save_thm ( "length_map_thm", (
set_goal([], ⌜∀f list⦁ #(Map f list) = # list⌝);
a(REPEAT strip_tac);
a(list_induction_tac ⌜list⌝
	THEN asm_rewrite_tac[map_def, length_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏elems_map_thm⦎ = save_thm ( "elems_map_thm", (
set_goal([], ⌜∀f list⦁ 
	Elems (Map f list) = {y | ∃x⦁x ∈ Elems list ∧ y = f x}⌝);
a(REPEAT strip_tac);
a(list_induction_tac ⌜list⌝
	THEN asm_rewrite_tac[map_def, elems_def]
	THEN REPEAT strip_tac
	THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏map_distinct_thm⦎ = save_thm ( "map_distinct_thm", (
set_goal([], ⌜∀f list⦁ 
	(∀ x y⦁ x ∈ Elems list ∧ y ∈ Elems list ∧ f x = f y ⇒ x = y)
∧	list ∈ Distinct
⇒	Map f list ∈ Distinct⌝);
a(REPEAT ∀_tac);
a(intro_∀_tac(⌜f⌝, ⌜f⌝) THEN list_induction_tac ⌜list⌝
	THEN asm_rewrite_tac[map_def, distinct_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[elems_map_thm] THEN REPEAT strip_tac);
a(swap_nth_asm_concl_tac 3);
a(LEMMA_T⌜x = x'⌝ asm_rewrite_thm_tac);
a(DROP_NTH_ASM_T 4 bc_thm_tac);
a(PC_T1 "sets_ext1" asm_rewrite_tac[elems_def]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 6 bc_thm_tac);
a(PC_T1 "sets_ext1" asm_rewrite_tac[elems_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏nth_∈_elems_thm⦎ = save_thm ( "nth_∈_elems_thm", (
set_goal([], ⌜∀list i⦁ 
	i < #list
⇒	Nth list (i+1) ∈ Elems list⌝);
a(∀_tac);
a(list_induction_tac ⌜list⌝
	THEN asm_rewrite_tac[elems_def, nth_def, length_def]);
a(REPEAT ∀_tac);
a(cases_tac⌜i = 0⌝ THEN asm_rewrite_tac[]
	THEN1 PC_T1 "sets_ext1" rewrite_tac[]);
a(REPEAT strip_tac);
a(lemma_tac⌜1 ≤ i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def]));
a(DROP_NTH_ASM_T 4 discard_tac THEN all_var_elim_asm_tac1);
a(once_rewrite_tac[plus_comm_thm]);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏elems_nth_thm⦎ = save_thm ( "elems_nth_thm", (
set_goal([], ⌜∀list⦁ 
	Elems list = {x | ∃i⦁ i < #list ∧ Nth list (i+1) = x}⌝);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜x⌝, ⌜x⌝));
a(list_induction_tac ⌜list⌝
	THEN MERGE_PCS_T1 ["sets_ext1", "basic_hol"]
		asm_rewrite_tac[elems_def, nth_def, length_def]);
a(REPEAT ∀_tac);
a(cases_tac⌜x' = x⌝ THEN asm_rewrite_tac[]
	THEN1 (∃_tac⌜0⌝ THEN asm_rewrite_tac[]));
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
a(∃_tac⌜i+1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a(all_var_elim_asm_tac1 THEN all_fc_tac[nth_∈_elems_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏distinct_nth_thm⦎ = save_thm ( "distinct_nth_thm", (
set_goal([], ⌜∀list i j⦁ 
	list ∈ Distinct
∧	i < #list ∧ j < #list
∧	Nth list (i+1) = Nth list (j+1)
⇒	i = j⌝);
a(∀_tac);
a(list_induction_tac ⌜list⌝
	THEN asm_rewrite_tac[length_def, nth_def, distinct_def]);
a(REPEAT ∀_tac);
a(cases_tac⌜i = 0⌝ THEN cases_tac⌜j = 0⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 3);
a(LEMMA_T ⌜1 ≤ j⌝ (strip_asm_tac o once_rewrite_rule[plus_comm_thm]
		o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 4 discard_tac THEN all_var_elim_asm_tac1);
a(bc_thm_tac nth_∈_elems_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜1 ≤ i⌝ (strip_asm_tac o once_rewrite_rule[plus_comm_thm]
		o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 4 discard_tac THEN all_var_elim_asm_tac1);
a(bc_thm_tac nth_∈_elems_thm THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(LEMMA_T ⌜1 ≤ i ∧ 1 ≤ j⌝ (strip_asm_tac o once_rewrite_rule[plus_comm_thm]
		o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [8, 9] discard_tac THEN all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [6] (ALL_FC_T rewrite_tac));
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏bijection_finite_size_thm⦎ = save_thm ( "bijection_finite_size_thm", (
set_goal([], ⌜∀a b f⦁
	 a ∈ Finite
∧	(∀x y⦁x ∈ a ∧ y ∈ a ∧ f x = f y ⇒ x = y)
∧	b = {z | ∃x⦁x ∈ a ∧ z = f x}
⇒	b ∈ Finite ∧ #b = #a⌝);
a(rewrite_tac[list_finite_size_thm] THEN REPEAT strip_tac);
a(all_fc_tac[finite_distinct_elems_thm]);
a(all_fc_tac[distinct_size_length_thm]);
a(all_var_elim_asm_tac1 THEN ∃_tac ⌜Map f list⌝);
a(asm_rewrite_tac[length_map_thm, elems_map_thm]
	THEN REPEAT strip_tac);
a(bc_thm_tac map_distinct_thm);
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏bijection_finite_size_thm1⦎ = save_thm ( "bijection_finite_size_thm1", (
set_goal([], ⌜∀a b f⦁
	 a ∈ Finite
∧	(∀x y⦁x ∈ b ∧ y ∈ b ∧ f x = f y ⇒ x = y)
∧	a = {z | ∃x⦁x ∈ b ∧ z = f x}
⇒	b ∈ Finite ∧ #b = #a⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN bc_thm_tac bijection_finite_size_thm);
a(∃_tac⌜λz⦁εx⦁x ∈ b ∧ f x = z⌝ THEN rewrite_tac[]
	THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1 THEN all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac THEN all_ε_tac
	THEN_TRY SOLVED_T (asm_prove_tac[]));
a(LIST_DROP_NTH_ASM_T[7] (ALL_FC_T rewrite_tac));
a(STRIP_T rewrite_thm_tac);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(∃_tac⌜f x⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN1 asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_ε_tac THEN1 asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T[4] (ALL_FC_T rewrite_tac));
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1 THEN all_var_elim_asm_tac1);
a(all_ε_tac THEN asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏range_bijection_finite_size_thm⦎ = save_thm ( "range_bijection_finite_size_thm", (
set_goal([], ⌜∀a m⦁
	 a ∈ Finite ∧ #a = m
⇔	∃f⦁	(∀i j⦁i < m ∧ j < m ∧ f i = f j ⇒ i = j)
	∧ 	a = {x | ∃i⦁i < m ∧ f i = x}⌝);
a(REPEAT_UNTIL is_∧ strip_tac THEN strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[list_finite_size_thm]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(∃_tac⌜λi⦁Nth list (i+1)⌝ THEN rewrite_tac[]);
a(REPEAT strip_tac THEN1 all_fc_tac[distinct_nth_thm]);
a(rewrite_tac[elems_nth_thm]);
(* *** Goal "2" *** *)
a(strip_tac);
a(once_rewrite_tac[
	eq_sym_rule(∧_right_elim(∀_elim⌜m⌝ range_finite_size_thm))]);
a(bc_thm_tac bijection_finite_size_thm);
a(∃_tac⌜f⌝ THEN asm_rewrite_tac[range_finite_size_thm]);
a(conv_tac(LEFT_C (ONCE_MAP_C eq_sym_conv)));
a(rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏surjection_finite_size_thm⦎ = save_thm( "surjection_finite_size_thm", (
set_goal([], ⌜∀a b f⦁
	a ∈ Finite
∧	b ⊆ {z | ∃x⦁x ∈ a ∧ z = f x}
⇒	b ∈ Finite ∧ #b ≤ #a⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac⌜{z | ∃x⦁x ∈ a ∧ z = f x} ∈ Finite ∧ #{z | ∃x⦁x ∈ a ∧ z = f x} ≤ #a⌝);
(* *** Goal "1" *** *)
a(POP_ASM_T discard_tac THEN finite_induction_tac⌜a⌝);
(* *** Goal "1.1" *** *)
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜{x|F}= {}⌝,
	empty_finite_thm, size_empty_thm]);
(* *** Goal "1.2" *** *)
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(cases_tac⌜{z|∃ x'⦁ x' ∈ {x} ∪ a ∧ z = f x'} = 
	{z|∃ x⦁ x ∈ a ∧ z = f x}⌝
	THEN1 (asm_rewrite_tac[]
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(LEMMA_T⌜{z|∃ x'⦁ x' ∈ {x} ∪ a ∧ z = f x'} = 
	{f x} ∪ {z|∃ x⦁ x ∈ a ∧ z = f x}⌝ rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" prove_tac[]));
a(CASES_T⌜¬f x ∈ {z|∃ x⦁ x ∈ a ∧ z = f x}⌝ asm_tac
	THEN1 (all_fc_tac[singleton_∪_finite_thm,
		size_singleton_∪_thm]
		THEN asm_rewrite_tac[]));
a(i_contr_tac THEN POP_ASM_T ante_tac THEN POP_ASM_T ante_tac);
a(DROP_ASMS_T discard_tac THEN PC_T1 "sets_ext1" rewrite_tac[]
	THEN_TRY all_var_elim_asm_tac1
	THEN asm_prove_tac[]
	THEN all_var_elim_asm_tac1 THEN asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_fc_tac[⊆_finite_size_thm] THEN REPEAT strip_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));
=TEX
%%%%
%%%%
=SML
val ⦏range_finite_size_thm1⦎ = save_thm ( "range_finite_size_thm1", (
set_goal([], ⌜∀m⦁ {i | 1 ≤ i ∧ i ≤ m} ∈ Finite ∧ #{i | 1 ≤ i  ∧ i ≤ m} = m⌝);
a(∀_tac THEN strip_asm_tac(∀_elim⌜m:ℕ⌝range_finite_size_thm));
a(POP_ASM_T(fn th => conv_tac(RIGHT_C(RIGHT_C(once_rewrite_conv[eq_sym_rule th])))));
a(bc_thm_tac bijection_finite_size_thm);
a(∃_tac⌜λk⦁k + 1⌝ THEN asm_rewrite_tac[]
	THEN PC_T1 "sets_ext" REPEAT strip_tac
	THEN_TRY (all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(all_asm_ante_tac THEN rewrite_tac[≤_def] THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(∃_tac⌜i⌝ THEN PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏range_bijection_finite_size_thm1⦎ = save_thm ( "range_bijection_finite_size_thm1", (
set_goal([], ⌜∀a⦁
	 a ∈ Finite
⇔	∃f⦁	(∀i j⦁i < #a ∧ j < #a ∧ f i = f j ⇒ i = j)
	∧ 	a = {x | ∃i⦁i < #a ∧ f i = x}⌝);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) range_bijection_finite_size_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ℕ_exp_def⦎ = get_spec ⌜1 ^ 2⌝;
=TEX
%%%%
%%%%
=SML
val ⦏ℙ_thm⦎ = save_thm ( "ℙ_thm", (
set_goal([], ⌜∀a⦁ ℙ a = {b | b ⊆ a}⌝);
a(REPEAT strip_tac THEN PC_T "sets_ext1" strip_tac);
a(rewrite_tac[ℙ_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ℙ_split_thm⦎ = save_thm ( "ℙ_split_thm", (
set_goal([], ⌜∀x a⦁
	ℙ a = {b | b ⊆ a ∧ x ∈ b} ∪ {b | b ⊆ a ∧ ¬x ∈ b}
∧	{b | b ⊆ a ∧ x ∈ b} ∩ {b | b ⊆ a ∧ ¬x ∈ b} = {}
⌝);
a(rewrite_tac[ℙ_thm] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ℙ_split_thm1⦎ = save_thm ( "ℙ_split_thm1", (
set_goal([], ⌜∀a b⦁ b ⊆ a ⇒
	ℙ a = ℙ b ∪ {c | c ⊆ a ∧ ∃x⦁ x ∈ c ∧ ¬x ∈ b}
∧	ℙ b ∩ {c | c ⊆ a ∧ ∃x⦁ x ∈ c ∧ ¬x ∈ b} = {}
⌝);
a(rewrite_tac[ℙ_thm] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ℙ_finite_size_thm⦎ = save_thm ( "ℙ_finite_size_thm", (
set_goal([], ⌜∀a⦁
	 a ∈ Finite
⇒	ℙ a ∈ Finite ∧ #(ℙ a) = 2 ^ #a⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(rewrite_tac[ℙ_thm] THEN finite_induction_tac⌜a⌝);
(* *** Goal "1" *** *)
a(LEMMA_T⌜{b|b ⊆ {}} = {{}}⌝ rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(rewrite_tac[size_empty_thm, ℕ_exp_def,
	size_singleton_thm, singleton_finite_thm]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(rewrite_tac[ℕ_exp_def]);
a(LEMMA_T⌜{b|b ⊆ {x} ∪ a} =
	{b|b ⊆ a} ∪ {c|∃b⦁b ⊆ a ∧ c = {x} ∪ b}⌝
	rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(∃_tac⌜x' ∩ a⌝ THEN PC_T1 "sets_ext1" asm_prove_tac[]);
a(spec_nth_asm_tac 3 ⌜x''⌝ THEN all_var_elim_asm_tac);
(* *** Goal "2.1.2" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2.1.3" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
a(spec_nth_asm_tac 3 ⌜x''⌝);
a(spec_nth_asm_tac 5 ⌜x''⌝);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜
	{c|∃ b⦁ b ⊆ a ∧ c = {x} ∪ b} ∈ Finite ∧
	#{c|∃ b⦁ b ⊆ a ∧ c = {x} ∪ b} = #{b|b ⊆ a}⌝
	THEN1 bc_thm_tac bijection_finite_size_thm);
(* *** Goal "2.2.1" *** *)
a(∃_tac⌜λb⦁{x} ∪ b⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.2.1.1" *** *)
a(swap_nth_asm_concl_tac 2 THEN strip_tac);
a(∃_tac⌜x''⌝ THEN PC_T1 "sets_ext1" asm_rewrite_tac[]);
a(contr_tac THEN all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
(* *** Goal "2.2.1.2" *** *)
a(swap_nth_asm_concl_tac 2 THEN strip_tac);
a(∃_tac⌜x''⌝ THEN PC_T1 "sets_ext1" asm_rewrite_tac[]);
a(contr_tac THEN all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(asm_rewrite_tac[∪_finite_thm]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜{b|b ⊆ a} ∩ {c|∃ b⦁ b ⊆ a ∧ c = {x} ∪ b} = {}⌝);
(* *** Goal "2.2.2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜x⌝);
a(spec_nth_asm_tac 2 ⌜x⌝);
(* *** Goal "2.2.2.2" *** *)
a(ante_tac(list_∀_elim[⌜{b|b ⊆ a}⌝,
	⌜{c|∃ b⦁ b ⊆ a ∧ c = {x} ∪ b}⌝]
	size_∪_thm));
a(asm_rewrite_tac[size_empty_thm]);
a(STRIP_T rewrite_thm_tac);
a(PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏×_finite_size_thm⦎ = save_thm ( "×_finite_size_thm", (
set_goal([], ⌜∀a b⦁
	a ∈ Finite ∧ b ∈ Finite
⇒	(a × b) ∈ Finite ∧ #(a × b) = #a * #b
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(finite_induction_tac⌜a⌝);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜({} × b) = {}⌝
	(fn th => rewrite_tac[th, empty_finite_thm, size_empty_thm]));
a(PC_T1 "sets_ext1" prove_tac[×_def]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜({x} ∪ a × b) = ({x} × b) ∪ (a × b)⌝
	(fn th => asm_rewrite_tac[th, ∪_finite_thm])
	THEN1 PC_T1 "sets_ext1" prove_tac[×_def]);
a(lemma_tac⌜({x} × b) ∩ (a × b) = {}⌝
	THEN1 (PC_T1 "sets_ext1" asm_prove_tac[×_def]
		THEN contr_tac THEN all_var_elim_asm_tac1));
a(lemma_tac⌜({x} × b) ∈ Finite ∧ #({x} × b) = #b⌝);
(* *** Goal "2.1" *** *)
a(bc_thm_tac bijection_finite_size_thm);
a(∃_tac⌜λy⦁ (x, y)⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" rewrite_tac[×_def]);
a(rewrite_tac[]);
a(contr_tac THEN_TRY all_var_elim_asm_tac);
a(spec_nth_asm_tac 1 ⌜x2⌝);
(* *** Goal "2.2" *** *)
a(REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(ante_tac(list_∀_elim[⌜{x} × b⌝, ⌜a × b⌝] size_∪_thm));
a(asm_rewrite_tac[size_empty_thm, times_plus_distrib_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_size_thm⦎ = save_thm ( "ind_sum_size_thm", (
set_goal([], ⌜∀A⦁
	A ∈ Finite
⇒	Σ A (λx⦁ℕℝ 1) = ℕℝ (#A)⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_sum_def, size_empty_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_def, size_singleton_∪_thm]);
a(asm_rewrite_tac[ℕℝ_plus_homomorphism_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_plus_thm⦎ = save_thm ( "ind_sum_plus_thm", (
set_goal([], ⌜∀A f g⦁
	A ∈ Finite
⇒	Σ A (λx⦁f x + g x) = Σ A f + Σ A g⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_sum_def]);
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_minus_thm⦎ = save_thm ( "ind_sum_minus_thm", (
set_goal([], ⌜∀A f⦁
	A ∈ Finite
⇒	Σ A (λx⦁~(f x)) = ~(Σ A f)⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_sum_def]);
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_const_times_thm⦎ = save_thm ( "ind_sum_const_times_thm", (
set_goal([], ⌜∀A f c⦁
	A ∈ Finite
⇒	Σ A (λx⦁c*(f x)) = c*(Σ A f)⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_sum_def]);
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_0_thm⦎ = save_thm ( "ind_sum_0_thm", (
set_goal([], ⌜∀A f⦁
	A ∈ Finite
⇒	Σ A  (λ x⦁ ℕℝ 0) = ℕℝ 0⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_sum_def]);
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_diff_0_thm⦎ = save_thm ( "ind_sum_diff_0_thm", (
set_goal([], ⌜∀A f g⦁
	A ∈ Finite
∧	Σ A (λx⦁f x - g x) = ℕℝ 0
⇒	Σ A f = Σ A g⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(LEMMA_T ⌜f = λx⦁(λx⦁ f x + ~(g x)) x + g x⌝ pure_once_rewrite_thm_tac
	THEN1 rewrite_tac[ℝ_plus_assoc_thm]);
a(ALL_FC_T pure_rewrite_tac[ind_sum_plus_thm]);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_local_thm⦎ = save_thm ( "ind_sum_local_thm", (
set_goal([], ⌜∀A f g⦁
	A ∈ Finite
∧ 	(∀x⦁x ∈ A ⇒ f x = g x)
⇒	Σ A f = Σ A g⌝);
a(REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜f⌝, ⌜f⌝));
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_sum_def]);
a(REPEAT strip_tac);
a(lemma_tac⌜∀ x⦁ x ∈ A ⇒ f x = g x⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
a(ALL_ASM_FC_T rewrite_tac[ind_sum_def]);
a(spec_nth_asm_tac 2 ⌜x⌝);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_0_bc_thm⦎ = save_thm ( "ind_sum_0_bc_thm", (
set_goal([], ⌜∀A f⦁
	A ∈ Finite
∧	(∀x⦁x ∈ A ⇒ f x = ℕℝ 0)
⇒	Σ A f = ℕℝ 0⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜Σ A (λJ⦁ ℕℝ 0) = ℕℝ 0⌝
	(pure_once_rewrite_thm_tac o eq_sym_rule)
	THEN1 (bc_thm_tac ind_sum_0_thm
		THEN REPEAT strip_tac));
a(bc_thm_tac ind_sum_local_thm);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏bijection_ind_sum_thm⦎ = save_thm ( "bijection_ind_sum_thm", (
set_goal([], ⌜∀A f b⦁
	 A ∈ Finite
∧	(∀x y⦁x ∈ A ∧ y ∈ A ∧ b x = b y ⇒ x = y)
⇒	Σ {z | ∃x⦁x ∈ A ∧ z = b x} f = Σ A (λx⦁f(b x))⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(intro_∀_tac(⌜b⌝, ⌜b⌝) THEN finite_induction_tac⌜A⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[ind_sum_def,
	pc_rule1"sets_ext1" prove_rule[]⌜{x|F} = {}⌝]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜∀ x y⦁ x ∈ A ∧ y ∈ A ∧ b x = b y ⇒ x = y⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
a(lemma_tac⌜∃B⦁ B = {z|∃ x'⦁ x' ∈ A ∧ z = b x'}⌝
	THEN1 prove_∃_tac);
a(all_fc_tac[bijection_finite_size_thm]);
a(all_var_elim_asm_tac1);
a(PC_T1 "predicates" lemma_tac⌜
	¬b x ∈ {z|∃ x'⦁ x' ∈ A ∧ z = b x'} ∧
	{z|∃ x'⦁ x' ∈ {x} ∪ A ∧ z = b x'} =
	{b x} ∪ {z|∃ x'⦁ x' ∈ A ∧ z = b x'}⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(cases_tac⌜x' = x⌝ THEN1 asm_rewrite_tac[]);
a(swap_nth_asm_concl_tac 1 THEN DROP_NTH_ASM_T 6 bc_thm_tac);
a(PC_T1 "sets_ext1" asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(DROP_ASMS_T discard_tac THEN PC_T1 "sets_ext1" rewrite_tac[]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "2.2.1" *** *)
a(∃_tac⌜x''⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.3" *** *)
a(∃_tac⌜x''⌝ THEN REPEAT strip_tac);
(* *** Goal "2.3" *** *)
a(POP_ASM_T rewrite_thm_tac);
a(ALL_FC_T rewrite_tac[ind_sum_def]);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_χ_singleton_thm⦎ = save_thm ( "ind_sum_χ_singleton_thm", (
set_goal([], ⌜∀A x⦁
	A ∈ Finite
⇒	Σ A (χ{x}) =
	if x ∈ A then ℕℝ 1 else ℕℝ 0⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_sum_def]);
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
a(PC_T1 "sets_ext1" asm_rewrite_tac[χ_def]);
a(cases_tac⌜x' = x⌝ THEN1 all_var_elim_asm_tac
	THEN asm_rewrite_tac[]);
a(POP_ASM_T (rewrite_thm_tac o conv_rule(RAND_C eq_sym_conv)));
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_singleton_thm⦎ = save_thm ( "ind_sum_singleton_thm", (
set_goal([], ⌜∀x f⦁
	Σ {x} f = f x⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule [] ⌜{x} = {x} ∪ {}⌝]);
a(lemma_tac⌜{} ∈ Finite⌝ THEN1 rewrite_tac[empty_finite_thm]);
a(LEMMA_T⌜¬x ∈ {}⌝ asm_tac THEN1 rewrite_tac[]);
a(ALL_FC_T pure_rewrite_tac[ind_sum_def]);
a(rewrite_tac[ind_sum_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏fin_supp_induction_thm1⦎ = save_thm ( "fin_supp_induction_thm1", (
set_goal([], ⌜∀p⦁
	(∀x⦁p(χ{x}))
∧	(∀f c⦁	{x | ¬f x = ℕℝ 0} ∈ Finite
	∧	p f
	⇒	p (λx⦁c*(f x)))
∧	(∀f g⦁	{x | ¬f x = ℕℝ 0} ∈ Finite
	∧	{x | ¬g x = ℕℝ 0} ∈ Finite
	∧	p f ∧ p g
	⇒	p (λx⦁f x + g x))
⇒	(∀f⦁	{x | ¬f x = ℕℝ 0} ∈ Finite
	⇒	p f)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃A⦁ A = {x|¬ f x = ℕℝ 0}⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜A ∈ Finite⌝
	THEN1 asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 3 discard_tac);
a(DROP_NTH_ASM_T 2 ante_tac);
a(intro_∀_tac(⌜f⌝, ⌜f⌝) THEN finite_induction_tac ⌜A⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T⌜f = λx⦁ℕℝ 0 * (χ{a} x)⌝ pure_rewrite_thm_tac);
(* *** Goal "1.1" *** *)
a(rewrite_tac[] THEN POP_ASM_T ante_tac);
a(PC_T1 "sets_ext" rewrite_tac[] THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN POP_ASM_T discard_tac
	THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜{x|¬ χ {a} x = ℕℝ 0} = {a}⌝
	(fn th => rewrite_tac[th, singleton_finite_thm]));
a(PC_T1 "sets_ext1" rewrite_tac[χ_def] THEN strip_tac);
a(cases_tac⌜x = a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜f = λx⦁
	(λz⦁if z ∈ A then f z else ℕℝ 0) x +
	(λz⦁if z ∈ A then ℕℝ 0 else f z) x⌝
	pure_once_rewrite_thm_tac
	THEN1 (rewrite_tac[] THEN REPEAT strip_tac
		THEN cases_tac⌜x' ∈ A⌝
		THEN asm_rewrite_tac[]));
a(DROP_NTH_ASM_T 5 bc_thm_tac);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜A⌝
	THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{x}⌝
	THEN PC_T1 "sets_ext1" rewrite_tac[singleton_finite_thm]
	THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN
	cases_tac⌜x' ∈ A⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 2 ante_tac);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜x'⌝);
(* *** Goal "2.3" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT ∀_tac);
a(cases_tac⌜x' ∈ A⌝ THEN asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [2] (PC_T1 "sets_ext" all_fc_tac));
(* *** Goal "2.4" *** *)
a(LEMMA_T⌜(λ z⦁ if z ∈ A then ℕℝ 0 else f z) =
	(λz⦁f x * χ{x} z)⌝
	rewrite_thm_tac);
(* *** Goal "2.4.1" *** *)
a(rewrite_tac[χ_def] THEN REPEAT strip_tac);
a(cases_tac⌜x' = x⌝
	THEN1 all_var_elim_asm_tac1 THEN asm_rewrite_tac[]);
a(cases_tac⌜x' ∈ A⌝ THEN asm_rewrite_tac[]);
a(contr_tac THEN LEMMA_T⌜x' ∈ {x} ∪ A⌝ ante_tac
	THEN1 asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2.4.2" *** *)
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜{x'|¬ χ {x} x' = ℕℝ 0} = {x}⌝
	(fn th => rewrite_tac[th, singleton_finite_thm]));
a(PC_T1 "sets_ext" rewrite_tac[χ_def] THEN ∀_tac);
a(cases_tac⌜x' = x⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏fin_supp_induction_thm⦎ = save_thm ( "fin_supp_induction_thm", (
set_goal([], ⌜∀p⦁
	(∀x⦁p(χ{x}))
∧	(∀f c⦁	Supp f ∈ Finite
	∧	p f
	⇒	p (λx⦁c*(f x)))
∧	(∀f g⦁	Supp f ∈ Finite
	∧	Supp g ∈ Finite
	∧	p f ∧ p g
	⇒	p (λx⦁f x + g x))
⇒	(∀f⦁	Supp f ∈ Finite
	⇒	p f)
⌝);
a(rewrite_tac[supp_def, fin_supp_induction_thm1]);
pop_thm()
));

=TEX
=SML
val ⦏supp_clauses⦎ = save_thm ( "supp_clauses", (
set_goal([], ⌜
	Supp (λx:'a⦁ ℕℝ 0) = {}
∧	(∀f:'a → ℝ⦁ Supp (λx⦁~(f x)) = Supp f)
∧	(∀f g:'a → ℝ⦁ Supp (λx⦁ f x + g x) ⊆ Supp f ∪ Supp g)
∧	(∀c:ℝ; f:'a → ℝ⦁ Supp (λx⦁ c*f x) ⊆ Supp f)
⌝);
a(PC_T1 "sets_ext1" rewrite_tac[supp_def] THEN REPEAT strip_tac
	THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀A⦁ ⋃{A} = A⌝);
a(PC_T "sets_ext1" contr_tac THEN1 all_asm_fc_tac[]);
a(spec_nth_asm_tac 1 ⌜A⌝ THEN all_var_elim_asm_tac1);
val ⋃_singleton_thm = pop_thm ();
=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_∪_thm⦎ = save_thm ( "ind_sum_∪_thm", (
set_goal([], ⌜∀A B f⦁
	A ∈ Finite
∧	B ∈ Finite
⇒	Σ (A ∪ B) f =
	Σ A f + Σ B f - Σ (A ∩ B) f
⌝);
a(REPEAT strip_tac);
a(finite_induction_tac ⌜A⌝ THEN1 rewrite_tac[ind_sum_def]);
a(lemma_tac⌜A ∪ B ∈ Finite ∧ A ∩ B ∈ Finite⌝
	THEN1 (asm_rewrite_tac[∪_finite_thm]
		THEN ALL_FC_T rewrite_tac[∩_finite_thm]));
a(cases_tac⌜{x} ⊆ B⌝);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b c⦁ a ⊆ c ⇒ 
		(a ∪ b) ∪ c = b ∪ c
	∧	(a ∪ b) ∩ c = a ∪ (b ∩ c)⌝]);
a(LEMMA_T⌜¬x ∈ A ∩ B⌝ asm_tac THEN1 REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[ind_sum_def]);
a(DROP_NTH_ASM_T 6 ante_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T (PC_T1 "sets_ext" strip_asm_tac)
	THEN all_var_elim_asm_tac);
a(ALL_FC_T rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b c⦁ ¬x ∈ c ⇒ 
		(a ∪ b) ∪ c = a ∪ b ∪ c
	∧	({x} ∪ b) ∩ c = (b ∩ c)⌝]);
a(LEMMA_T⌜¬x ∈ A ∪ B⌝ asm_tac THEN1 REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[ind_sum_def]);
a(DROP_NTH_ASM_T 6 ante_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_ℙ_thm⦎ = save_thm ( "ind_sum_ℙ_thm", (
set_goal([], ⌜∀K⦁
	K ∈ Finite ∧ ¬K = {}
⇒	Σ (ℙK) (λJ⦁ ~(ℕℝ 1) ^ #J) = ℕℝ 0⌝);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(LEMMA_T⌜ℙK ∈ Finite⌝ ante_tac THEN1
	all_fc_tac[ℙ_finite_size_thm]);
a(strip_asm_tac (list_∀_elim[⌜x⌝, ⌜K⌝]ℙ_split_thm));
a(DROP_NTH_ASM_T 2 rewrite_thm_tac);
a(rewrite_tac[∪_finite_thm] THEN strip_tac);
a(ALL_FC_T asm_rewrite_tac[ind_sum_∪_thm]);
a(rewrite_tac[ind_sum_def]);
a(lemma_tac⌜∃g⦁∀J⦁g J = J \ {x}⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜ ∀ X Y⦁ X ∈ {b|b ⊆ K ∧ x ∈ b}
	∧ Y ∈ {b|b ⊆ K ∧ x ∈ b}
	∧ g X = g Y ⇒ X = Y⌝);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[] THEN DROP_ASMS_T discard_tac
	THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(cases_tac⌜x' = x⌝ THEN1 asm_rewrite_tac[]);
a(spec_nth_asm_tac 3 ⌜x'⌝);
(* *** Goal "1.2" *** *)
a(cases_tac⌜x' = x⌝ THEN1 asm_rewrite_tac[]);
a(spec_nth_asm_tac 3 ⌜x'⌝);
(* *** Goal "2" *** *)
a(ante_tac(list_∀_elim[	⌜{b|b ⊆ K ∧ x ∈ b}⌝,
		⌜λ J: 'a SET⦁ ~ (ℕℝ 1) ^ # J⌝,
		⌜g⌝] bijection_ind_sum_thm));
a(asm_rewrite_tac[∪_finite_thm, singleton_finite_thm]);
a(LEMMA_T ⌜
	{z|∃ x'⦁ (x' ⊆ K ∧ x ∈ x') ∧ z = x' \ {x}} =
	{b|b ⊆ K ∧ ¬x ∈ b}⌝ rewrite_thm_tac);
(* *** Goal ".1" *** *)
a(DROP_ASM_T ⌜x ∈ K⌝ ante_tac
	THEN DROP_ASMS_T discard_tac
	THEN PC_T1 "sets_ext1" rewrite_tac[]
	THEN REPEAT strip_tac
	THEN_TRY SOLVED_T (asm_prove_tac[]));
a(∃_tac⌜{x} ∪ x'⌝ THEN PC_T1 "sets_ext1" asm_prove_tac[]);
a(contr_tac THEN all_var_elim_asm_tac);
(* *** Goal "2.2" *** *)
a(STRIP_T rewrite_thm_tac THEN rename_tac[]);
a(LEMMA_T⌜
	Σ {b|b ⊆ K ∧ x ∈ b} (λ x'⦁ ~ (ℕℝ 1) ^ # (x' \ {x})) =
	Σ {b|b ⊆ K ∧ x ∈ b} (λK⦁~((λ J⦁ ~ (ℕℝ 1) ^ # J) K))⌝
	pure_rewrite_thm_tac);
(* *** Goal "2.2.1" *** *)
a(bc_thm_tac ind_sum_local_thm THEN REPEAT strip_tac);
a(LEMMA_T ⌜#x' = #(x' \{x}) + 1⌝
	(fn th => rewrite_tac[th, ℝ_ℕ_exp_def]
		THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(LEMMA_T⌜x' = {x} ∪ (x' \ {x})⌝
	(fn th => conv_tac (LEFT_C(once_rewrite_conv[th])))
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "sets_ext" prove_tac[]));
a(LEMMA_T⌜¬x ∈ x' \ {x}⌝ asm_tac
	THEN1 PC_T1 "sets_ext" prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(lemma_tac⌜x' \ {x} ⊆ x'⌝ 
	THEN1 PC_T1 "sets_ext" prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(all_fc_tac[size_singleton_∪_thm]);
(* *** Goal "2.2.2" *** *)
a(ALL_FC_T rewrite_tac[ind_sum_minus_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_⋃_finite_thm⦎ = save_thm ( "ind_⋃_finite_thm", (
set_goal([], ⌜∀I U A f⦁
	I ∈ Finite
∧	(∀i⦁ i ∈ I ⇒ U i ∈ Finite)
∧	A = ⋃{B | ∃i⦁ i ∈ I ∧ B = U i}
⇒	A ∈ Finite⌝);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac);
a(finite_induction_tac⌜I⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜⋃{B|F} = {}⌝]);
a(REPEAT strip_tac THEN asm_rewrite_tac[empty_finite_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(REPEAT strip_tac);
a(LEMMA_T ⌜{B|∃ i⦁ i ∈ {x} ∪ I ∧ B = U i} =
	{B|∃ i⦁ i ∈ I ∧ B = U i} ∪ {U x}⌝ rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(asm_rewrite_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀V W⦁⋃(V ∪ W) = ⋃V ∪ ⋃W⌝,
	⋃_singleton_thm,
	∪_finite_thm]);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀I U A x⦁
	I ∈ Finite ∧ ¬I = {}
∧	(∀i⦁ i ∈ I ⇒ U i ∈ Finite)
∧	A = ⋃{B | ∃i⦁ i ∈ I ∧ B = U i}
⇒	Σ
	(ℙI)
	(λJ⦁ ~(ℕℝ 1) ^ #J * Σ (A ∩ ⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) (χ{x}))
	= ℕℝ 0⌝);
a(REPEAT strip_tac);
a(all_fc_tac[ind_⋃_finite_thm]);
a(lemma_tac⌜ℙI ∈ Finite⌝
	THEN1 all_fc_tac[ ℙ_finite_size_thm ]);
a(cases_tac⌜¬x ∈ A⌝);
(* *** Goal "1" *** *)
a(bc_thm_tac ind_sum_0_bc_thm);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(LEMMA_T⌜Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ x' ∧ B = U j}) (χ {x}) = ℕℝ 0⌝
	rewrite_thm_tac);
a(bc_thm_tac ind_sum_0_bc_thm);
a(ALL_FC_T rewrite_tac[∩_finite_thm]);
a(REPEAT strip_tac THEN rewrite_tac[χ_def]);
a(cases_tac⌜x'' = x⌝ THEN asm_rewrite_tac[]
	THEN1 all_var_elim_asm_tac);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 4 (strip_asm_tac o eq_sym_rule));
a(lemma_tac ⌜x ∈ ⋃ {B|∃ i⦁ i ∈ I ∧ B = U i}⌝
	THEN1 asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(var_elim_nth_asm_tac 1);
a(lemma_tac⌜¬{j | j ∈ I ∧ x ∈ U j} = {} ∧
	{j | j ∈ I ∧ x ∈ U j} ⊆ I⌝
	THEN1 PC_T1 "sets_ext" asm_prove_tac[]);
a(GET_ASM_T ⌜ℙI ∈ Finite⌝ ante_tac);
a(ALL_FC_T (MAP_EVERY ante_tac) [ℙ_split_thm1]);
a(rewrite_tac[] THEN strip_tac);
a(STRIP_T rewrite_thm_tac);
a(rewrite_tac[∪_finite_thm] THEN REPEAT strip_tac);
a(ALL_FC_T asm_rewrite_tac[ind_sum_∪_thm]);
a(rewrite_tac[ind_sum_def]);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y⦁ y = ℕℝ 0 ∧ x = ℕℝ 0 ⇒ x + y = ℕℝ 0⌝)
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac ind_sum_0_bc_thm);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(LIST_DROP_NTH_ASM_T [3] (PC_T1 "sets_ext" all_fc_tac));
(* *** Goal "2.1.2" *** *)
a(LEMMA_T⌜Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ x' ∧ B = U j}) (χ {x}) = ℕℝ 0⌝
	rewrite_thm_tac);
a(bc_thm_tac ind_sum_0_bc_thm);
a(ALL_FC_T rewrite_tac[∩_finite_thm]);
a(REPEAT strip_tac THEN rewrite_tac[χ_def]);
a(cases_tac⌜x''' = x⌝ THEN asm_rewrite_tac[]
	THEN1 all_var_elim_asm_tac);
a(POP_ASM_T (ante_tac o ∀_elim⌜U x''⌝));
a(asm_rewrite_tac[]);
a(∃_tac⌜x''⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜{j|j ∈ I ∧ x ∈ U j} ∈ Finite⌝
	THEN1 all_fc_tac[⊆_finite_thm]);
a(DROP_NTH_ASM_T 14 discard_tac
	THEN all_fc_tac[ind_sum_ℙ_thm]);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac ind_sum_local_thm THEN REPEAT strip_tac);
a(LEMMA_T⌜Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ x' ∧ B = U j}) (χ {x}) = ℕℝ 1⌝
	rewrite_thm_tac);
a(lemma_tac⌜A ∩ ⋂ {B|∃ j⦁ j ∈ x' ∧ B = U j} ∈ Finite⌝
	THEN1 ALL_FC_T rewrite_tac[∩_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_χ_singleton_thm]);
a(LEMMA_T ⌜x ∈ A ∩ ⋂ {B|∃ j⦁ j ∈ x' ∧ B = U j}⌝
	rewrite_thm_tac);
a(rename_tac[(⌜x'⌝, "J")] THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [3] (PC_T1 "sets_ext" all_fc_tac));
val ⦏ind_sum_inc_exc_lemma1⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀I U A f c⦁
	I ∈ Finite ∧ ¬I = {}
∧	(∀i⦁ i ∈ I ⇒ U i ∈ Finite)
∧	A = ⋃{B | ∃i⦁ i ∈ I ∧ B = U i}
∧	Σ
	(ℙI)
	(λJ⦁ ~(ℕℝ 1) ^ #J * Σ (A ∩ ⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) f) = ℕℝ 0
⇒	Σ
	(ℙI)
	(λJ⦁ ~(ℕℝ 1) ^ #J * Σ (A ∩ ⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) (λx⦁c*f x)) = ℕℝ 0
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[ind_⋃_finite_thm]);
a(lemma_tac⌜ℙI ∈ Finite⌝
	THEN1 all_fc_tac[ ℙ_finite_size_thm ]);
a(LEMMA_T ⌜Σ (ℙ I)
	(λ J⦁ ~ (ℕℝ 1) ^ # J * Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) (λ x⦁ c * f x)) =
	c * Σ (ℙ I) (λ J⦁ ~ (ℕℝ 1) ^ # J * Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) f)⌝
	asm_rewrite_thm_tac);
a(ALL_FC_T rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv)
	ind_sum_const_times_thm]);
a(bc_thm_tac ind_sum_local_thm);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac⌜(A ∩ ⋂ {B|∃ j⦁ j ∈ x ∧ B = U j}) ∈ Finite⌝
	THEN1 ALL_FC_T rewrite_tac[∩_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_const_times_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
val ⦏ind_sum_inc_exc_lemma2⦎ = pop_thm ();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀I U A f g⦁
	I ∈ Finite ∧ ¬I = {}
∧	(∀i⦁ i ∈ I ⇒ U i ∈ Finite)
∧	A = ⋃{B | ∃i⦁ i ∈ I ∧ B = U i}
∧	Σ
	(ℙI)
	(λJ⦁ ~(ℕℝ 1) ^ #J * Σ (A ∩ ⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) f) = ℕℝ 0
∧	Σ
	(ℙI)
	(λJ⦁ ~(ℕℝ 1) ^ #J * Σ (A ∩ ⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) g) = ℕℝ 0
⇒	Σ
	(ℙI)
	(λJ⦁ ~(ℕℝ 1) ^ #J * Σ (A ∩ ⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) (λx⦁f x + g x)) = ℕℝ 0
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[ind_⋃_finite_thm]);
a(lemma_tac⌜ℙI ∈ Finite⌝
	THEN1 all_fc_tac[ ℙ_finite_size_thm ]);
a(LEMMA_T ⌜Σ (ℙ I)
	(λ J⦁ ~ (ℕℝ 1) ^ # J * Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) (λ x⦁ f x + g x)) =
	Σ (ℙ I) (λ J⦁ ~ (ℕℝ 1) ^ # J * Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) f) + 
	Σ (ℙ I) (λ J⦁ ~ (ℕℝ 1) ^ # J * Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) g)⌝
	asm_rewrite_thm_tac);
a(ALL_FC_T rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv)
	ind_sum_plus_thm]);
a(bc_thm_tac ind_sum_local_thm);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac⌜(A ∩ ⋂ {B|∃ j⦁ j ∈ x ∧ B = U j}) ∈ Finite⌝
	THEN1 ALL_FC_T rewrite_tac[∩_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_plus_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
val ⦏ind_sum_inc_exc_lemma3⦎ = pop_thm ();
=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_inc_exc_sym_thm⦎ = save_thm ( "ind_sum_inc_exc_sym_thm", (
set_goal([], ⌜∀I U A f⦁
	I ∈ Finite ∧ ¬I = {}
∧	(∀i⦁ i ∈ I ⇒ U i ∈ Finite)
∧	A = ⋃{B | ∃i⦁ i ∈ I ∧ B = U i}
⇒	Σ
	(ℙI)
	(λJ⦁ ~(ℕℝ 1) ^ #J * Σ (A ∩ ⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) f) = ℕℝ 0
⌝);
a(REPEAT strip_tac);
a(ante_tac(∀_elim⌜λf⦁Σ (ℙI)
	(λJ⦁ ~(ℕℝ 1) ^ #J * Σ (A ∩ ⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) f) = ℕℝ 0⌝
	fin_supp_induction_thm1));
a(rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(swap_nth_asm_concl_tac 1);
a(ALL_FC_T rewrite_tac[ind_sum_inc_exc_lemma1]);
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 1);
a(ALL_FC_T rewrite_tac[ind_sum_inc_exc_lemma2]);
(* *** Goal "3" *** *)
a(swap_nth_asm_concl_tac 1);
a(ALL_FC_T rewrite_tac[ind_sum_inc_exc_lemma3]);
(* *** Goal "4" *** *)
a(LEMMA_T ⌜
	Σ (ℙ I) (λ J⦁ ~ (ℕℝ 1) ^ # J * Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ J ∧ B = U j})
	(λx⦁if x ∈ A then f x else ℕℝ 0)) = ℕℝ 0⌝
	(once_rewrite_thm_tac o eq_sym_rule));
(* *** Goal "4.1" *** *)
a(POP_ASM_T bc_thm_tac);
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜A⌝);
a(all_fc_tac[ind_⋃_finite_thm]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "4.2" *** *)
a(lemma_tac⌜ℙI ∈ Finite⌝
	THEN1 all_fc_tac[ ℙ_finite_size_thm ]);
a(all_fc_tac[ind_⋃_finite_thm]);
a(bc_thm_tac ind_sum_local_thm THEN REPEAT strip_tac
	THEN rewrite_tac[]);
a(LEMMA_T⌜Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ x ∧ B = U j}) f =
	Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ x ∧ B = U j})
	(λ x⦁ if x ∈ A then f x else ℕℝ 0)⌝
	rewrite_thm_tac);
a(bc_thm_tac ind_sum_local_thm);
a(all_fc_tac[ind_⋃_finite_thm]);
a(ALL_FC_T rewrite_tac[∩_finite_thm]);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ind_sum_inc_exc_thm⦎ = save_thm ( "ind_sum_inc_exc_thm", (
set_goal([], ⌜∀I U A f⦁
	I ∈ Finite ∧ ¬I = {}
∧	(∀i⦁ i ∈ I ⇒ U i ∈ Finite)
∧	A = ⋃{B | ∃i⦁ i ∈ I ∧ B = U i}
⇒	Σ A f =
	Σ
	(ℙI \ {{}})
	(λJ⦁ ~(ℕℝ 1) ^ (#J + 1) * Σ (⋂{B | ∃j⦁ j ∈ J ∧ B = U j}) f)
⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜A ∈ Finite⌝
	THEN all_fc_tac[ind_⋃_finite_thm]);
a(lemma_tac⌜ℙI ∈ Finite⌝
	THEN1 all_fc_tac[ ℙ_finite_size_thm ]);
a(lemma_tac⌜ℙI \ {{}} ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜ℙI⌝ THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext" prove_tac[]));
a(LEMMA_T⌜(λ J⦁ ~ (ℕℝ 1) ^ (# J + 1) * Σ (⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) f) =
	(λ J⦁ ~(ℕℝ 1) * (λJ⦁ ~ (ℕℝ 1) ^ # J * Σ (⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) f) J)⌝
	pure_rewrite_thm_tac
	THEN1 (rewrite_tac[ℝ_ℕ_exp_def]
		THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(ALL_FC_T pure_rewrite_tac[ind_sum_const_times_thm]);
a(LEMMA_T ⌜ Σ (ℙ I \ {{}})
	(λ J⦁ ~ (ℕℝ 1) ^ # J * Σ (⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) f) =
	Σ (ℙ I \ {{}})
	(λ J⦁ ~ (ℕℝ 1) ^ # J * Σ (A ∩ ⋂ {B|∃ j⦁ j ∈ J ∧ B = U j}) f)⌝
	rewrite_thm_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ind_sum_local_thm);
a(REPEAT strip_tac THEN rewrite_tac[]);
a(LEMMA_T ⌜A ∩ ⋂ {B|∃ j⦁ j ∈ x ∧ B = U j} =
	⋂ {B|∃ j⦁ j ∈ x ∧ B = U j}⌝
	rewrite_thm_tac);
a(bc_thm_tac (pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b⦁b ⊆ a ⇒ a ∩ b = b⌝));
a(all_var_elim_asm_tac1);
a(PC_T "sets_ext" strip_tac THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (PC_T1 "sets_ext" strip_asm_tac));
a(spec_nth_asm_tac 2 ⌜U x''⌝);
(* *** Goal "1.1" *** *)
a(spec_nth_asm_tac 1 ⌜x''⌝);
(* *** Goal "1.2" *** *)
a(∃_tac ⌜U x''⌝ THEN REPEAT strip_tac);
a(∃_tac ⌜x''⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] (PC_T1 "sets_ext1" all_fc_tac));
(* *** Goal "2" *** *)
a(all_fc_tac[ind_sum_inc_exc_sym_thm]);
a(POP_ASM_T (ante_tac o ∀_elim⌜f⌝));
a(LEMMA_T⌜{} ∈ ℙI⌝ asm_tac THEN1 rewrite_tac[]);
a(ALL_FC_T (fn ths => conv_tac (LEFT_C(once_rewrite_conv ths)))
	[pc_rule1 "sets_ext" prove_rule[]
	⌜∀a x⦁x ∈ a ⇒ a = (a \ {x}) ∪ {x}⌝]);
a(lemma_tac⌜{{}} ∈ Finite⌝ THEN1 rewrite_tac[singleton_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_∪_thm]);
a(rewrite_tac[ind_sum_def,
	ind_sum_singleton_thm,
	size_empty_thm,
	pc_rule1 "sets_ext" prove_rule[]
	⌜⋂{B|F} = Universe ∧ ∀a b⦁(a \ b) ∩ b = {}⌝]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏size_inc_exc_thm⦎ = save_thm ( "size_inc_exc_thm", (
set_goal([], ⌜∀I U A⦁
	I ∈ Finite ∧ ¬I = {}
∧	(∀i⦁ i ∈ I ⇒ U i ∈ Finite)
∧	A = ⋃{B | ∃i⦁ i ∈ I ∧ B = U i}
⇒	ℕℝ(# A) =
	Σ
	(ℙI \ {{}})
	(λJ⦁ ~(ℕℝ 1) ^ (#J + 1) * ℕℝ(# (⋂{B | ∃j⦁ j ∈ J ∧ B = U j})))
⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜A ∈ Finite⌝
	THEN all_fc_tac[ind_⋃_finite_thm]);
a(lemma_tac⌜ℙI ∈ Finite⌝
	THEN1 all_fc_tac[ ℙ_finite_size_thm ]);
a(ALL_FC_T rewrite_tac[
	conv_rule(ONCE_MAP_C eq_sym_conv) ind_sum_size_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_inc_exc_thm]);
a(bc_thm_tac ind_sum_local_thm);
a(lemma_tac⌜ℙI \ {{}} ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜ℙI⌝ THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext" prove_tac[]));
a(REPEAT strip_tac THEN rewrite_tac[]);
a(LEMMA_T ⌜⋂ {B|∃ j⦁ j ∈ x ∧ B = U j} =
	A ∩ ⋂ {B|∃ j⦁ j ∈ x ∧ B = U j}⌝
	once_rewrite_thm_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac (pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b⦁b ⊆ a ⇒ b = a ∩ b⌝));
a(all_var_elim_asm_tac1);
a(PC_T "sets_ext" strip_tac THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (PC_T1 "sets_ext" strip_asm_tac));
a(spec_nth_asm_tac 2 ⌜U x''⌝);
(* *** Goal "1.1" *** *)
a(spec_nth_asm_tac 1 ⌜x''⌝);
(* *** Goal "1.2" *** *)
a(∃_tac ⌜U x''⌝ THEN REPEAT strip_tac);
a(∃_tac ⌜x''⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] (PC_T1 "sets_ext1" all_fc_tac));
a(lemma_tac ⌜A ∩ ⋂ {B|∃ j⦁ j ∈ x ∧ B = U j} ∈ Finite⌝
	THEN1 ALL_FC_T rewrite_tac[∩_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_size_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏supp_χ_thm⦎ = save_thm ( "supp_χ_thm", (
set_goal([], ⌜∀A⦁
	Supp (χ A) = A
⌝);
a(REPEAT strip_tac THEN PC_T1 "sets_ext1" rewrite_tac[supp_def, χ_def]
	THEN ∀_tac);
a(cases_tac⌜x ∈ A⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏supp_plus_thm⦎ = save_thm ( "supp_plus_thm", (
set_goal([], ⌜∀f g⦁
	Supp (λx⦁f x + g x) =
	(Supp f ∪ Supp g) \ {x | f x = ~(g x)}
⌝);
a(REPEAT strip_tac THEN PC_T1 "sets_ext1" rewrite_tac[supp_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏ind_sum_supp_thm⦎ = save_thm ( "ind_sum_supp_thm", (
set_goal([], ⌜∀A f⦁
	A ∈ Finite
⇒	Σ A f = Σ (A ∩ Supp f) f
⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝ THEN1 rewrite_tac[ind_sum_def]);
a(cases_tac⌜x ∈ Supp f⌝);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜({x} ∪ A) ∩ Supp f = {x} ∪ (A ∩ Supp f)⌝
	rewrite_thm_tac
	THEN1 PC_T1 "sets_ext" asm_prove_tac[]);
a(LEMMA_T ⌜¬x ∈ (A ∩ Supp f)⌝ asm_tac
	THEN1 REPEAT strip_tac);
a(LEMMA_T ⌜A ∩ Supp f ∈ Finite⌝ asm_tac
	THEN1 (bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜A⌝  THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
(* *** Goal "2" *** *)
a(TOP_ASM_T (strip_asm_tac o rewrite_rule[supp_def]));
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
a(LEMMA_T ⌜({x} ∪ A) ∩ Supp f = (A ∩ Supp f)⌝
	rewrite_thm_tac
	THEN1 PC_T1 "sets_ext" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏ind_sum_transfer_thm⦎ = save_thm ( "ind_sum_transfer_thm", (
set_goal([], ⌜∀A B f g h⦁
	A ∈ Finite
∧	B ∈ Finite
∧	(∀x⦁ x ∈ A ∧ ¬f x = ℕℝ 0 ⇒ h x ∈ B ∧ f x = g(h x))
∧	(∀y⦁ y ∈ B ∧ ¬ g y = ℕℝ 0 ⇒ ∃⋎1x⦁ x ∈ A ∧ h x = y ∧ f x = g y)
⇒	Σ A f = Σ B g
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀C⦁ C ∈ Finite ⇒
	Σ {x | x ∈ A ∧ ¬f x = ℕℝ 0 ∧ h x ∈ C} f =
	Σ (B ∩ C) g⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(finite_induction_tac⌜C⌝);
(* *** Goal "1" *** *)
(* *** Goal "1.1" *** *)
a(rewrite_tac[ind_sum_def, pc_rule1 "sets_ext1" prove_rule[]⌜{x|F} = {}⌝]);
(* *** Goal "1.2" *** *)
a(cases_tac⌜x ∈ B⌝);
a(LEMMA_T⌜B ∩ ({x} ∪ C) = {x} ∪ (B ∩ C)⌝ rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(LEMMA_T⌜¬x ∈ (B ∩ C)⌝ asm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜B ∩ C ∈ Finite⌝
	THEN1 (bc_thm_tac ∩_finite_thm THEN REPEAT strip_tac));
a(cases_tac⌜g x = ℕℝ 0⌝);
(* *** Goal "1.2.1.1" *** *)
a(LEMMA_T⌜{x'|x' ∈ A ∧ ¬ f x' = ℕℝ 0 ∧ h x' ∈ {x} ∪ C}
	= {x|x ∈ A ∧ ¬ f x = ℕℝ 0 ∧ h x ∈ C}⌝
	asm_rewrite_thm_tac);
(* *** Goal "1.2.1.1.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [10] all_fc_tac);
a(swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]);
(* *** Goal "1.2.1.1.2" *** *)
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
(* *** Goal "1.2.1.2" *** *)
a(spec_nth_asm_tac 8 ⌜x⌝ THEN 
	PC_T "predicates" all_var_elim_asm_tac1);
a(LEMMA_T⌜{x''|x'' ∈ A ∧ ¬ f x'' = ℕℝ 0 ∧ h x'' ∈ {h x'} ∪ C}
	= {x'} ∪ {x|x ∈ A ∧ ¬ f x = ℕℝ 0 ∧ h x ∈ C}⌝
	asm_rewrite_thm_tac);
(* *** Goal "1.2.1.2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY all_var_elim_asm_tac1);
(* *** Goal "1.2.1.2.1.1" *** *)
a(swap_nth_asm_concl_tac 1);
a(spec_nth_asm_tac 16 ⌜x⌝);
a(DROP_NTH_ASM_T 7 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.2.1.2.1.2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "1.2.1.2.2" *** *)
a(LEMMA_T⌜¬x' ∈ {x|x ∈ A ∧ ¬ f x = ℕℝ 0 ∧ h x ∈ C}⌝
	asm_tac
	THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜{x|x ∈ A ∧ ¬ f x = ℕℝ 0 ∧ h x ∈ C} ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜A⌝ THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
(* *** Goal "1.2.2" *** *)
a(LEMMA_T⌜B ∩ ({x} ∪ C) = B ∩ C⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜{x'|x' ∈ A ∧ ¬ f x' = ℕℝ 0 ∧ h x' ∈ {x} ∪ C}
	= {x|x ∈ A ∧ ¬ f x = ℕℝ 0 ∧ h x ∈ C}⌝
	asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(spec_nth_asm_tac 8 ⌜x'⌝);
(* *** Goal "2" *** *)
a(POP_ASM_T (ante_tac o ∀_elim⌜B⌝) THEN asm_rewrite_tac[]);
a(STRIP_T (rewrite_thm_tac o eq_sym_rule));
a(LEMMA_T ⌜{x|x ∈ A ∧ ¬ f x = ℕℝ 0 ∧ h x ∈ B} =
	A ∩ Supp f⌝ rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[supp_def]
	THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a(ALL_FC_T rewrite_tac[ind_sum_supp_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏ind_sum_singleton_×_thm⦎ = save_thm ( "ind_sum_singleton_×_thm", (
set_goal([], ⌜∀x B; f:'a × 'b → ℝ⦁
	B ∈ Finite
⇒	Σ ({x} × B) f = Σ B (λy⦁f(x, y))
⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜B⌝ THEN1 rewrite_tac[ind_sum_def, ×_def,
	pc_rule1 "sets_ext1" prove_rule[]⌜{(x, y)|F} = {}⌝]);
a(LEMMA_T⌜({x} × ({x'} ∪ B)) = {(x,  x')} ∪ ({x} × B)⌝rewrite_thm_tac
	THEN1 MERGE_PCS_T1 ["'bin_rel", "'pair", "sets_ext1"] prove_tac[]);
a(LEMMA_T⌜¬(x,  x') ∈ ({x} × B)⌝ asm_tac
	THEN1 MERGE_PCS_T1 ["'bin_rel", "sets_ext1"] prove_tac[]);
a(strip_asm_tac (∀_elim⌜x⌝ singleton_finite_thm));
a(lemma_tac⌜({x} × B) ∈ Finite⌝
	THEN1 all_fc_tac[×_finite_size_thm]);
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏ind_sum_×_thm⦎ = save_thm ( "ind_sum_×_thm", (
set_goal([], ⌜∀f:'a × 'b → ℝ; A B⦁
	A ∈ Finite ∧ B ∈ Finite
⇒	Σ A (λx⦁Σ B (λy⦁f(x, y))) = Σ (A × B) f
⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝ THEN1 rewrite_tac[ind_sum_def, ×_def,
	pc_rule1 "sets_ext1" prove_rule[]⌜{(x, y)|F} = {}⌝]);
a(ALL_FC_T asm_rewrite_tac[ind_sum_def]);
a(LEMMA_T⌜(({x} ∪ A) × B) = ({x} × B) ∪ (A × B)⌝rewrite_thm_tac
	THEN1 MERGE_PCS_T1 ["'bin_rel", "'pair", "sets_ext1"] prove_tac[]);
a(strip_asm_tac (∀_elim⌜x⌝ singleton_finite_thm));
a(lemma_tac⌜({x} × B) ∈ Finite ∧ (A × B) ∈ Finite ⌝
	THEN1 ALL_FC_T rewrite_tac[×_finite_size_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_∪_thm, ind_sum_singleton_×_thm]);
a(LEMMA_T⌜({x} × B) ∩ (A × B) = {}⌝rewrite_thm_tac
	THEN1 (MERGE_PCS_T1 ["'bin_rel", "'pair", "sets_ext1"] rewrite_tac[]
		THEN contr_tac THEN all_var_elim_asm_tac1));
a(rewrite_tac[ind_sum_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏binomial_0_clauses⦎ = save_thm ( "binomial_0_clauses", (
set_goal([], ⌜∀n⦁ Binomial n 0 = 1 ∧
		Binomial 0 (n+1) = 0⌝);
a(rewrite_tac[binomial_def] THEN REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN asm_rewrite_tac[binomial_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏binomial_less_0_thm⦎ = save_thm ( "binomial_less_0_thm", (
set_goal([], ⌜∀n m⦁ n < m ⇒ Binomial n m = 0⌝);
a(∀_tac THEN induction_tac ⌜n:ℕ⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T⌜1 ≤ m⌝ (strip_asm_tac o 
	once_rewrite_rule[plus_comm_thm] o
	rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN rewrite_tac[binomial_0_clauses]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜1 ≤ m'⌝ (strip_asm_tac o 
	once_rewrite_rule[plus_comm_thm] o
	rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN rewrite_tac[binomial_def]);
a(REPEAT strip_tac THEN DROP_NTH_ASM_T 2 bc_thm_tac
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏binomial_eq_thm⦎ = save_thm ( "binomial_eq_thm", (
set_goal([], ⌜∀n⦁ Binomial n n = 1⌝);
a(∀_tac THEN induction_tac ⌜n:ℕ⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[binomial_0_clauses]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[binomial_def]);
a(bc_thm_tac binomial_less_0_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀A m⦁
	A ∈ Finite
⇒	{X | X ⊆ A ∧ #X = m} ∈ Finite
⌝);
a(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm);
a(∃_tac⌜ℙA⌝ THEN1 ALL_FC_T rewrite_tac[ℙ_finite_size_thm]);
a(PC_T1 "sets_ext"prove_tac[]);
val ⦏combinations_finite_lemma⦎ = pop_thm ();
=TEX
%%%%
%%%%
=SML
val ⦏combinations_finite_size_thm⦎ = save_thm ( "combinations_finite_size_thm", (
set_goal([], ⌜∀A n m⦁
	A ∈ Finite
∧	#A = n
⇒	{X | X ⊆ A ∧ #X = m} ∈ Finite
∧	#{X | X ⊆ A ∧ #X = m} = Binomial n m
⌝);
a(REPEAT strip_tac THEN1 ALL_FC_T rewrite_tac[combinations_finite_lemma]);
a(REPEAT (POP_ASM_T ante_tac));
a(intro_∀_tac(⌜A⌝, ⌜A⌝) THEN intro_∀_tac(⌜m⌝, ⌜m⌝) 
	THEN induction_tac⌜n⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac
	THEN ALL_FC_T1 fc_⇔_canon rewrite_tac[size_0_thm]
	THEN strip_tac THEN all_var_elim_asm_tac1);
a(strip_asm_tac(∀_elim⌜m⌝ ℕ_cases_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "1.1" *** *)
a(rewrite_tac[binomial_0_clauses]);
a(LEMMA_T ⌜{X|X ⊆ {} ∧ # X = 0} = {{}}⌝
	(fn th => rewrite_tac[th, size_empty_thm,
		size_singleton_thm, binomial_def]));
a(PC_T "sets_ext" strip_tac THEN REPEAT strip_tac);
(* *** Goal "1.1.1" *** *)
a(swap_nth_asm_concl_tac 2);
a(all_fc_tac[⊆_finite_thm]);
a(ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[size_0_thm]);
(* *** Goal "1.1.2" *** *)
a(all_var_elim_asm_tac1 THEN REPEAT strip_tac);
(* *** Goal "1.1.3" *** *)
a(asm_rewrite_tac[size_empty_thm]);
(* *** Goal "1.2" *** *)
a(rewrite_tac[binomial_0_clauses]);
a(LEMMA_T ⌜{X|X ⊆ {} ∧ # X = i + 1} = {}⌝
	(fn th => rewrite_tac[th, size_empty_thm]));
a(LEMMA_T⌜∀X⦁X ⊆ {} ⇔ X = {}⌝ rewrite_thm_tac
	THEN1 PC_T1 "sets_ext" prove_tac[]);
a(PC_T "sets_ext" strip_tac THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[size_empty_thm]);
(* *** Goal "2" *** *)
a(strip_asm_tac(∀_elim⌜m'⌝ ℕ_cases_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "2.1" *** *)
a(rewrite_tac[binomial_0_clauses]);
a(LEMMA_T ⌜{X|X ⊆ A ∧ # X = 0} = {{}}⌝
	(fn th => rewrite_tac[th, size_empty_thm,
		size_singleton_thm, binomial_def]));
a(PC_T "sets_ext" strip_tac THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(swap_nth_asm_concl_tac 2);
a(all_fc_tac[⊆_finite_thm]);
a(ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[size_0_thm]);
(* *** Goal "2.1.2" *** *)
a(all_var_elim_asm_tac1 THEN REPEAT strip_tac);
(* *** Goal "2.1.3" *** *)
a(asm_rewrite_tac[size_empty_thm]);
(* *** Goal "2.2" *** *)
a(rewrite_tac[binomial_def]);
a(cases_tac⌜A = {}⌝
	THEN1 (all_var_elim_asm_tac1 THEN POP_ASM_T ante_tac
		THEN rewrite_tac[size_empty_thm]));
a(POP_ASM_T (PC_T1 "sets_ext1" strip_asm_tac));
a(lemma_tac⌜∃B⦁B ⊆ A ∧ ¬x ∈ B ∧ A = {x} ∪ B⌝
	THEN1 (∃_tac⌜A \ {x}⌝ THEN PC_T1 "sets_ext" asm_prove_tac[]));
a(all_fc_tac[⊆_finite_thm] THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 4 ante_tac);
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(lemma_tac ⌜
	{X|X ⊆ {x} ∪ B ∧ # X = i + 1} ∈ Finite⌝
	THEN1 (bc_thm_tac combinations_finite_lemma
		THEN strip_tac));
a(lemma_tac ⌜
	{X | X ⊆ B ∧ # X = i + 1} ⊆
	{X|X ⊆ {x} ∪ B ∧ # X = i + 1}⌝
	THEN1 PC_T1 "sets_ext" prove_tac[]);
a(ALL_FC_T asm_rewrite_tac[size_⊆_diff_thm]);
a(ante_tac(list_∀_elim[⌜{X|X ⊆ B ∧ # X = i}⌝,
	⌜{X|X ⊆ {x} ∪ B ∧ # X = i + 1} \ {X|X ⊆ B ∧ # X = i + 1}⌝,
	⌜λY⦁{x} ∪ Y⌝] bijection_finite_size_thm));
a(ALL_FC_T asm_rewrite_tac[combinations_finite_lemma]);
a(REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(i_contr_tac THEN LIST_DROP_NTH_ASM_T [1, 2, 4, 6, 12]
	(MAP_EVERY ante_tac) THEN DROP_ASMS_T discard_tac);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2.1.1" *** *)
a(spec_nth_asm_tac 2 ⌜x''⌝ THEN all_var_elim_asm_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.2.1.2" *** *)
a(spec_nth_asm_tac 2 ⌜x''⌝ THEN all_var_elim_asm_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.2.2" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 1);
a(LEMMA_T ⌜{X|X ⊆ {x} ∪ B ∧ # X = i + 1} \
	{X|X ⊆ B ∧ # X = i + 1} =
	{X|X ⊆ {x} ∪ B ∧ # X = i + 1 ∧ x ∈ X}⌝
	rewrite_thm_tac
	THEN1 (DROP_NTH_ASM_T 6 ante_tac
		THEN DROP_ASMS_T discard_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
(* *** Goal "2.2.2.1" *** *)
a(spec_nth_asm_tac 4 ⌜x''⌝ THEN all_var_elim_asm_tac);
(* *** Goal "2.2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [5, 6, 8]
	(MAP_EVERY ante_tac) THEN DROP_ASMS_T discard_tac
	THEN REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(∃_tac⌜x' \ {x}⌝ THEN REPEAT strip_tac
	THEN_TRY SOLVED_T (PC_T1 "sets_ext" asm_prove_tac[]));
a(all_fc_tac[⊆_finite_thm]);
a(lemma_tac⌜{x} ⊆ x'⌝ THEN1 PC_T1 "sets_ext" asm_prove_tac[]);
a(DROP_NTH_ASM_T 4 ante_tac THEN ALL_FC_T rewrite_tac[size_⊆_diff_thm]);
a(rewrite_tac[size_singleton_thm]);
(* *** Goal "2.2.2.2.2" *** *)
a(all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.2.2.3" *** *)
a(all_var_elim_asm_tac1);
a(all_fc_tac[⊆_finite_thm]);
a(lemma_tac⌜¬x ∈ x''⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
(* *** Goal "2.2.2.2.4" *** *)
a(all_var_elim_asm_tac1 THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏binomial_thm1⦎ = save_thm ( "binomial_thm1", (
set_goal([], ⌜∀x n⦁
	(ℕℝ 1 + x) ^ n =
	Series (λm⦁ℕℝ(Binomial n m) * x ^ m) (n+1)
⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[ℝ_ℕ_exp_def, series_def, binomial_0_clauses]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[ℝ_ℕ_exp_def] THEN POP_ASM_T discard_tac);
a(conv_tac (RIGHT_C(once_rewrite_conv[series_induction_thm1])));
a(rewrite_tac[binomial_def, ℕℝ_plus_homomorphism_thm,
	ℝ_times_plus_distrib_thm]);
a(EXTEND_PC_T1 "'sho_rw" pure_rewrite_tac[plus_series_thm] THEN rewrite_tac[]);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y a b⦁x = a ∧ y = ℕℝ 1 + b ⇒ y + x = ℕℝ 1 + a + b⌝)
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[ℝ_ℕ_exp_def,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b⦁a * x * b = x * a * b⌝]);
a(EXTEND_PC_T1 "'sho_rw" pure_rewrite_tac[const_times_series_thm] THEN rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(conv_tac (LEFT_C(rewrite_conv[series_induction_thm1])));
a(rewrite_tac[binomial_0_clauses]);
a(rewrite_tac[series_def]);
a(LEMMA_T ⌜Binomial n (n+1) = 0⌝ rewrite_thm_tac);
a(bc_thm_tac binomial_less_0_thm THEN rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
For historical reasons, the meat of the following proof deals with $(y+x)^n$ not $(x+y)^n$.

=SML
val ⦏binomial_thm⦎ = save_thm ( "binomial_thm", (
set_goal([], ⌜∀x y n⦁
	(x + y) ^ n =
	Series (λm⦁ℕℝ(Binomial n m) * x ^ m * y ^ (n - m)) (n+1)
⌝);
a(REPEAT strip_tac THEN once_rewrite_tac[ℝ_plus_comm_thm]);
a(cases_tac⌜y = ℕℝ 0⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(rewrite_tac[series_def, binomial_eq_thm]);
a(LEMMA_T ⌜∀k⦁k ≤ n ⇒ Series (λ m⦁ ℕℝ (Binomial n m) * x ^ m * ℕℝ 0 ^ (n - m)) k = ℕℝ 0⌝
	(fn th => rewrite_tac[rewrite_rule[](∀_elim⌜n⌝ th)]));
a(∀_tac THEN induction_tac ⌜k:ℕ⌝
	THEN asm_rewrite_tac[series_def]
	THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]
	THEN rewrite_tac[≤_def]
	THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(k+1)+i = (i+1)+k⌝,
	ℝ_ℕ_exp_0_1_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜(y + x) ^ n = y^n *(ℕℝ 1 + y ⋏-⋏1 * x)^n⌝
	(fn th => rewrite_tac[th, binomial_thm1]));
(* *** Goal "2.1" *** *)
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) ℝ_ℕ_exp_times_thm,
	ℝ_times_plus_distrib_thm,
	ℝ_times_assoc_thm1]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(LEMMA_T ⌜∀k⦁k ≤ n + 1 ⇒
	y ^ n * Series (λ m⦁ ℕℝ (Binomial n m) * (y ⋏-⋏1 * x) ^ m) k =
	Series (λ m⦁ ℕℝ (Binomial n m) * x ^ m * y ^ (n - m)) k⌝
	(fn th => rewrite_tac[rewrite_rule[](∀_elim⌜n+1⌝ th)]));
a(∀_tac THEN induction_tac ⌜k:ℕ⌝
	THEN asm_rewrite_tac[series_def,
		ℝ_times_plus_distrib_thm]
	THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]
	THEN rewrite_tac[≤_def]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(rewrite_tac[ℝ_ℕ_exp_plus_thm, ℝ_ℕ_exp_times_thm,
	∀_elim⌜(y ⋏-⋏1)^k⌝ ℝ_times_order_thm]);
a(rewrite_tac[ℝ_times_assoc_thm1]);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) ℝ_ℕ_exp_times_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(rewrite_tac[ℝ_ℕ_exp_0_1_thm] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏factorial_not_0_thm⦎ = save_thm ( "factorial_not_0_thm", (
set_goal([], ⌜∀m⦁ ¬ℕℝ(m!) = ℕℝ 0⌝);
a(strip_tac);
a(strip_asm_tac(∀_elim⌜m⌝factorial_0_less_thm));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏factorial_times_thm⦎ = save_thm ( "factorial_times_thm", (
set_goal([], ⌜∀m⦁ ℕℝ(m!) * ℕℝ(m!) ⋏-⋏1 = ℕℝ 1 ∧ ℕℝ(m!) ⋏-⋏1 * ℕℝ(m!) = ℕℝ 1 ⌝);
a(strip_tac);
a(strip_asm_tac(∀_elim⌜m⌝factorial_not_0_thm));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏binomial_factorial_thm⦎ = save_thm ( "binomial_factorial_thm", (
set_goal([], ⌜∀m n⦁
	ℕℝ (Binomial (m+n) m) = ℕℝ((m+n)!) * ℕℝ(m!) ⋏-⋏1 * ℕℝ(n!) ⋏-⋏1
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃t⦁m + n = t⌝ THEN1 prove_∃_tac
	THEN POP_ASM_T ante_tac);
a(intro_∀_tac(⌜n⌝, ⌜n⌝) THEN intro_∀_tac(⌜m⌝, ⌜m⌝));
a(induction_tac⌜t⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[binomial_0_clauses, factorial_def,
	factorial_times_thm,
	ℕℝ_times_homomorphism_thm]);
(* *** Goal "2" *** *)
a(strip_asm_tac(∀_elim⌜m'⌝ℕ_cases_thm)
	THEN all_var_elim_asm_tac1);
(* *** Goal "2.1" *** *)
a(rewrite_tac[binomial_0_clauses,
	∧_left_elim factorial_def,
	factorial_times_thm]);
(* *** Goal "2.2" *** *)
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(i+1)+n = (i+n)+1⌝,
	ℕℝ_plus_homomorphism_thm,
	binomial_def]);
a(lemma_tac⌜i + n = t⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_GET_NTH_ASM_T [3] (ALL_FC_T rewrite_tac));
a(strip_asm_tac(∀_elim⌜n⌝ℕ_cases_thm)
	THEN var_elim_nth_asm_tac 1);
(* *** Goal "2.2.1" *** *)
a(LEMMA_T ⌜Binomial i (i+1) = 0⌝ rewrite_thm_tac
	THEN1 (bc_thm_tac binomial_less_0_thm
		THEN REPEAT strip_tac));
a(asm_rewrite_tac[binomial_0_clauses,
	∧_left_elim factorial_def,
	factorial_times_thm]);
(* *** Goal "2.2.2" *** *)
a(rename_tac[(⌜i⌝, "M"), (⌜i'⌝, "N")]
	THEN POP_ASM_T ante_tac);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜M + N + 1 = (M + 1) + N⌝]
	THEN strip_tac);
a(LIST_DROP_NTH_ASM_T [3] (ALL_FC_T rewrite_tac));
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(M + 1) + N = (M + N) + 1⌝]);
a(strip_asm_tac(∀_elim⌜N+1⌝ factorial_not_0_thm));
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[
	conv_rule(ONCE_MAP_C (RIGHT_C eq_sym_conv)) ℝ_times_cancel_thm]);
a(POP_ASM_T discard_tac);
a(rewrite_tac[ℝ_times_assoc_thm, factorial_times_thm]);
a(strip_asm_tac(∀_elim⌜M+1⌝ factorial_not_0_thm));
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[
	conv_rule(ONCE_MAP_C (RIGHT_C eq_sym_conv)) ℝ_times_cancel_thm]);
a(POP_ASM_T discard_tac);
a(rewrite_tac[ℝ_times_assoc_thm,
	factorial_times_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀MN1 M N Mi Ni M1 N1 M1i N1i:ℝ⦁
	(MN1 * Mi * N1i + MN1 * M1i * Ni) * N1 * M1
	= (MN1 * Mi * (N1i * N1) * M1 + MN1 * (M1i * M1) * Ni *N1)
⌝]);
a(rewrite_tac[factorial_times_thm]);
a(rewrite_tac[eq_sym_rule(∀_elim⌜M⌝factorial_times_recip_thm)]);
a(rewrite_tac[eq_sym_rule(∀_elim⌜N⌝factorial_times_recip_thm)]);
a(rewrite_tac[ℝ_times_assoc_thm,
	factorial_times_thm]);
a(conv_tac(RIGHT_C(once_rewrite_conv[factorial_def])));
a(rewrite_tac[ℕℝ_plus_homomorphism_thm,
	ℕℝ_times_homomorphism_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏enumerate_thm⦎ = save_thm ( "enumerate_thm", (
set_goal([], ⌜∃enumerate⦁∀a ⦁
	a ∈ Finite
⇔	(∀ i j⦁ i < #a ∧ j < #a ∧ enumerate a i = enumerate a j ⇒ i = j)
∧	a = {x|∃ i⦁ i < #a ∧ enumerate a i = x}
⌝);
a(prove_∃_tac THEN strip_tac);
a(cases_tac⌜a' ∈ Finite⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[range_bijection_finite_size_thm1]);
(* *** Goal "2" *** *)
a(∃_tac⌜λm:ℕ⦁ (y:'a)⌝ THEN rewrite_tac[]);
a(strip_tac THEN ∨_right_tac);
a(swap_nth_asm_concl_tac 1);
a(once_asm_rewrite_tac[] THEN DROP_ASMS_T discard_tac);
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{y}⌝
	THEN rewrite_tac[singleton_finite_thm]
	THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏covering_finite_size_thm⦎ = save_thm ( "covering_finite_size_thm", (
set_goal([], ⌜∀a b f m⦁
	a ∈ Finite
∧	(∀x⦁x ∈ b ⇒ f x ∈ a)
∧	(∀y⦁y ∈ a ⇒ {x | x ∈ b ∧ y = f x} ∈ Finite ∧ #{x | x ∈ b ∧ y = f x} = m)
⇒	b ∈ Finite ∧ #b = m * #a⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(strip_asm_tac(∀_elim⌜m⌝ range_finite_size_thm));
a(LEMMA_T⌜({i | i < m} × a) ∈ Finite ∧ #({i | i < m} × a) = # {i|i < m} * #a⌝
	ante_tac
	THEN1 (bc_thm_tac ×_finite_size_thm THEN REPEAT strip_tac));
a(asm_rewrite_tac[] THEN strip_tac);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac(bijection_finite_size_thm));
a(strip_asm_tac enumerate_thm);
a(∃_tac⌜λ(i, y)⦁enumerate {x | x ∈ b ∧ y = f x} i⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN DROP_NTH_ASM_T 2 ante_tac);
a(rewrite_tac[×_def]);
a(strip_asm_tac (∀_elim⌜m⌝ℕ_cases_thm)
	THEN all_var_elim_asm_tac1 THEN1 asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 10 (fn th =>
		ante_tac (∀_elim⌜Snd x⌝ th)
	THEN ante_tac (∀_elim⌜Snd y⌝ th)));
a(DROP_NTH_ASM_T 6 rewrite_thm_tac
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T[2, 3, 5, 6]
	(MAP_EVERY ante_tac));
a(rename_tac[] THEN LIST_GET_NTH_ASM_T [1, 2] rewrite_tac
	THEN REPEAT strip_tac);
a(lemma_tac⌜enumerate {x'|x' ∈ b ∧ Snd x = f x'} (Fst x) ∈
	{x'|x' ∈ b ∧ Snd x = f x'}⌝);
(* *** Goal "1.1" *** *)
a(POP_ASM_T (fn th => conv_tac(RIGHT_C (once_rewrite_conv[th]))));
a(rewrite_tac[]);
a(∃_tac⌜Fst x⌝ THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜enumerate {x'|x' ∈ b ∧ Snd x = f x'} (Fst x) ∈
	{x'|x' ∈ b ∧ Snd y = f x'}⌝);
(* *** Goal "1.2.1" *** *)
a(DROP_NTH_ASM_T 13 pure_rewrite_thm_tac);
a(DROP_NTH_ASM_T 5 (fn th => conv_tac(RIGHT_C (once_rewrite_conv[th]))));
a(rewrite_tac[]);
a(∃_tac⌜Fst y⌝ THEN REPEAT strip_tac);
a(LEMMA_T ⌜Snd x = Snd y⌝ 
	(fn th => all_asm_ante_tac
		THEN asm_tac th
		THEN asm_rewrite_tac[]
		THEN REPEAT strip_tac)
	THEN1 (POP_ASM_T rewrite_thm_tac
		THEN strip_tac));
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(PC_T1 "prop_eq_pair" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LIST_GET_NTH_ASM_T [7] all_fc_tac);
a(LIST_GET_NTH_ASM_T [7] (ALL_FC_T(MAP_EVERY ante_tac)));
a(DROP_NTH_ASM_T 3 rewrite_thm_tac
	THEN REPEAT strip_tac);
a(LEMMA_T ⌜x ∈ {x'|x' ∈ b ∧ f x = f x'}⌝
	ante_tac THEN1 asm_rewrite_tac[]);
a(POP_ASM_T pure_once_rewrite_thm_tac);
a(rewrite_tac[] THEN strip_tac);
a(all_var_elim_asm_tac1);
a(∃_tac⌜(i, f x)⌝ THEN asm_rewrite_tac[×_def]);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[×_def]));
a(LIST_GET_NTH_ASM_T [8] (ALL_FC_T(MAP_EVERY ante_tac)));
a(DROP_NTH_ASM_T 4 rewrite_thm_tac
	THEN REPEAT strip_tac);
a(LEMMA_T⌜x ∈ {x|x ∈ b ∧ Snd x' = f x}⌝
	(fn th => ante_tac th THEN PC_T1 "sets_ext1" prove_tac[]));
a(POP_ASM_T pure_once_rewrite_thm_tac THEN rewrite_tac[]);
a(all_var_elim_asm_tac1 THEN ∃_tac⌜Fst x'⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏samples_finite_size_thm⦎ = save_thm ( "samples_finite_size_thm", (
set_goal([], ⌜∀a n⦁
	a ∈ Finite
⇒	{L | Elems L ⊆ a ∧ #L = n} ∈ Finite
∧	#{L | Elems L ⊆ a ∧ #L = n} = #a ^ n
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(induction_tac⌜n⌝ THEN rewrite_tac[ℕ_exp_def]);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜{L|Elems L ⊆ a ∧ # L = 0} = {[]}⌝
	(fn th => rewrite_tac[th, size_singleton_thm, singleton_finite_thm]));
a(PC_T "sets_ext1" strip_tac THEN ∀_tac THEN rewrite_tac[]);
a(strip_asm_tac(∀_elim⌜x⌝list_cases_thm)
	THEN asm_rewrite_tac[elems_def, length_def]);
(* *** Goal "2" *** *)
a(ante_tac(list_∀_elim[⌜a⌝, ⌜{L | Elems L ⊆ a ∧ #L = n}⌝]
	×_finite_size_thm));
a(asm_rewrite_tac[]);
a(REPEAT ⇒_tac THEN POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac(bijection_finite_size_thm));
a(∃_tac⌜Uncurry Cons⌝ THEN rewrite_tac[uncurry_def]
	THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(PC_T1 "prop_eq_pair" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(POP_ASM_T ante_tac THEN strip_asm_tac(∀_elim⌜x⌝list_cases_thm)
	THEN all_var_elim_asm_tac1 
	THEN rewrite_tac[length_def]);
a(REPEAT strip_tac);
a(∃_tac⌜(x', list2)⌝ THEN asm_rewrite_tac[×_def]);
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[elems_def]);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.3" *** *)
a(all_var_elim_asm_tac1);
a(REPEAT_N 2 (POP_ASM_T ante_tac));
a(rewrite_tac[elems_def, ×_def]);
a(REPEAT strip_tac THEN1 all_var_elim_asm_tac1);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2.4" *** *)
a(all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac THEN rewrite_tac[×_def, length_def]
	THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏distinct_samples_rw_thm⦎ = save_thm ( "distinct_samples_rw_thm", (
set_goal([], ⌜∀n m⦁
	DistinctSamples n m =
	if m = 0
	then 1
	else (n+m) * DistinctSamples n (m-1)
⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜m⌝ℕ_cases_thm) THEN asm_rewrite_tac[distinct_samples_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏distinct_samples_up_thm⦎ = save_thm ( "distinct_samples_up_thm", (
set_goal([], ⌜∀n m⦁
	DistinctSamples n (m+1) = (n+1) * DistinctSamples (n+1) m
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜m⌝);
(* *** Goal "1" *** *)
a(rewrite_tac [distinct_samples_def]);
(* *** Goal "2" *** *)
a(once_rewrite_tac[distinct_samples_def]);
a(asm_rewrite_tac[]);
a(PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏distinct_samples_finite_size_thm⦎ = save_thm ( "distinct_samples_finite_size_thm", (
set_goal([], ⌜∀a n⦁a ∈ Finite ∧ n ≤ #a
⇒	{L | Elems L ⊆ a ∧ # L = n ∧ L ∈ Distinct} ∈ Finite
∧	#{L | Elems L ⊆ a ∧ # L = n ∧ L ∈ Distinct} = DistinctSamples (#a - n) n
⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN POP_ASM_T ante_tac);
a(induction_tac⌜n:ℕ⌝);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜{L|Elems L ⊆ a ∧ # L = 0 ∧ L ∈ Distinct} = {[]}⌝
	(fn th => asm_rewrite_tac[th, size_singleton_thm, singleton_finite_thm,
	distinct_samples_def]));
a(PC_T "sets_ext1" strip_tac THEN ∀_tac THEN rewrite_tac[]);
a(strip_asm_tac(∀_elim⌜x⌝list_cases_thm)
	THEN asm_rewrite_tac[elems_def, length_def, distinct_def]);
(* *** Goal "2" *** *)
a(strip_tac THEN i_contr_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(⇒_tac);
a(DROP_NTH_ASM_T 2 ante_tac);
a(POP_ASM_T (strip_asm_tac o once_rewrite_rule[plus_comm_thm]
	 o rewrite_rule[≤_def]));
a(TOP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(rewrite_tac[distinct_samples_up_thm, ∀_elim⌜n⌝ plus_order_thm]);
a(STRIP_T (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac covering_finite_size_thm);
(* *** Goal "3" *** *)
a(∃_tac⌜Tail⌝ THEN rewrite_tac[] THEN REPEAT_UNTIL is_∧ strip_tac
	THEN REPEAT_N 3 strip_tac THEN1 REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(DROP_NTH_ASM_T 3 ante_tac
	THEN DROP_NTH_ASM_T 2 ante_tac
	THEN strip_asm_tac (∀_elim⌜x⌝ list_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN asm_rewrite_tac[length_def, elems_def, tail_def]
	THEN PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "3.2" *** *)
a(DROP_NTH_ASM_T 4 ante_tac
	THEN DROP_NTH_ASM_T 2 ante_tac
	THEN strip_asm_tac (∀_elim⌜x⌝ list_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN asm_rewrite_tac[length_def, tail_def]
	THEN taut_tac);
(* *** Goal "3.3" *** *)
a(POP_ASM_T ante_tac THEN POP_ASM_T ante_tac
	THEN strip_asm_tac (∀_elim⌜x⌝ list_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN asm_rewrite_tac[length_def, distinct_def, tail_def]
	THEN taut_tac);
(* *** Goal "3.4" *** *)
a(REPEAT ⇒_tac);
a(ante_tac(list_∀_elim[⌜a⌝, ⌜Elems y⌝] size_⊆_diff_thm)
	THEN DROP_NTH_ASM_T 4 (asm_rewrite_thm_tac o eq_sym_rule));
a(LEMMA_T ⌜#(Elems y) = #y⌝ asm_rewrite_thm_tac
	THEN1 (bc_thm_tac distinct_size_length_thm
		THEN REPEAT strip_tac));
a(rewrite_tac[∀_elim⌜n⌝ plus_order_thm]);
a(STRIP_T rewrite_thm_tac);
a(bc_thm_tac bijection_finite_size_thm);
a(∃_tac⌜λx⦁Cons x y⌝ THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "3.4.1" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜a⌝ THEN REPEAT strip_tac
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "3.4.2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "3.4.2.1" *** *)
a(LIST_DROP_NTH_ASM_T [2, 3, 5, 7] (MAP_EVERY ante_tac)
	THEN strip_asm_tac (∀_elim⌜x⌝ list_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[length_def, tail_def, distinct_def, elems_def]);
a(REPEAT strip_tac THEN ∃_tac⌜x'⌝ THEN PC_T1 "sets_ext1" asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN rewrite_tac[elems_def]
	THEN REPEAT strip_tac);
(* *** Goal "3.4.2.2" *** *)
a(POP_ASM_T ante_tac THEN all_var_elim_asm_tac1
	THEN asm_rewrite_tac[elems_def]);
a(REPEAT strip_tac THEN1 all_var_elim_asm_tac);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "3.4.2.3" *** *)
a(asm_rewrite_tac[length_def]);
(* *** Goal "3.4.2.4" *** *)
a(asm_rewrite_tac[distinct_def]);
(* *** Goal "3.4.2.5" *** *)
a(asm_rewrite_tac[tail_def]);
pop_thm()
));

=TEX
%%%%
%%%%
If a naive approach to the calculations were taken, the following would take 15 seconds or so to run through (prior to version 2.7.7 of ProofPower).
The contrivances below cut this down to a second or so (as also do performance enhancements in versions 2.7.7 and later of ProofPower).

=SML
val ⦏birthdays_thm⦎ = save_thm ( "birthdays_thm", (
set_goal([], ⌜
	let	S = {L | Elems L ⊆ {i | 1 ≤ i ∧ i ≤ 365} ∧ # L = 23} 
	in let	X = {L | L ∈ S ∧ ¬L ∈ Distinct}
	in	S ∈ Finite
	∧	¬#S = 0
	∧	X ⊆ S
	∧	#X / #S > 1/2
⌝);
a(rewrite_tac[let_def]);
a(strip_asm_tac(∀_elim⌜365⌝ range_finite_size_thm1));
a(lemma_tac⌜23 ≤ #{i | 1 ≤ i ∧ i ≤ 365}⌝ THEN1 asm_rewrite_tac[]);
a(all_fc_tac[distinct_samples_finite_size_thm]);
a(all_fc_tac[samples_finite_size_thm]);
a(REPEAT_N 2 (POP_ASM_T(ante_tac o ∀_elim⌜23⌝)) );
a(POP_ASM_T discard_tac THEN strip_tac THEN strip_tac);
a(pure_asm_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv)ℕℝ_one_one_thm,
	ℕℝ_ℕ_exp_thm,
	ℝ_frac_def]);
a(asm_tac(rewrite_conv[]⌜ℕℝ 365 ^ 23⌝));
a(PC_T1"predicates" rewrite_tac[] THEN strip_tac
	THEN1 (pure_asm_rewrite_tac[ℕℝ_one_one_thm]
		THEN PC_T1 "lin_arith" prove_tac[]));
a(REPEAT strip_tac THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(pure_rewrite_tac[ℕℝ_one_one_thm]);
a(LEMMA_T⌜{L | (Elems L ⊆ {i | 1 ≤ i ∧ i ≤ 365} ∧ # L = 23) ∧ ¬L ∈ Distinct}
 = {L | Elems L ⊆ {i | 1 ≤ i ∧ i ≤ 365} ∧ # L = 23} \
	{L | Elems L ⊆ {i | 1 ≤ i ∧ i ≤ 365} ∧ # L = 23 ∧ L ∈ Distinct}⌝
	pure_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(lemma_tac⌜{L | Elems L ⊆ {i | 1 ≤ i ∧ i ≤ 365} ∧ # L = 23 ∧ L ∈ Distinct} ⊆
	{L | Elems L ⊆ {i | 1 ≤ i ∧ i ≤ 365} ∧ # L = 23}⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(ALL_FC_T (MAP_EVERY (ante_tac o
	once_rewrite_rule[conv_rule(ONCE_MAP_C eq_sym_conv)ℕℝ_one_one_thm])) [size_⊆_diff_thm]);
a(pure_rewrite_tac[ℕℝ_plus_homomorphism_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b c:ℝ⦁a = b + c ⇔ b = a - c⌝]
	THEN STRIP_T pure_rewrite_thm_tac);
a(LIST_DROP_NTH_ASM_T [3, 6, 9] pure_rewrite_tac);
a(LEMMA_T ⌜∀a b c d:ℝ⦁ℕℝ 0 < b ∧ ℕℝ 0 < d ∧ a*d < b*c ⇒ a/b < c/d⌝
	bc_thm_tac
	THEN1 (REPEAT strip_tac
		THEN1 ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[ℝ_cross_mult_less_thm]));
a(pure_asm_rewrite_tac[ℕℝ_ℕ_exp_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b c:ℝ⦁a < ℕℝ 2 * (b - c) ⇔ a + ℕℝ 2 * c < ℕℝ 2 * b⌝,
	REPEAT_C (once_rewrite_conv[distinct_samples_rw_thm] THEN_C rewrite_conv[])
	⌜DistinctSamples (365-23) 23⌝]);
a(pure_rewrite_tac[ℕℝ_plus_homomorphism_thm1,
	ℕℝ_times_homomorphism_thm1,
	ℕℝ_less_thm]);
a(rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_thm⦎ = save_thm ( "walk_thm", (
set_goal([], ⌜∀n x⦁
	Walk n x =
	{s
	| ∃a⦁	(∀m⦁m ∈ a ⇒ m < n)
	∧ 	(∀m⦁ s m = x + ℕℤ(#({k | k < m ∧ k < n} ∩ a)) - ℕℤ(#({k | k < m ∧ k < n} \ a)))}⌝);
a(PC_T1 "sets_ext1" rewrite_tac[walk_def1] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rename_tac[(⌜x'⌝, "s")] THEN ∃_tac⌜{m | m < n ∧ s(m+1) - s m = ℕℤ 1}⌝);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(induction_tac⌜m⌝ THEN1 asm_rewrite_tac[
	pc_rule1 "sets_ext1" prove_rule[]⌜{x|F} = {}⌝,
	size_empty_thm]);
a(cases_tac⌜¬m < n⌝);
(* *** Goal "1.1" *** *)
a(lemma_tac⌜n ≤ m ∧ n ≤ m+1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(DROP_NTH_ASM_T 2 rewrite_thm_tac
	THEN POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(DROP_NTH_ASM_T 4 (fn th => conv_tac(LEFT_C (eq_match_conv th)))
	THEN rewrite_tac[]);
a(LEMMA_T ⌜∀a b c d x y:ℕ SET⦁
	a = c ∧ b = d ⇒ ℕℤ(#(a ∩ x)) + ~(ℕℤ(#(b \ x))) = ℕℤ(#(c ∩ x)) + ~(ℕℤ(#(d \ x)))⌝ bc_thm_tac
	THEN1 (REPEAT strip_tac THEN asm_rewrite_tac[]));
a(PC_T1 "sets_ext" rewrite_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 4 (strip_asm_tac o ∀_elim⌜m⌝));
(* *** Goal "1.2.1" *** *)
a(ALL_FC_T rewrite_tac[pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜∀x y⦁x + ~y = ℕℤ 1 ⇒ x = y + ℕℤ 1⌝]);
a(DROP_NTH_ASM_T 3 (fn th => conv_tac(LEFT_C (LEFT_C(eq_match_conv th))))
	THEN rewrite_tac[ℤ_plus_assoc_thm]);
a(LEMMA_T ⌜∀b d:ℕ SET; r s⦁
	b = d ∧ s = r + ℕℤ 1 ⇒ r + ~(ℕℤ(#b)) + ℕℤ 1 = s + ~(ℕℤ(#d))⌝ bc_thm_tac
	THEN1 (REPEAT strip_tac THEN asm_rewrite_tac[]
		THEN PC_T1 "ℤ_lin_arith" prove_tac[]));
a(REPEAT strip_tac
	THEN1 (PC_T1 "sets_ext" REPEAT strip_tac
		THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]));
(* *** Goal "1.2.1.1" *** *)
a(contr_tac THEN lemma_tac⌜x' = m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
(* *** Goal "1.2.1.2" *** *)
a(rewrite_tac[ℕℤ_plus_homomorphism_thm1, ℕℤ_one_one_thm]);
a(LEMMA_T⌜
	{k|k < m + 1 ∧ k < n} ∩ {m|m < n ∧ s (m + 1) + ~ (s m) = ℕℤ 1} =
	{m} ∪ ({k|k < m ∧ k < n} ∩ {m|m < n ∧ s (m + 1) + ~ (s m) = ℕℤ 1})⌝
	rewrite_thm_tac
	THEN PC_T1 "sets_ext" REPEAT strip_tac
		THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.1.2.1" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "1.2.1.2.2" *** *)
a(bc_thm_tac size_singleton_∪_thm);
a(REPEAT strip_tac);
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{k|k < m}⌝);
a(rewrite_tac[range_finite_size_thm]);
a(PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(ALL_FC_T rewrite_tac[pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜∀x y⦁x + ~y = ~(ℕℤ 1) ⇒ x = y + ~(ℕℤ 1)⌝]);
a(DROP_NTH_ASM_T 3 (fn th => conv_tac(LEFT_C (LEFT_C(eq_match_conv th))))
	THEN rewrite_tac[ℤ_plus_assoc_thm]);
a(LEMMA_T ⌜∀b d:ℕ SET; r s⦁
	b = d ∧ s = r + ~(ℕℤ 1) ⇒ ℕℤ(#b) + r + ~(ℕℤ 1) = ℕℤ(#d) + s⌝ bc_thm_tac
	THEN1 (REPEAT strip_tac THEN asm_rewrite_tac[]
		THEN PC_T1 "ℤ_lin_arith" prove_tac[]));
a(REPEAT strip_tac
	THEN1 (PC_T1 "sets_ext" REPEAT strip_tac
		THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]));
(* *** Goal "1.2.2.1" *** *)
a(contr_tac THEN lemma_tac⌜x' = m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.2" *** *)
a(rewrite_tac[ℕℤ_plus_homomorphism_thm1, ℕℤ_one_one_thm,
	pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜∀x y⦁~x = ~y + ~(ℕℤ 1) ⇔ x = y + ℕℤ 1⌝]);
a(LEMMA_T⌜
	{k|k < m + 1 ∧ k < n} \ {m|m < n ∧ s (m + 1) + ~ (s m) = ℕℤ 1} =
	{m} ∪ ({k|k < m ∧ k < n} \ {m|m < n ∧ s (m + 1) + ~ (s m) = ℕℤ 1})⌝
	rewrite_thm_tac
	THEN PC_T1 "sets_ext" REPEAT strip_tac
		THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2.2.1" *** *)
a(all_var_elim_asm_tac1 THEN POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.2.2" *** *)
a(bc_thm_tac size_singleton_∪_thm);
a(REPEAT strip_tac);
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{k|k < m}⌝);
a(rewrite_tac[range_finite_size_thm]);
a(PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[
	pc_rule1 "sets_ext1" prove_rule[]⌜{x|F} = {}⌝,
	size_empty_thm]);
(* *** Goal "3" *** *)
a(lemma_tac⌜¬m ∈ a⌝);
(* *** Goal "3.1" *** *)
a(swap_nth_asm_concl_tac 1);
a(DROP_NTH_ASM_T 3 (fn th => conv_tac(once_rewrite_conv[th])));
a(LEMMA_T ⌜∀a b c d x y:ℕ SET; t : ℤ⦁
	b = d ∧ ℕℤ(#a) = ℕℤ(#c) + ℕℤ 1⇒
	(t + ℕℤ(#a) - ℕℤ(#b)) +
	~(t + ℕℤ(#c) - ℕℤ(#d)) = ℕℤ 1⌝ bc_thm_tac
	THEN1 (REPEAT strip_tac THEN asm_rewrite_tac[]
		THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]));
a(REPEAT strip_tac);
(* *** Goal "3.1.1" *** *)
a(PC_T1 "sets_ext" asm_rewrite_tac[]);
a(REPEAT strip_tac THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]);
a(contr_tac THEN lemma_tac⌜x = m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
(* *** Goal "3.1.2" *** *)
a(rewrite_tac[ℕℤ_plus_homomorphism_thm1, ℕℤ_one_one_thm]);
a(LEMMA_T⌜
	{k|k < m + 1 ∧ k < n} ∩ a =
	{m} ∪ ({k|k < m ∧ k < n} ∩ a)⌝
	rewrite_thm_tac
	THEN PC_T1 "sets_ext" REPEAT strip_tac
		THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]
		THEN1 all_var_elim_asm_tac1);
a(bc_thm_tac size_singleton_∪_thm);
a(REPEAT strip_tac);
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{k|k < m}⌝);
a(rewrite_tac[range_finite_size_thm]);
a(PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "3.2" *** *)
a(DROP_NTH_ASM_T 4 (fn th => conv_tac(once_rewrite_conv[th])));
a(LEMMA_T ⌜∀a b c d x y:ℕ SET; t : ℤ⦁
	a = c ∧ ℕℤ(#b) = ℕℤ(#d) + ℕℤ 1 ⇒
	(t + ℕℤ(#a) - ℕℤ(#b)) +
	~(t + ℕℤ(#c) - ℕℤ(#d)) = ~(ℕℤ 1)⌝ bc_thm_tac
	THEN1 (REPEAT strip_tac THEN asm_rewrite_tac[]
		THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]));
a(REPEAT strip_tac);
(* *** Goal "3.2.1" *** *)
a(PC_T1 "sets_ext" asm_rewrite_tac[]);
a(REPEAT strip_tac THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]);
a(contr_tac THEN lemma_tac⌜x = m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
(* *** Goal "3.2.2" *** *)
a(rewrite_tac[ℕℤ_plus_homomorphism_thm1, ℕℤ_one_one_thm]);
a(LEMMA_T⌜
	{k|k < m + 1 ∧ k < n} \ a =
	{m} ∪ ({k|k < m ∧ k < n} \ a)⌝
	rewrite_thm_tac
	THEN PC_T1 "sets_ext" REPEAT strip_tac
		THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]
		THEN1 all_var_elim_asm_tac1);
a(bc_thm_tac size_singleton_∪_thm);
a(REPEAT strip_tac);
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{k|k < m}⌝);
a(rewrite_tac[range_finite_size_thm]);
a(PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "4" *** *)
a(DROP_NTH_ASM_T 2 rewrite_thm_tac);
a(LEMMA_T ⌜{k|k < m ∧ k < n} = {k|k < n}⌝ rewrite_thm_tac);
a(PC_T1 "sets_ext" asm_rewrite_tac[]);
a(REPEAT strip_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_to_thm⦎ = save_thm ( "walk_to_thm", (
set_goal([], ⌜∀n x y⦁
	WalkTo n x y =
	{s
	| ∃a⦁	(∀m⦁m ∈ a ⇒ m < n)
	∧ 	(∀m⦁ s m = x + ℕℤ(#({k | k < m ∧ k < n} ∩ a)) - ℕℤ(#({k | k < m ∧ k < n} \ a)))
	∧	s n = y}⌝);
a(REPEAT strip_tac THEN PC_T "sets_ext1" strip_tac);
a(rewrite_tac[walk_to_def, walk_thm] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_finite_size_thm⦎ = save_thm ( "walk_finite_size_thm", (
set_goal([], ⌜∀n x⦁ Walk n x ∈ Finite ∧ #(Walk n x) = 2 ^ n⌝);
a(REPEAT ∀_tac);
a(strip_asm_tac(∀_elim⌜n⌝ range_finite_size_thm));
a(ALL_FC_T(MAP_EVERY ante_tac)[ℙ_finite_size_thm]);
a(asm_rewrite_tac[] THEN REPEAT ⇒_tac);
a(GET_NTH_ASM_T 2 (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac bijection_finite_size_thm);
a(asm_rewrite_tac[]);
a(∃_tac⌜λa⦁λm⦁x + ℕℤ (# ({k|k < m ∧ k < n} ∩ a)) - ℕℤ (# ({k|k < m ∧ k < n} \ a))⌝);
a(rewrite_tac[walk_thm, ℙ_def, ⊆_def,
	pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜∀x y z w:ℤ⦁x + ~y = z + ~w ⇔ x + w = z + y⌝,
	ℕℤ_plus_homomorphism_thm1, ℕℤ_one_one_thm]
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4, 5, 6, 7] discard_tac);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN ∀_tac);
a(rename_tac[(⌜x'⌝, "X"), (⌜y⌝, "Y"), (⌜x⌝, "i")]
	THEN cov_induction_tac⌜i:ℕ⌝);
a(cases_tac⌜¬i < n⌝
	THEN1 (lemma_tac⌜¬i ∈ X⌝ THEN1 (contr_tac THEN all_asm_fc_tac[])
	THEN lemma_tac⌜¬i ∈ Y⌝ THEN1 (contr_tac THEN all_asm_fc_tac[])
	THEN REPEAT strip_tac));
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜i+1⌝));
a(cases_tac⌜i ∈ X⌝ THEN contr_tac);
(* *** Goal "1" *** *)
a(swap_nth_asm_concl_tac 3);
a(LEMMA_T⌜
	{k|k < i + 1 ∧ k < n} ∩ X =
	{i} ∪ ({k|k < i ∧ k < n} ∩ X) ∧
	{k|k < i + 1 ∧ k < n} ∩ Y =
	({k|k < i ∧ k < n} ∩ Y) ∧
	{k|k < i + 1 ∧ k < n} \ X =
	({k|k < i ∧ k < n} \ X) ∧
	{k|k < i + 1 ∧ k < n} \ Y =
	{i} ∪ ({k|k < i ∧ k < n} \ Y)⌝
	rewrite_thm_tac);
(* *** Goal "1.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1
	THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.1.1" *** *)
a(cases_tac⌜x = i⌝ THEN1 all_var_elim_asm_tac1);
a(lemma_tac⌜x < i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.1.2" *** *)
a(cases_tac⌜x = i⌝ THEN1 all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(LEMMA_T⌜
	{k|k < i ∧ k < n} ∩ X =
	({k|k < i ∧ k < n} ∩ Y) ∧
	{k|k < i ∧ k < n} \ X =
	({k|k < i ∧ k < n} \ Y)⌝
	rewrite_thm_tac);
(* *** Goal "1.2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY ALL_ASM_FC_T1 fc_⇔_canon (MAP_EVERY strip_asm_tac)[]);
(* *** Goal "1.2.2" *** *)
a(strip_asm_tac(∀_elim⌜i⌝ range_finite_size_thm));
a(lemma_tac⌜
	({k|k < i ∧ k < n} ∩ Y) ∈ Finite ∧
	({k|k < i ∧ k < n} \ Y) ∈ Finite⌝
	THEN1 (REPEAT strip_tac
		THEN bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜{j|j < i}⌝ THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜
	¬i ∈ ({k|k < i ∧ k < n} ∩ Y) ∧
	¬i ∈ ({k|k < i ∧ k < n} \ Y)⌝ (∧_THEN asm_tac)
	THEN1 (REPEAT strip_tac
		THEN PC_T1 "lin_arith" prove_tac[]));
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 3);
a(LEMMA_T⌜
	{k|k < i + 1 ∧ k < n} ∩ Y =
	{i} ∪ ({k|k < i ∧ k < n} ∩ Y) ∧
	{k|k < i + 1 ∧ k < n} ∩ X =
	({k|k < i ∧ k < n} ∩ X) ∧
	{k|k < i + 1 ∧ k < n} \ Y =
	({k|k < i ∧ k < n} \ Y) ∧
	{k|k < i + 1 ∧ k < n} \ X =
	{i} ∪ ({k|k < i ∧ k < n} \ X)⌝
	rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1
	THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.1" *** *)
a(cases_tac⌜x = i⌝ THEN1 all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(cases_tac⌜x = i⌝ THEN1 all_var_elim_asm_tac1);
a(lemma_tac⌜x < i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(LEMMA_T⌜
	{k|k < i ∧ k < n} ∩ X =
	({k|k < i ∧ k < n} ∩ Y) ∧
	{k|k < i ∧ k < n} \ X =
	({k|k < i ∧ k < n} \ Y)⌝
	rewrite_thm_tac);
(* *** Goal "2.2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY ALL_ASM_FC_T1 fc_⇔_canon (MAP_EVERY strip_asm_tac)[]);
(* *** Goal "2.2.2" *** *)
a(strip_asm_tac(∀_elim⌜i⌝ range_finite_size_thm));
a(lemma_tac⌜
	({k|k < i ∧ k < n} ∩ Y) ∈ Finite ∧
	({k|k < i ∧ k < n} \ Y) ∈ Finite⌝
	THEN1 (REPEAT strip_tac
		THEN bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜{j|j < i}⌝ THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜
	¬i ∈ ({k|k < i ∧ k < n} ∩ Y) ∧
	¬i ∈ ({k|k < i ∧ k < n} \ Y)⌝ (∧_THEN asm_tac)
	THEN1 (REPEAT strip_tac
		THEN PC_T1 "lin_arith" prove_tac[]));
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_to_finite_size_thm⦎ = save_thm ( "walk_to_finite_size_thm", (
set_goal([], ⌜∀x m n⦁ WalkTo (m + n) x (x + ℕℤ m - ℕℤ n) ∈ Finite ∧ #(WalkTo (m + n) x (x + ℕℤ m - ℕℤ n)) = Binomial (m + n) m⌝);
a(REPEAT ∀_tac);
a(strip_asm_tac(∀_elim⌜m+n⌝range_finite_size_thm));
a(all_fc_tac[combinations_finite_size_thm]);
a(LIST_DROP_NTH_ASM_T [1, 2] (MAP_EVERY (strip_asm_tac o ∀_elim⌜m⌝)));
a(GET_NTH_ASM_T 2 (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac bijection_finite_size_thm);
a(asm_rewrite_tac[]);
a(∃_tac⌜λa⦁λl⦁x + ℕℤ (# ({k|k < l ∧ k < m + n} ∩ a)) - ℕℤ (# ({k|k < l ∧ k < m + n} \ a))⌝);
a(rewrite_tac[walk_to_thm, ℙ_def, ⊆_def,
	pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜∀x y z w:ℤ⦁x + ~y = z + ~w ⇔ x + w = z + y⌝,
	ℕℤ_plus_homomorphism_thm1, ℕℤ_one_one_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [6, 7, 8, 9] discard_tac);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN ∀_tac);
a(rename_tac[(⌜x'⌝, "X"), (⌜y⌝, "Y"), (⌜x⌝, "i")]
	THEN cov_induction_tac⌜i:ℕ⌝);
a(cases_tac⌜¬i < m + n⌝
	THEN1 (lemma_tac⌜¬i ∈ X⌝ THEN1 (contr_tac THEN all_asm_fc_tac[])
	THEN lemma_tac⌜¬i ∈ Y⌝ THEN1 (contr_tac THEN all_asm_fc_tac[])
	THEN REPEAT strip_tac));
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜i+1⌝));
a(cases_tac⌜i ∈ X⌝ THEN contr_tac);
(* *** Goal "1" *** *)
a(swap_nth_asm_concl_tac 3);
a(LEMMA_T⌜
	{k|k < i + 1 ∧ k < m + n} ∩ X =
	{i} ∪ ({k|k < i ∧ k < m + n} ∩ X) ∧
	{k|k < i + 1 ∧ k < m + n} ∩ Y =
	({k|k < i ∧ k < m + n} ∩ Y) ∧
	{k|k < i + 1 ∧ k < m + n} \ X =
	({k|k < i ∧ k < m + n} \ X) ∧
	{k|k < i + 1 ∧ k < m + n} \ Y =
	{i} ∪ ({k|k < i ∧ k < m + n} \ Y)⌝
	rewrite_thm_tac);
(* *** Goal "1.1.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1
	THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.1.1.1" *** *)
a(cases_tac⌜x = i⌝ THEN1 all_var_elim_asm_tac1);
a(lemma_tac⌜x < i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.1.1.2" *** *)
a(cases_tac⌜x = i⌝ THEN1 all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.1.2" *** *)
a(LEMMA_T⌜
	{k|k < i ∧ k < m + n} ∩ X =
	({k|k < i ∧ k < m + n} ∩ Y) ∧
	{k|k < i ∧ k < m + n} \ X =
	({k|k < i ∧ k < m + n} \ Y)⌝
	rewrite_thm_tac);
(* *** Goal "1.2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY ALL_ASM_FC_T1 fc_⇔_canon (MAP_EVERY strip_asm_tac)[]);
(* *** Goal "1.1.2.2" *** *)
a(strip_asm_tac(∀_elim⌜i⌝ range_finite_size_thm));
a(lemma_tac⌜
	({k|k < i ∧ k < m + n} ∩ Y) ∈ Finite ∧
	({k|k < i ∧ k < m + n} \ Y) ∈ Finite⌝
	THEN1 (REPEAT strip_tac
		THEN bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜{j|j < i}⌝ THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜
	¬i ∈ ({k|k < i ∧ k < m + n} ∩ Y) ∧
	¬i ∈ ({k|k < i ∧ k < m + n} \ Y)⌝ (∧_THEN asm_tac)
	THEN1 (REPEAT strip_tac
		THEN PC_T1 "lin_arith" prove_tac[]));
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "1.2" *** *)
a(swap_nth_asm_concl_tac 3);
a(LEMMA_T⌜
	{k|k < i + 1 ∧ k < m + n} ∩ Y =
	{i} ∪ ({k|k < i ∧ k < m + n} ∩ Y) ∧
	{k|k < i + 1 ∧ k < m + n} ∩ X =
	({k|k < i ∧ k < m + n} ∩ X) ∧
	{k|k < i + 1 ∧ k < m + n} \ Y =
	({k|k < i ∧ k < m + n} \ Y) ∧
	{k|k < i + 1 ∧ k < m + n} \ X =
	{i} ∪ ({k|k < i ∧ k < m + n} \ X)⌝
	rewrite_thm_tac);
(* *** Goal "1.2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1
	THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.1.1" *** *)
a(cases_tac⌜x = i⌝ THEN1 all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.1.2" *** *)
a(cases_tac⌜x = i⌝ THEN1 all_var_elim_asm_tac1);
a(lemma_tac⌜x < i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(LEMMA_T⌜
	{k|k < i ∧ k < m + n} ∩ X =
	({k|k < i ∧ k < m + n} ∩ Y) ∧
	{k|k < i ∧ k < m + n} \ X =
	({k|k < i ∧ k < m + n} \ Y)⌝
	rewrite_thm_tac);
(* *** Goal "1.2.2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY ALL_ASM_FC_T1 fc_⇔_canon (MAP_EVERY strip_asm_tac)[]);
(* *** Goal "1.2.2.2" *** *)
a(strip_asm_tac(∀_elim⌜i⌝ range_finite_size_thm));
a(lemma_tac⌜
	({k|k < i ∧ k < m + n} ∩ Y) ∈ Finite ∧
	({k|k < i ∧ k < m + n} \ Y) ∈ Finite⌝
	THEN1 (REPEAT strip_tac
		THEN bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜{j|j < i}⌝ THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜
	¬i ∈ ({k|k < i ∧ k < m + n} ∩ Y) ∧
	¬i ∈ ({k|k < i ∧ k < m + n} \ Y)⌝ (∧_THEN asm_tac)
	THEN1 (REPEAT strip_tac
		THEN PC_T1 "lin_arith" prove_tac[]));
a(ALL_FC_T rewrite_tac[size_singleton_∪_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(rename_tac[(⌜x'⌝, "s")] THEN ∃_tac⌜a⌝
	THEN asm_rewrite_tac[]);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[
	pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜∀x y z w:ℤ⦁x + ~y = z + ~w ⇔ x + w = z + y⌝,
	ℕℤ_plus_homomorphism_thm1, ℕℤ_one_one_thm]);
a(LEMMA_T ⌜{k|k < m + n} ∩ a = a⌝ rewrite_thm_tac);
(* *** Goal "2.1.1" *** *)
a(REPEAT strip_tac THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(DROP_NTH_ASM_T 5 ante_tac);
a(lemma_tac ⌜
	a ⊆ {i|i < m + n} ∧
	({k|k < m + n} \ a) ⊆ {i|i < m + n} ∧
	a ∩ ({k|k < m + n} \ a) = {} ∧
	{k|k < m + n}  = a ∪ ({k|k < m + n} \ a)⌝ 
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(POP_ASM_T (fn th => conv_tac( LEFT_C(once_rewrite_conv[th]))));
a(all_fc_tac[⊆_finite_thm]);
a(ante_tac(list_∀_elim[⌜a⌝, ⌜{k|k < m + n} \ a⌝] size_∪_thm));
a(asm_rewrite_tac[size_empty_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2.2" *** *)
a(rename_tac[(⌜x'⌝, "s"), (⌜x''⌝, "a")] THEN ∃_tac⌜a:ℕ SET⌝
	THEN asm_rewrite_tac[]);
a(rewrite_tac[
	pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜∀x y z w:ℤ⦁x + ~y = z + ~w ⇔ x + w = z + y⌝,
	ℕℤ_plus_homomorphism_thm1, ℕℤ_one_one_thm]);
a(LEMMA_T ⌜{k|k < m + n} ∩ a = a⌝ rewrite_thm_tac);
(* *** Goal "2.2.1" *** *)
a(REPEAT strip_tac THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac ⌜
	a ⊆ {i|i < m + n} ∧
	({k|k < m + n} \ a) ⊆ {i|i < m + n} ∧
	a ∩ ({k|k < m + n} \ a) = {} ∧
	a ∪ ({k|k < m + n} \ a) = {k|k < m + n}⌝ 
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(ante_tac(list_∀_elim[⌜a⌝, ⌜{k|k < m + n} \ a⌝] size_∪_thm));
a(asm_rewrite_tac[size_empty_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_to_empty_thm⦎ = save_thm ( "walk_to_empty_thm", (
set_goal([], ⌜∀n x y⦁ 
	(∀p q⦁ ¬(p + q = n ∧ y = x + ℕℤ p - ℕℤ q))
⇔	WalkTo n x y = {}
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[walk_to_thm] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(POP_ASM_T (ante_tac o ∀_elim⌜n⌝)
	THEN rewrite_tac[] THEN contr_tac);
a(DROP_NTH_ASM_T 3 (ante_tac o list_∀_elim[
	⌜# ({k|k < n} ∩ a)⌝,
	⌜# ({k|k < n} \ a)⌝]));
a(asm_rewrite_tac[]);
a(lemma_tac⌜
	({k|k < n} ∩ a) ⊆ {k|k < n}
∧	({k|k < n } \ a) ⊆ {k|k < n}
∧	({k|k < n} ∩ a) ∩ ({k|k < n} \ a) = {}
∧	{k|k < n} = ({k|k < n} ∩ a) ∪ ({k|k < n} \ a)⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(strip_asm_tac(∀_elim⌜n⌝ range_finite_size_thm));
a(POP_ASM_T ante_tac);
a(DROP_NTH_ASM_T 2 (fn th => conv_tac (LEFT_C(once_rewrite_conv[th]))));
a(all_fc_tac[⊆_finite_thm]);
a(LEMMA_T ⌜# ({k|k < n} ∩ a ∪ {k|k < n} \ a) =
	# ({k|k < n} ∩ a ∪ {k|k < n} \ a) +
	# (({k|k < n} ∩ a) ∩ ({k|k < n} \ a))⌝
	once_rewrite_thm_tac
	THEN1 (asm_rewrite_tac[size_empty_thm]));
a(ALL_FC_T rewrite_tac[size_∪_thm]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 2 ante_tac);
a(PC_T1 "sets_ext1" rewrite_tac[]);
a(rewrite_tac[walk_to_def, walk_def1]);
a(REPEAT strip_tac);
a(swap_nth_asm_concl_tac 1 THEN strip_tac
	THEN all_var_elim_asm_tac1);
a(∃_tac⌜λk⦁
	if k ≤ p
	then x + ℕℤ k
	else if k ≤ p + q
	then x + ℕℤ 2 * ℕℤ p - ℕℤ k
	else x + ℕℤ p - ℕℤ q⌝);
a(rewrite_tac[] THEN REPEAT
	(∧_tac ORELSE ∀_tac ORELSE ⇒_tac));
(* *** Goal "2.1" *** *)
a(LEMMA_T⌜m ≤ p + q ∧ m + 1 ≤ p + q⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(cases_tac⌜m + 1 ≤ p⌝ THEN asm_rewrite_tac[ℕℤ_plus_homomorphism_thm]);
(* *** Goal "2.1.1" *** *)
a(∨_left_tac);
a(LEMMA_T⌜m ≤ p⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(PC_T1 "ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(∨_right_tac);
a(cases_tac ⌜m = p⌝
	THEN1 (asm_rewrite_tac[]
		THEN PC_T1 "ℤ_lin_arith" prove_tac[]));
a(LEMMA_T⌜¬m ≤ p⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(PC_T1 "ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.2" *** *)
a(cases_tac⌜q = 0⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
a(all_var_elim_asm_tac1 THEN POP_ASM_T ante_tac
	THEN rewrite_tac[] THEN strip_tac);
a(cases_tac⌜m = p⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜¬m ≤ p⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(LEMMA_T⌜¬m ≤ p⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(cases_tac⌜m = p + q⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜¬m ≤ p + q⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(rewrite_tac[ℕℤ_plus_homomorphism_thm]);
a(PC_T1 "ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.3" *** *)
a(cases_tac⌜q = 0⌝ THEN asm_rewrite_tac[ℕℤ_plus_homomorphism_thm]
	THEN PC_T1 "ℤ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_to_finite_thm⦎ = save_thm ( "walk_to_finite_thm", (
set_goal([], ⌜∀n x y⦁ 
	WalkTo n x y ∈ Finite
⌝);
a(REPEAT strip_tac
	THEN cases_tac⌜∀ p q⦁ ¬ (p + q = n ∧ y = x + ℕℤ p - ℕℤ q)⌝);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac [walk_to_empty_thm]);
a(rewrite_tac[empty_finite_thm]);
a(all_var_elim_asm_tac1);
a(rewrite_tac[walk_to_finite_size_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_walk_to_thm⦎ = save_thm ( "walk_walk_to_thm", (
set_goal([], ⌜∀m n x s⦁ 
	m ≤ n
∧	s ∈ Walk n x
⇒	(λk⦁if k ≤ m then s k else s m) ∈ WalkTo m x (s m)
⌝);
a(rewrite_tac[walk_def1, walk_to_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac);
a(LEMMA_T⌜m' + 1 ≤ m ∧ m' ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(lemma_tac⌜m' < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac);
a(spec_nth_asm_tac 5 ⌜m'⌝);
(* *** Goal "2" *** *)
a(cases_tac⌜m' ≤ m⌝ THEN asm_rewrite_tac[]);
a(LEMMA_T⌜m' = m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_shift_thm⦎ = save_thm ( "walk_shift_thm", (
set_goal([], ⌜∀m n x⦁ 
	s ∈ Walk (m + n) x
⇒	(λk⦁s (k + m)) ∈ Walk n (s m)
⌝);
a(rewrite_tac[walk_def1] THEN REPEAT (⇒_tac ORELSE ∀_tac ORELSE ∧_tac));
(* *** Goal "1" *** *)
a(LEMMA_T⌜(m' + 1) + m = (m' + m) + 1⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" prove_tac[]);
a(LEMMA_T ⌜m' + m < m + n⌝ asm_tac
	THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [4] fc_tac
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜m + n ≤ m' + m⌝ asm_tac
	THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T[3] (ALL_FC_T rewrite_tac));
a(LEMMA_T⌜m + n = n + m⌝ rewrite_thm_tac THEN rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_minus_thm⦎ = save_thm ( "walk_minus_thm", (
set_goal([], ⌜∀s n x⦁ 
	s ∈ Walk n x
⇒	(λk⦁~(s k)) ∈ Walk n (~x)
⌝);
a(rewrite_tac[walk_def1] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac);
a(rewrite_tac[pc_rule1 "ℤ_lin_arith" prove_rule[]
		⌜∀x y z:ℤ⦁~x + y = z ⇔ x + ~y = ~z⌝]);
a(REPEAT strip_tac THEN spec_nth_asm_tac 4 ⌜m⌝);
(* *** Goal "3" *** *)
a(LIST_DROP_NTH_ASM_T [2] (ALL_FC_T asm_rewrite_tac));
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_to_minus_thm⦎ = save_thm ( "walk_to_minus_thm", (
set_goal([], ⌜∀s n x y⦁ 
	s ∈ WalkTo n x y
⇒	(λk⦁~(s k)) ∈ WalkTo n (~x) (~y)
⌝);
a(rewrite_tac[walk_to_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[walk_minus_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏walk_to_intermediate_value_thm⦎ = save_thm ( "walk_to_intermediate_value_thm", (
set_goal([], ⌜∀n x y s z⦁ 
	s ∈ WalkTo n x y
∧	(x ≤ z ∧ z ≤ y ∨ y ≤ z ∧ z ≤ x)
⇒	∃k⦁k ≤ n ∧ s k = z 
⌝);
a(lemma_tac⌜∀n x y s z⦁ 
	s ∈ WalkTo n x y
∧	(x ≤ z ∧ z ≤ y)
⇒	∃k⦁k ≤ n ∧ s k = z⌝);
(* *** Goal "1" *** *)
a(∀_tac THEN induction_tac⌜n:ℕ⌝
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(DROP_NTH_ASM_T 3 (strip_asm_tac o
	rewrite_rule[walk_def1, walk_to_def]));
a(all_var_elim_asm_tac1);
a(∃_tac⌜0⌝ THEN rewrite_tac[]
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(GET_NTH_ASM_T 3 (strip_asm_tac o
	rewrite_rule[walk_def1, walk_to_def]));
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜n⌝));
(* *** Goal "1.2.1" *** *)
a(cases_tac⌜z = y⌝
	THEN1 (∃_tac⌜n+1⌝ THEN asm_rewrite_tac[]));
a(lemma_tac⌜z ≤ s n⌝ THEN1 PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(ante_tac (list_∀_elim[⌜n⌝, ⌜n+1⌝]walk_walk_to_thm)
	THEN rewrite_tac[]);
a(GET_NTH_ASM_T 9 (strip_asm_tac o
	rewrite_rule[walk_to_def]));
a(STRIP_T (fn th => all_fc_tac[th]));
a(DROP_NTH_ASM_T 12 (fn th => all_fc_tac[th]));
a(∃_tac⌜k⌝ THEN POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(lemma_tac⌜z ≤ s n ∧ s 0 ≤ s n ⌝ THEN1 PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(ante_tac (list_∀_elim[⌜n⌝, ⌜n+1⌝]walk_walk_to_thm)
	THEN rewrite_tac[]);
a(GET_NTH_ASM_T 9 (strip_asm_tac o
	rewrite_rule[walk_to_def]));
a(STRIP_T (fn th => all_fc_tac[th]));
a(DROP_NTH_ASM_T 12 (fn th => all_fc_tac[th]));
a(∃_tac⌜k⌝ THEN POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(all_fc_tac[walk_to_minus_thm]);
a(lemma_tac⌜~x ≤ ~z ∧ ~z ≤ ~y⌝ THEN1 PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(∃_tac⌜k⌝ THEN POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a(PC_T1 "ℤ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_goal([], ⌜∀p q; x y z w:ℤ⦁
	((x = if p then y else z)
⇔	(if p then x = y else x = z))
∧	((x = ~(if p then y else z))
⇔	(if p then x = ~y else x = ~z))
∧	(((if p then y else z) < w)
⇔	(if p then y < w else z < w))
∧	((if p then q else T) ⇔ ¬p ∨ q)
∧	((if p then T else q) ⇔ p ∨ q)
⌝);
a(REPEAT ∀_tac THEN cases_tac⌜p:BOOL⌝
	THEN asm_rewrite_tac[]);
val ⦏if_out_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_goal([], ⌜∀p; x :ℤ⦁
	(if p then x else ~x) = ℕℤ 0 
⇔	x = ℕℤ 0⌝);
a(REPEAT ∀_tac THEN cases_tac⌜p:BOOL⌝
	THEN asm_rewrite_tac[]
	THEN PC_T1 "ℤ_lin_arith" prove_tac[]);
val ⦏if_plus_minus_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
val ⦏walk_to_reflection_thm⦎ = save_thm ( "walk_to_reflection_thm", (
set_goal([], ⌜∀m n k z⦁ 
	ℕℤ 0 < z ∧ 0 < k ∧ n < k + m
⇒	#(WalkTo (m+n) (~(ℕℤ k)) z) =
	#{s | s ∈ WalkTo (m+n) (ℕℤ k) z
		∧ ∃i⦁s i = ℕℤ 0}
⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN conv_tac eq_sym_conv);
a(bc_thm_tac (taut_rule⌜∀p⦁
	{s | s ∈ WalkTo (m+n) (ℕℤ k) z
	 ∧ ∃i⦁s i = ℕℤ 0} ∈ Finite ∧ p ⇒ p⌝));
a(MAP_EVERY ∃_tac [⌜z⌝, ⌜k⌝, ⌜n⌝, ⌜m⌝]);
a(lemma_tac⌜∀s⦁
	s ∈ WalkTo (m + n) (~ (ℕℤ k)) z
⇒	s (Min {l | s l = ℕℤ 0}) = ℕℤ 0
∧	(∀k⦁s k = ℕℤ 0 ⇒ Min {l | s l = ℕℤ 0} ≤ k)
⌝);
(* *** Goal "1" *** *)
a(REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac⌜∃j⦁j ≤ m + n ∧ s j = ℕℤ 0⌝);
(* *** Goal "1.1" *** *)
a(pure_rewrite_tac[pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜ℕℤ 0 = ~(ℕℤ k) + ℕℤ k⌝]
	THEN bc_thm_tac walk_to_intermediate_value_thm);
a(∃_tac⌜ z ⌝ THEN ∃_tac⌜~ (ℕℤ k) ⌝);
a(asm_rewrite_tac[pc_rule1 "ℤ_lin_arith" prove_rule[]
	⌜∀a b c:ℤ⦁ (~a ≤ b + ~c ⇔ c ≤ a + b)⌝,
	ℕℤ_plus_homomorphism_thm1, ℕℤ_≤_thm]);
a(REPEAT strip_tac THEN
	PC_T1 "ℤ_lin_arith" asm_prove_tac[]
	ORELSE PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(strip_asm_tac (list_∀_elim[⌜j⌝, ⌜{l | s l = ℕℤ 0}⌝] min_∈_thm)
	THEN REPEAT strip_tac);
a(strip_asm_tac (list_∀_elim[⌜k'⌝, ⌜{l | s l = ℕℤ 0}⌝] min_≤_thm)
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(bc_thm_tac bijection_finite_size_thm);
a(∃_tac⌜λs⦁λj⦁ if Min{l | s l = ℕℤ 0} ≤ j then s j else ~(s j)⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[walk_to_finite_thm]);
(* *** Goal "2.2" *** *)
a(LEMMA_T⌜∀ x'⦁
	(if Min {l|x l = ℕℤ 0} ≤ x' then x x' else ~ (x x')) = ℕℤ 0
⇔	(if Min {l|y l = ℕℤ 0} ≤ x' then y x' else ~ (y x')) = ℕℤ 0⌝ ante_tac
	THEN1 asm_rewrite_tac[]);
a(rewrite_tac[if_plus_minus_lemma] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
a(STRIP_T (ante_tac o ∀_elim⌜x'⌝));
a(cases_tac⌜Min {l|y l = ℕℤ 0} ≤ x'⌝
	THEN asm_rewrite_tac[]
	THEN PC_T1 "ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.3" *** *)
a(PC_T1"sets_ext1" REPEAT strip_tac);
(* *** Goal "2.3.1" *** *)
a(rename_tac[(⌜x⌝, "s")]
	THEN ∃_tac⌜λj:ℕ⦁
		if Min {l | s l = ℕℤ 0} ≤ j
		then s j
		else ~(s j)⌝);
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[walk_def1, walk_to_def]
	THEN strip_tac);
a(lemma_tac⌜Min {l|s l = ℕℤ 0} ≤ m + n⌝);
(* *** Goal "2.3.1.1" *** *)
a(bc_thm_tac ≤_trans_thm);
a(cases_tac⌜i ≤ m + n⌝ 
	THEN1 (∃_tac⌜i⌝ THEN REPEAT strip_tac
		THEN bc_thm_tac min_≤_thm
		THEN REPEAT strip_tac));
a(lemma_tac⌜m + n ≤ i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(∃_tac⌜m+n⌝ THEN REPEAT strip_tac);
a(bc_thm_tac min_≤_thm THEN rewrite_tac[]);
a(SPEC_NTH_ASM_T 4 ⌜i⌝ ante_tac);
a(POP_ASM_T rewrite_thm_tac);
a(STRIP_T (rewrite_thm_tac o eq_sym_rule));
a(REPEAT strip_tac);
(* *** Goal "2.3.1.2" *** *)
a(REPEAT (∧_tac ORELSE ∀_tac ORELSE ⇒_tac)
	THEN1 asm_rewrite_tac[]);
(* *** Goal "2.3.1.2.1" *** *)
a(LEMMA_T ⌜¬Min {l|s l = ℕℤ 0} = 0⌝ rewrite_thm_tac
	THEN contr_tac);
a(ante_tac (list_∀_elim[⌜i⌝, ⌜{l | s l = ℕℤ 0}⌝] min_∈_thm));
a(asm_rewrite_tac[ℕℤ_one_one_thm]
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.3.1.2.2" *** *)
a(CASES_T ⌜Min {l|s l = ℕℤ 0} ≤ m'⌝
	(fn th => rewrite_thm_tac th 
		THEN strip_asm_tac th));
(* *** Goal "2.3.1.2.2.1" *** *)
a(LEMMA_T⌜Min {l|s l = ℕℤ 0} ≤ m' + 1⌝
	rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 6 ⌜m'⌝
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.3.1.2.2.2" *** *)
a(CASES_T ⌜Min {l|s l = ℕℤ 0} ≤ m' + 1⌝
	(fn th => rewrite_thm_tac th 
		THEN strip_asm_tac th));
(* *** Goal "2.3.1.2.2.2.1" *** *)
a(lemma_tac⌜Min {l|s l = ℕℤ 0} = m' + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(ante_tac (list_∀_elim[⌜i⌝, ⌜{l | s l = ℕℤ 0}⌝] min_∈_thm));
a(asm_rewrite_tac[] THEN strip_tac);
a(SPEC_NTH_ASM_T 9 ⌜m'⌝ ante_tac);
a(LIST_GET_NTH_ASM_T [1, 5] rewrite_tac);
a(PC_T1"ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.3.1.2.2.2.2" *** *)
a(SPEC_NTH_ASM_T 7 ⌜m'⌝ ante_tac);
a(LIST_GET_NTH_ASM_T [3] rewrite_tac);
a(PC_T1"ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.3.1.2.3" *** *)
a(LEMMA_T⌜Min {l|s l = ℕℤ 0} ≤ m'⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "2.3.1.2.4" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2.3.1.2.5" *** *)
a(rewrite_tac[if_plus_minus_lemma, if_out_lemma]);
a(cases_tac⌜Min {l|s l = ℕℤ 0} ≤ x''⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "2.3.2" *** *)
a(rename_tac[(⌜x'⌝, "s")]
	THEN DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜s:ℕ→ℤ⌝));
a(DROP_NTH_ASM_T 4 ante_tac THEN rewrite_tac[walk_def1, walk_to_def]
	THEN strip_tac);
a(lemma_tac⌜Min {l|s l = ℕℤ 0} ≤ m + n⌝);
(* *** Goal "2.3.2.1" *** *)
a(bc_thm_tac ≤_trans_thm);
a(cases_tac⌜Min {l|s l = ℕℤ 0} ≤ m + n⌝ 
	THEN1 (∃_tac⌜Min {l|s l = ℕℤ 0}⌝
		THEN REPEAT strip_tac
		THEN bc_thm_tac min_≤_thm
		THEN REPEAT strip_tac));
a(lemma_tac⌜m + n ≤ Min {l|s l = ℕℤ 0}⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(∃_tac⌜m+n⌝ THEN REPEAT strip_tac);
a(bc_thm_tac min_≤_thm THEN rewrite_tac[]);
a(SPEC_NTH_ASM_T 4 ⌜Min {l|s l = ℕℤ 0}⌝ ante_tac);
a(POP_ASM_T rewrite_thm_tac);
a(STRIP_T (rewrite_thm_tac o eq_sym_rule));
a(REPEAT strip_tac);
(* *** Goal "2.3.2.2" *** *)
a(REPEAT (∧_tac ORELSE ∀_tac ORELSE ⇒_tac)
	THEN asm_rewrite_tac[]);
(* *** Goal "2.3.2.2.1" *** *)
a(LEMMA_T ⌜¬Min {l|s l = ℕℤ 0} = 0⌝ rewrite_thm_tac);
a(swap_nth_asm_concl_tac 7 THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜ℕℤ 0 < ℕℤ k⌝ ante_tac	
	THEN1 asm_rewrite_tac[ℕℤ_less_thm]);
a(PC_T1"ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.3.2.2.2" *** *)
a(CASES_T ⌜Min {l|s l = ℕℤ 0} ≤ m'⌝
	(fn th => rewrite_thm_tac th 
		THEN strip_asm_tac th));
(* *** Goal "2.3.2.2.2,1" *** *)
a(LEMMA_T⌜Min {l|s l = ℕℤ 0} ≤ m' + 1⌝
	rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 6 ⌜m'⌝
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.3.2.2.2.2" *** *)
a(CASES_T ⌜Min {l|s l = ℕℤ 0} ≤ m' + 1⌝
	(fn th => rewrite_thm_tac th 
		THEN strip_asm_tac th));
a(lemma_tac⌜Min {l|s l = ℕℤ 0} = m' + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 11 ante_tac);
a(asm_rewrite_tac[] THEN strip_tac);
a(SPEC_NTH_ASM_T 9 ⌜m'⌝ ante_tac);
a(LIST_GET_NTH_ASM_T [1, 5] rewrite_tac);
a(PC_T1"ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.3.2.2.2.2.2" *** *)
a(SPEC_NTH_ASM_T 7 ⌜m'⌝ ante_tac);
a(LIST_GET_NTH_ASM_T [3] rewrite_tac);
a(PC_T1"ℤ_lin_arith" prove_tac[]);
(* *** Goal "2.3.2.3" *** *)
a(LEMMA_T⌜Min {l|s l = ℕℤ 0} ≤ m'⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "2.3.3" *** *)
a(rename_tac[(⌜x'⌝, "s")]
	THEN DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜s:ℕ→ℤ⌝));
a(∃_tac⌜Min {l|s l = ℕℤ 0}⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ballot_lemma1⦎ = save_thm ( "ballot_lemma1", (
set_goal([], ⌜∀m n y⦁
	#{s | s ∈ WalkTo (m+n+1) (ℕℤ 0) y ∧ ∀i⦁ℕℤ 0 < s (i+1)} =
	#{s | s ∈ WalkTo (m+n) (ℕℤ 1) y ∧ ∀ i⦁ ℕℤ 0 < s i}
⌝);
a(REPEAT ∀_tac);
a(bc_thm_tac (taut_rule⌜∀p⦁
	{s | s ∈ WalkTo (m+n+1) (ℕℤ 0) y ∧ ∀i⦁ℕℤ 0 < s (i+1)} ∈ Finite ∧ p ⇒ p⌝));
a(MAP_EVERY ∃_tac [⌜y⌝, ⌜n⌝, ⌜m⌝]);
a(bc_thm_tac bijection_finite_size_thm1);
a(∃_tac⌜λs⦁λk⦁s(k+1)⌝);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ⊆_finite_thm
	THEN ∃_tac⌜ WalkTo (m + n) (ℕℤ 1) y ⌝
	THEN rewrite_tac[walk_to_finite_thm]
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o rewrite_rule[walk_def1, walk_to_def]));
a(DROP_NTH_ASM_T 8 (strip_asm_tac o rewrite_rule[walk_def1, walk_to_def]));
a(strip_asm_tac(∀_elim⌜x'⌝ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(rewrite_tac[]);
a(lemma_tac⌜∃s⦁s 0 = ℕℤ 0 ∧ ∀k⦁s(k+1) = x k⌝
	THEN1 prove_∃_tac);
a(∃_tac⌜s⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 ante_tac
	THEN rewrite_tac[walk_to_def, walk_def1]
	THEN REPEAT (∀_tac ORELSE ⇒_tac ORELSE ∧_tac)
	THEN1 asm_rewrite_tac[]);
(* *** Goal "3.1" *** *)
a(strip_asm_tac(∀_elim⌜m'⌝ ℕ_cases_thm)
	THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 5 bc_thm_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3.2" *** *)
a(POP_ASM_T (strip_asm_tac o 
	once_rewrite_rule[plus_comm_thm] o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1 THEN asm_rewrite_tac[plus_assoc_thm1]);
a(POP_ASM_T bc_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3.3" *** *)
a(asm_rewrite_tac[plus_assoc_thm1]);
(* *** Goal "4" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[walk_to_def, plus_assoc_thm]
	THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[walk_def1]));
a(DROP_NTH_ASM_T 2 (ante_tac o ∀_elim⌜0⌝));
a(asm_rewrite_tac[plus_assoc_thm1]);
a(REPEAT strip_tac);
(* *** Goal "4.1" *** *)
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac walk_shift_thm);
a(∃_tac⌜ℕℤ 0⌝ THEN asm_rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜1 + m + n = m + n + 1⌝]);
(* *** Goal "4.2" *** *)
a(SPEC_NTH_ASM_T 6 ⌜0⌝ ante_tac);
a(POP_ASM_T rewrite_thm_tac);
(* *** Goal "5" *** *)
a(all_var_elim_asm_tac1 THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ballot_lemma2⦎ = save_thm ( "ballot_lemma2", (
set_goal([], ⌜∀m n⦁ 
	0 < n ∧ n < m + 1
⇒	ℕℝ(#{s | s ∈ WalkTo (m+n+1) (ℕℤ 0) (ℕℤ (m+1) - ℕℤ n)
		∧ ∀i⦁ℕℤ 0 < s (i+1)}) =
	ℕℝ(Binomial (m + n) m) - ℕℝ(Binomial (m+n) (m+1))⌝);
a(REPEAT strip_tac);
a(pure_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀x y z:ℝ⦁x = y - z ⇔ y = x + z⌝,
	ℕℝ_plus_homomorphism_thm1, ℕℝ_one_one_thm,
	ballot_lemma1]);
a(strip_asm_tac (∀_elim ⌜m⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rename_tac[(⌜i:ℕ⌝, "M")]
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(strip_asm_tac (∀_elim ⌜n⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rename_tac[(⌜i:ℕ⌝, "N")]);
a(pure_rewrite_tac[
	conv_rule(ONCE_MAP_C eq_sym_conv)
		(list_∀_elim[⌜ℕℤ 1⌝, ⌜M+1⌝, ⌜N+1⌝]
			walk_to_finite_size_thm),
	rewrite_rule[pc_rule1"lin_arith" prove_rule[]
		⌜((M+1)+1)+N = ((M+1)+N+1)⌝]
	(conv_rule(ONCE_MAP_C eq_sym_conv)
		(list_∀_elim[⌜~(ℕℤ 1)⌝, ⌜(M+1)+1⌝, ⌜N⌝]
			walk_to_finite_size_thm))]);
a(rewrite_tac[ℕℤ_plus_homomorphism_thm]
	THEN conv_tac (ONCE_MAP_C ℤ_anf_conv));
a(ante_tac(
	list_∀_elim[⌜M+1⌝, ⌜N+1⌝, ⌜1⌝,
			⌜ℕℤ 1 + ℕℤ M + ~ (ℕℤ N)⌝]
	walk_to_reflection_thm));
a(LEMMA_T⌜ℕℤ 0 < ℕℤ 1 + ℕℤ M + ~(ℕℤ N)⌝ asm_rewrite_thm_tac
	THEN1 asm_rewrite_tac[pc_rule1"ℤ_lin_arith" prove_rule[]
	⌜∀a b c ⦁ ℕℤ 0 < a + b + ~c ⇔ c < b + a⌝,
	ℕℤ_plus_homomorphism_thm1, ℕℤ_less_thm]);
a(STRIP_T rewrite_thm_tac);
a(bc_thm_tac size_disjoint_∪_thm);
a(rewrite_tac[walk_to_finite_thm]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(GET_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[walk_to_def]));
a(lemma_tac⌜∃j⦁j ≤ (M+1) + N + 1 ∧ x j ≤ ℕℤ 0⌝
	THEN cases_tac⌜M' ≤ (M+1)+N+1⌝
	THEN1 (∃_tac⌜M'⌝
		THEN REPEAT strip_tac
		THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]));
(* *** Goal "1.1" *** *)
a(∃_tac⌜(M+1)+N+1⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o rewrite_rule[walk_def1]));
a(lemma_tac⌜(M+1)+N+1 ≤ M'⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 7 ante_tac);
a(LIST_DROP_NTH_ASM_T [2] (ALL_FC_T rewrite_tac));
(* *** Goal "1.2" *** *)
a(LIST_DROP_NTH_ASM_T [1, 6] discard_tac);
a(all_fc_tac[walk_walk_to_thm]);
a(LEMMA_T⌜ℕℤ 0 ≤ ℕℤ 1⌝ asm_tac THEN1 rewrite_tac[]);
a(all_fc_tac[walk_to_intermediate_value_thm]);
a(∃_tac⌜k⌝ THEN POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a(all_fc_tac[walk_walk_to_thm]);
a(LEMMA_T⌜ℕℤ 0 ≤ ℕℤ 1⌝ asm_tac THEN1 rewrite_tac[]);
a(all_fc_tac[walk_to_intermediate_value_thm]);
a(∃_tac⌜k⌝ THEN POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(SPEC_NTH_ASM_T 2 ⌜i⌝ ante_tac);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀m n k⦁
	(ℕℝ(m!) * ℕℝ(n!) ⋏-⋏1 * ℕℝ(k!) ⋏-⋏1) ⋏-⋏1 = ℕℝ(m!) ⋏-⋏1 * ℕℝ(n!) * ℕℝ(k!)⌝);
a(REPEAT ∀_tac);
a(strip_asm_tac(∀_elim⌜n⌝ factorial_not_0_thm));
a(strip_asm_tac(∀_elim⌜k⌝ factorial_not_0_thm));
a(all_fc_tac[ℝ_¬_recip_0_thm]);
a(strip_asm_tac(∀_elim⌜m⌝ factorial_not_0_thm));
a(lemma_tac ⌜¬ℕℝ(n!) ⋏-⋏1 * ℕℝ(k!) ⋏-⋏1 = ℕℝ 0⌝
	THEN1 asm_rewrite_tac[ℝ_times_eq_0_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
val  ⦏ballot_lemma3a⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
val ⦏ballot_lemma3⦎ = save_thm ( "ballot_lemma3", (
set_goal([], ⌜∀m n⦁
	0 < n ∧ n < m + 1
⇒	(ℕℝ (Binomial (m + n) m) - ℕℝ (Binomial (m + n) (m + 1))) *
	ℕℝ(Binomial (m+n+1) (m+1)) ⋏-⋏1 =
	((m + 1) - n) / ((m+1) + n) ⌝);
a(REPEAT strip_tac);
a(rewrite_tac[ℝ_frac_def]);
a(lemma_tac⌜¬ℕℝ((m+1)+n) = ℕℝ 0⌝
	THEN1 (rewrite_tac[ℕℝ_one_one_thm]
		THEN PC_T1"lin_arith" asm_prove_tac[]));
a(ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[conv_rule(ONCE_MAP_C (RIGHT_C eq_sym_conv)) ℝ_times_cancel_thm]);
a(rewrite_tac[ℝ_times_assoc_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(POP_ASM_T discard_tac);
a(LEMMA_T⌜1 ≤ n ∧ n ≤ m⌝ (strip_asm_tac o
	once_rewrite_rule[plus_comm_thm] o
	rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN all_var_elim_asm_tac1);
a(rename_tac[(⌜i'⌝, "M"), (⌜i⌝, "N")]
	THEN rewrite_tac[binomial_factorial_thm]);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(M + N + 1) + N + 1 = ((M + N + 1) + 1) + N
	∧ ((M + N + 1) + (N + 1) + 1) = ((M + N + 1) + 1) + (N+1)⌝,
	binomial_factorial_thm]);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(M + N + 1) + 1 = (M + 1) + (N + 1)⌝,
	ℝ_times_plus_distrib_thm]);
a(rewrite_tac[ballot_lemma3a]);
a(rewrite_tac[∀_elim⌜ℕℝ((((M + 1) + N + 1) + N + 1)!) ⋏-⋏1⌝
	ℝ_times_order_thm]);
a(rewrite_tac[∀_elim⌜ℕℝ(((M + 1) + N + 1) + N + 1)⌝
	ℝ_times_order_thm]);
a(rewrite_tac[ℝ_times_assoc_thm1,
	plus_assoc_thm1,
	factorial_times_recip_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y:ℝ⦁x * ~y = ~(x*y)⌝,
	ℝ_times_assoc_thm1,
	factorial_times_thm]);
a(rewrite_tac[∀_elim⌜ℕℝ((N + 1)!)⌝	ℝ_times_order_thm]);
a(rewrite_tac[∀_elim⌜ℕℝ((N + 1)!) ⋏-⋏1⌝	ℝ_times_order_thm]);
a(rewrite_tac[ℝ_times_assoc_thm1,
	factorial_times_thm]);
a(rewrite_tac[∀_elim⌜ℕℝ((((M + 1) + N) + 1)!)⌝ ℝ_times_order_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y:ℝ ⦁ ~(x*y) = x * ~y⌝,
	∀_elim⌜ℕℝ((((M + 1) + N) + 1)!) ⋏-⋏1⌝ ℝ_times_order_thm]);
a(rewrite_tac[ℝ_times_assoc_thm1,
	factorial_times_thm]);
a(conv_tac(ONCE_MAP_C (LEFT_C(RAND_C (eq_match_conv (∧_right_elim factorial_def))))));
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y:ℝ ⦁ x * ~y = ~(x * y)⌝,
pc_rule1 "lin_arith" prove_rule[]
	⌜(M + 1) + N = (M + N) + 1⌝,
	ℝ_times_assoc_thm,
	ℕℝ_times_homomorphism_thm,
	factorial_times_thm]);
a(rewrite_tac[ℕℝ_plus_homomorphism_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ballot_lemma4⦎ = save_thm ( "ballot_lemma4", (
set_goal([], ⌜∀m n⦁
	¬ #(WalkTo (m + n) (ℕℤ 0) (ℕℤ m - ℕℤ n)) = 0
⌝);
a(REPEAT ∀_tac);
a(lemma_tac⌜WalkTo (m + n) (ℕℤ 0) (ℕℤ m - ℕℤ n) ∈ Finite⌝
	THEN1 rewrite_tac[walk_to_finite_thm]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[size_0_thm]);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) walk_to_empty_thm]);
a(REPEAT strip_tac THEN ∃_tac⌜m⌝);
a(REPEAT strip_tac THEN ∃_tac⌜n⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ballot_lemma5⦎ = save_thm ( "ballot_lemma5", (
set_goal([], ⌜∀m⦁
	let	S = WalkTo m (ℕℤ 0) (ℕℤ m)
	in let	X = {s | s ∈ S ∧ ∀ i⦁ ℕℤ 0 < s (i+1)}
	in	0 < m ⇒ X = S
⌝);
a(rewrite_tac[let_def] THEN REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN rewrite_tac[]);
a(REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜ℕℤ 0⌝, ⌜m⌝, ⌜0⌝]
	walk_to_finite_size_thm));
a(rewrite_tac[binomial_eq_thm]);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[size_1_thm]);
a(REPEAT strip_tac);
a(lemma_tac⌜(λk⦁if k ≤ m then ℕℤ k else ℕℤ m) ∈ WalkTo m (ℕℤ 0) (ℕℤ m)⌝
	THEN1 rewrite_tac[walk_to_def, walk_def1]
	THEN REPEAT (∀_tac ORELSE ⇒_tac ORELSE ∧_tac));
(* *** Goal "1" *** *)
a(LEMMA_T ⌜m' + 1 ≤ m ∧ m' ≤ m⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(rewrite_tac[ℕℤ_plus_homomorphism_thm]);
a(PC_T1 "ℤ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜m' = m⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜¬m' ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(DROP_NTH_ASM_T 2 (fn th =>
	all_asm_ante_tac THEN rewrite_tac[th]
	THEN REPEAT strip_tac));
a(POP_ASM_T (asm_rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(cases_tac⌜i + 1 ≤ m⌝ THEN asm_rewrite_tac[ℕℤ_less_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ballot_thm⦎ = save_thm ( "ballot_thm", (
set_goal([], ⌜∀m n⦁
	let	S = BallotCounts m n
	in let	X = {s | s ∈ S ∧ ∀ i⦁ ℕℤ 0 < s (i+1)}
	in	S ∈ Finite
	∧	¬#S = 0
	∧	X ⊆ S
	∧	(n < m ⇒ #X / #S = (m - n) / (m + n))
⌝);
a(once_rewrite_tac[taut_rule⌜∀p1 p2 p3 p4⦁
	p1 ∧ p2 ∧ p3 ∧ p4 ⇔ p3 ∧ p1 ∧ (p1 ⇒ p2) ∧ (p1 ∧ p2 ⇒ p4)⌝]);
a(rewrite_tac[let_def, ballot_counts_def]);
a(REPEAT strip_tac THEN1 PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1" *** *)
a(rewrite_tac[walk_to_finite_thm]);
(* *** Goal "2" *** *)
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[size_0_thm]);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) walk_to_empty_thm]);
a(REPEAT strip_tac THEN ∃_tac⌜m⌝);
a(REPEAT strip_tac THEN ∃_tac⌜n⌝ THEN rewrite_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜¬ℕℝ (m + n) = ℕℝ 0
	∧ ¬ℕℝ (# (WalkTo (m + n) (ℕℤ 0) (ℕℤ m + ~ (ℕℤ n)))) = ℕℝ 0⌝
	THEN1 (rewrite_tac[ℕℝ_one_one_thm]
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(rewrite_tac[ℝ_frac_def] THEN
	ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(strip_asm_tac (∀_elim⌜n⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rename_tac[(⌜i:ℕ⌝, "N")]);
(* *** Goal "3.1" *** *)
a(DROP_NTH_ASM_T 3 (fn th =>
	all_asm_ante_tac THEN rewrite_tac[]
	THEN asm_tac th));
a(ALL_FC_T rewrite_tac[rewrite_rule[let_def] ballot_lemma5]);
a(REPEAT strip_tac THEN ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "3.2" *** *)
a(strip_asm_tac (∀_elim⌜m⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rename_tac[(⌜i:ℕ⌝, "M")]);
a(ante_tac(list_∀_elim[⌜M⌝, ⌜N+1⌝] ballot_lemma2));
a(asm_rewrite_tac[ℕℤ_plus_homomorphism_thm,
	pc_rule1 "lin_arith" prove_rule[]
	⌜(M + (N + 1) + 1) = (M + 1) + N + 1⌝]
	THEN conv_tac(ONCE_MAP_C ℤ_anf_conv));
a(STRIP_T rewrite_thm_tac);
a(ante_tac(∧_right_elim(list_∀_elim[⌜ℕℤ 0⌝, ⌜M+1⌝, ⌜N+1⌝] walk_to_finite_size_thm)));
a(asm_rewrite_tac[ℕℤ_plus_homomorphism_thm]
	THEN conv_tac(ONCE_MAP_C ℤ_anf_conv));
a(STRIP_T rewrite_thm_tac);
a(ante_tac(list_∀_elim[⌜M⌝, ⌜N+1⌝] ballot_lemma3));
a(asm_rewrite_tac [] THEN conv_tac(ONCE_MAP_C anf_conv));
a(STRIP_T rewrite_thm_tac);
a(lemma_tac⌜¬ℕℝ(2 + M + N) = ℕℝ 0⌝
	THEN1 (rewrite_tac[ℕℝ_one_one_thm]
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(rewrite_tac[ℝ_frac_def] THEN
	ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
pop_thm()
));

=TEX
=SML
set_goal([], ⌜∀ u a b⦁ Nest u ∧ a ∈ u ∧ b ∈ u ⇒ a ∪ b ∈ u⌝);
a(rewrite_tac[nest_def] THEN REPEAT strip_tac);
a(lemma_tac⌜a ⊆ b ∨ b ⊆ a⌝
	THEN1 (DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac)
	THEN ALL_FC_T asm_rewrite_tac[
		pc_rule1 "sets_ext1" prove_rule[]
			⌜∀A B⦁A ⊆ B ⇒ A ∪ B = B ∧ B ∪ A = B⌝]);
val ⦏∈_nest_∪_thm⦎ = pop_thm () (* "∈_nest_∪_thm"; *);
=TEX
=SML
set_goal([], ⌜∀ u⦁
	(∀v⦁ v ∈ u ⇒ Nest v)
∧	Nest u
⇒	Nest(⋃u)⌝);
a(REPEAT strip_tac THEN
	rewrite_tac[nest_def] THEN REPEAT_UNTIL is_∨ strip_tac);
a(LEMMA_T⌜Nest(s ∪ s')⌝(bc_thm_tac o rewrite_rule[nest_def])
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 6 bc_thm_tac);
a(all_fc_tac[∈_nest_∪_thm]);
val ⦏nest_nest_⋃_thm⦎ = pop_thm () (* "nest_nest_⋃_thm"; *);
=TEX
=SML
set_goal([], ⌜∀ u a⦁
	Nest u
∧	⋃u ⊆ a
⇒	Nest(u ∪ {a})⌝);
a(rewrite_tac[nest_def] THEN REPEAT_UNTIL is_∨ strip_tac
	THEN_TRY all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 3 discard_tac);
a(∨_left_tac THEN PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(DROP_NTH_ASM_T 3 discard_tac);
a(∨_right_tac THEN PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(REPEAT strip_tac);
val ⦏nest_∪_upb_thm⦎ = pop_thm () (* "nest_∪_upb_thm"; *);
=TEX
=SML
set_goal([], ⌜∀ u⦁
	¬ u = {}
∧	NestClosed u
⇒	(∃ a⦁ Maximal⋎⊆ u a)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃N⦁Maximal⋎⊆ {n | n ⊆ u ∧ Nest n} N⌝);
(* *** Goal "1" *** *)
a(bc_thm_tac zorn_thm1 THEN all_asm_ante_tac);
a(rewrite_tac[subset_closed_def, nest_closed_def]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac⌜{}⌝ THEN rewrite_tac[nest_def]);
(* *** Goal "1.2" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "1.3" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[nest_def]
	THEN REPEAT_UNTIL is_∨ strip_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac
	THEN PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "1.4" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.5" *** *)
a(bc_thm_tac nest_nest_⋃_thm THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜⋃N⌝ THEN POP_ASM_T ante_tac
	THEN rewrite_tac[maximal⋎⊆_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 4 (bc_thm_tac o rewrite_rule[nest_closed_def])
	THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(bc_tac(map (pc_rule1 "sets_ext1" prove_rule[])
	[⌜∀A B⦁A ⊆ B ∧ B ⊆ A ⇒ A = B⌝,
	⌜∀A U⦁ A ∈ U ⇒ A ⊆ ⋃U⌝,
	⌜∀x A⦁ A ∪ {x} = A ⇒ x ∈ A⌝])
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(asm_rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀A B C x⦁ A ⊆ A ∪ B ∧
		(A ∪ B ⊆ C ⇔ A ⊆ C ∧ B ⊆ C) ∧
		({x} ⊆ A ⇔ x ∈ A)⌝]);
a(bc_thm_tac nest_∪_upb_thm THEN REPEAT strip_tac);
val ⦏zorn_nearly_there_thm⦎ = pop_thm ();
=TEX
=SML
val ⦏zorn_thm2⦎ = save_thm ( "zorn_thm2", (
set_goal([], ⌜∀ u⦁
	¬ u = {}
∧	(∀ v⦁ ¬v = {} ∧ v ⊆ u ∧ Nest v ⇒ ⋃ v ∈ u)
⇒	(∃ a⦁ Maximal⋎⊆ u a)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃a⦁Maximal⋎⊆ (u ∪ {{}}) a⌝);
a(bc_thm_tac zorn_nearly_there_thm THEN rewrite_tac[nest_closed_def]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(bc_thm_tac (pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b⦁¬a = {} ⇒ ¬a ∪ b = {}⌝)
	THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(swap_nth_asm_concl_tac 2);
a(once_rewrite_tac[pc_rule1 "sets_ext1" prove_rule []
	⌜∀U⦁⋃U = ⋃(U \ {{}})⌝]
	THEN DROP_NTH_ASM_T 4 bc_thm_tac
	THEN REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(swap_nth_asm_concl_tac 1 THEN
	once_rewrite_tac[pc_rule1 "sets_ext1" prove_rule []
	⌜∀U⦁⋃U = ⋃(U \ {{}})⌝]
	THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2" *** *)
a(DROP_NTH_ASM_T 3 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.2.3" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[nest_def]
	THEN REPEAT_UNTIL is_∨ strip_tac);
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(∃_tac⌜a⌝ THEN POP_ASM_T ante_tac 
	THEN rewrite_tac[maximal⋎⊆_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 4 (PC_T1 "sets_ext1" strip_asm_tac)
	THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o ∀_elim⌜x⌝)
	THEN all_var_elim_asm_tac1);
(* *** Goal "2.3" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
=SML
val ⦏fund_region_thm⦎ = save_thm ( "fund_region_thm", (
set_goal([], ⌜∀f X⦁
	f ∈ Involution X
⇒	∃A⦁ 	A ⊆ X
	∧	∀x⦁
		(x ∈ A ⇒ ¬f x ∈ A)
	∧	(x ∈ X ∧ ¬x ∈ A ∧ ¬f x ∈ A ⇒ x ∈ Fixed f)
⌝);
a(rewrite_tac[involution_def, fixed_def] THEN REPEAT strip_tac);
a(LEMMA_T⌜∃A⦁ Maximal⋎⊆ {B | B ⊆ X ∧ ∀y⦁ y ∈ B ⇒ ¬f y ∈ B} A⌝
	(strip_asm_tac o rewrite_rule[maximal⋎⊆_def]));
a(bc_thm_tac zorn_thm2 THEN rewrite_tac[nest_def]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac⌜{}⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.3" *** *)
a(lemma_tac⌜s ⊆ s' ∨ s' ⊆ s⌝
	THEN1 (DROP_NTH_ASM_T 4 bc_thm_tac
		THEN REPEAT strip_tac));
(* *** Goal "1.3.1" *** *)
a(LIST_DROP_NTH_ASM_T [1] (PC_T1 "sets_ext1" all_fc_tac));
a(LIST_DROP_NTH_ASM_T [6] (PC_T1 "sets_ext1" all_fc_tac));
(* *** Goal "1.3.2" *** *)
a(LIST_DROP_NTH_ASM_T [6] (PC_T1 "sets_ext1" all_fc_tac));
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜A⌝ THEN contr_tac THEN1 all_asm_fc_tac[]);
a(swap_nth_asm_concl_tac 3);
a(LEMMA_T⌜A ∪ {x} = A⌝ (once_rewrite_thm_tac o eq_sym_rule)
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 bc_thm_tac);
a(contr_tac THEN PC_T1 "sets_ext1" asm_prove_tac[]);
a(var_elim_nth_asm_tac 1);
a(swap_nth_asm_concl_tac 3);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [6] (ALL_FC_T asm_rewrite_tac));
pop_thm()
));

=TEX
=SML
val ⦏involution_one_one_thm⦎ = save_thm ( "involution_one_one_thm", (
set_goal([], ⌜∀f X x y⦁
	f ∈ Involution X
∧	x ∈ X ∧ y ∈ X ∧ f x = f y
⇒	x = y
⌝);
a(rewrite_tac[involution_def] THEN REPEAT strip_tac);
a(LEMMA_T⌜f(f x) = f(f y)⌝ ante_tac
	THEN1 ALL_FC_T asm_rewrite_tac[]);
a(POP_ASM_T discard_tac THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏involution_def_thm1⦎ = save_thm ( "involution_def_thm1", (
set_goal([], ⌜∀f X x⦁
	f ∈ Involution X
∧	x ∈ X
⇒	f(f x) = x
⌝);
a(rewrite_tac[involution_def] THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏involution_def_thm2⦎ = save_thm ( "involution_def_thm2", (
set_goal([], ⌜∀f X x⦁
	f ∈ Involution X
∧	x ∈ X
⇒	f x ∈ X
⌝);
a(rewrite_tac[involution_def] THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏involution_size_thm⦎ = save_thm ( "involution_size_thm", (
set_goal([], ⌜∀f X⦁
	f ∈ Involution X
∧	X ∈ Finite
∧	A ⊆ X
∧	(∀x⦁x ∈ A ⇒ ¬f x ∈ A)
∧	(∀x⦁x ∈ X ⇒ x ∈ A ∨ f x ∈ A)
⇒	#X = 2 * #A
⌝);
a(REPEAT strip_tac THEN all_fc_tac[⊆_finite_thm]);
a(lemma_tac⌜X \ A ⊆ X ∧ A ∩ (X \ A) = {}⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(lemma_tac⌜X \ A ∈ Finite ∧ #(X \ A) = #A⌝
	THEN1 bc_thm_tac bijection_finite_size_thm);
(* *** Goal "1" *** *)
a(∃_tac⌜f⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(LIST_DROP_NTH_ASM_T [9] (PC_T1 "sets_ext1" all_fc_tac));
a(ALL_FC_T rewrite_tac[involution_one_one_thm]);
(* *** Goal "1.2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(∃_tac⌜f x⌝ THEN ALL_FC_T rewrite_tac[involution_def_thm1]);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
(* *** Goal "1.2.2" *** *)
a(all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [7] (PC_T1 "sets_ext1" all_fc_tac));
a(all_fc_tac[involution_def_thm2]);
(* *** Goal "1.2.3" *** *)
a(all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜X = A ∪ (X \ A)⌝ once_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(LEMMA_T ⌜#(A ∪ (X \ A)) = #(A ∪ (X \ A)) + #(A ∩ (X \ A))⌝ once_rewrite_thm_tac
	THEN1 asm_rewrite_tac[size_empty_thm]);
a(ALL_FC_T asm_rewrite_tac[size_∪_thm]
	THEN PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏involution_even_size_thm⦎ = save_thm ( "involution_even_size_thm", (
set_goal([], ⌜∀f X⦁
	f ∈ Involution X
∧	X ∈ Finite
∧	X ∩ Fixed f = {}
⇒	∃k⦁ #X = 2*k
⌝);
a(REPEAT strip_tac THEN all_fc_tac[fund_region_thm]);
a(∃_tac⌜#A⌝ THEN bc_thm_tac involution_size_thm);
a(∃_tac⌜f⌝ THEN contr_tac THEN all_asm_fc_tac[]);
a(LIST_DROP_NTH_ASM_T [1, 7] (MAP_EVERY ante_tac));
a(PC_T1 "sets_ext" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏involution_odd_size_thm⦎ = save_thm ( "involution_odd_size_thm", (
set_goal([], ⌜∀f X k⦁
	f ∈ Involution X
∧	X ∈ Finite
∧	#X = 2*k + 1
⇒	¬X ∩ Fixed f = {}
⌝);
a(contr_tac THEN all_fc_tac[involution_even_size_thm]);
a(LEMMA_T⌜(2*k + 1) Mod 2 = (2 * k') Mod 2⌝ ante_tac
	THEN1 (DROP_ASMS_T (rewrite_tac o mapfilter eq_sym_rule)));
a(rewrite_tac[mod_2_div_2_thm]);
pop_thm()
));

=TEX
=SML
val ⦏involution_set_dif_fixed_thm⦎ = save_thm ( "involution_set_dif_fixed_thm", (
set_goal([], ⌜∀f X k⦁
	f ∈ Involution X
⇒	f ∈ Involution (X \ Fixed f)
⌝);
a(PC_T1 "sets_ext1" rewrite_tac[involution_def, fixed_def]
	THEN REPEAT strip_tac
	THEN_TRY (ALL_ASM_FC_T rewrite_tac[]));
a(conv_tac(RAND_C eq_sym_conv) THEN strip_tac);
pop_thm()
));

=TEX
=SML
val ⦏involution_fixed_singleton_thm⦎ = save_thm ( "involution_fixed_singleton_thm", (
set_goal([], ⌜∀f X x⦁
	f ∈ Involution X
∧	X ∈ Finite
∧	X ∩ Fixed f = {x}
⇒	∃k⦁#X = 2*k + 1
⌝);
a(REPEAT strip_tac THEN all_fc_tac[involution_set_dif_fixed_thm]);
a(lemma_tac⌜(X \ Fixed f) ⊆ X ∧
	(X ∩ Fixed f) ⊆ X ∧
	(X \ Fixed f) ∩ Fixed f = {} ∧
	(X \ Fixed f) ∩ (X ∩ Fixed f) = {}⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(all_fc_tac[involution_even_size_thm]);
a(∃_tac ⌜k⌝);
a(LEMMA_T⌜X = (X \ Fixed f) ∪ (X ∩ Fixed f)⌝ once_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(LEMMA_T ⌜#((X \ Fixed f) ∪ (X ∩ Fixed f)) =
	#((X \ Fixed f) ∪ (X ∩ Fixed f)) +
		#((X \ Fixed f) ∩ (X ∩ Fixed f))⌝ once_rewrite_thm_tac
	THEN1 asm_rewrite_tac[size_empty_thm]);
a(ALL_FC_T asm_rewrite_tac[size_∪_thm]);
a(rewrite_tac[size_singleton_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
local
val thm1 = taut_rule ⌜∀p1 p2 p3⦁ (p1 ⇒ p2 ∧ p3) ⇒ p1 ⇒ p2⌝;
in
fun ⦏finite_bc_rule⦎ (thm : THM) = (
	all_∀_intro(simple_⇒_match_mp_rule thm1 (all_∀_elim thm))
);
end;
=SML
val ⦏ℤ_interval_finite_thm⦎ = save_thm ( "ℤ_interval_finite_thm", (
set_goal([], ⌜∀m n : ℤ⦁ {i : ℤ | m ≤ i ∧ i ≤ n} ∈ Finite⌝);
a(REPEAT strip_tac THEN cases_tac⌜m > (n:ℤ)⌝);
(* *** Goal "1" *** *)
a(LEMMA_T⌜{i|m ≤ i ∧ i ≤ n} = {}⌝
	(fn th => rewrite_tac[th, empty_finite_thm])
	THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(ℤ_≤_induction_tac⌜n⌝);
(* *** Goal "2.1" *** *)
a(LEMMA_T⌜{i|m ≤ i ∧ i ≤ m} = {m}⌝
	(fn th => rewrite_tac[th, singleton_finite_thm])
	THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(LEMMA_T⌜{n'|m ≤ n' ∧ n' ≤ n + ℕℤ 1} = {n'|m ≤ n' ∧ n' ≤ n} ∪ {n + ℕℤ 1}⌝
	(fn th => asm_rewrite_tac[th, ∪_finite_thm, singleton_finite_thm])
	THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

=SML
val ⦏ℤ_0_≤_square_thm⦎ = save_thm ( "ℤ_0_≤_square_thm", (
set_goal([], ⌜∀i : ℤ⦁ ℕℤ 0 ≤ i*i⌝);
a(REPEAT strip_tac THEN strip_asm_tac(∀_elim⌜i:ℤ⌝ℤ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN_TRY conv_tac (RIGHT_C ℤ_anf_conv)
	THEN bc_thm_tac ℤ_ℕ_times_thm
	THEN rewrite_tac[ℕℤ_≤_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

=SML
val ⦏ℤ_0_less_0_less_times_thm⦎ = save_thm ( "ℤ_0_less_0_less_times_thm", (
set_goal([], ⌜∀i j: ℤ⦁ ℕℤ 0 < i ∧ ℕℤ 0 < j ⇒ ℕℤ 0 < i*j⌝);
a(REPEAT strip_tac THEN lemma_tac⌜ℕℤ 1 ≤ i⌝
	THEN1 PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 3 discard_tac THEN ℤ_≤_induction_tac⌜i⌝
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏ℤ_0_less_times_thm⦎ = save_thm ( "ℤ_0_less_times_thm", (
set_goal([], ⌜∀i j: ℤ⦁ ℕℤ 0 < i ∧ ℕℤ 0 < j ⇒ j ≤ i * j⌝);
a(REPEAT strip_tac THEN lemma_tac⌜ℕℤ 1 ≤ i⌝
	THEN1 PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 3 discard_tac THEN ℤ_≤_induction_tac⌜i⌝
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

val ⦏ℤ_0_less_times_thm1⦎ = save_thm(
	"ℤ_0_less_times_thm1",
	conv_rule(once_rewrite_conv[ℤ_times_comm_thm]) ℤ_0_less_times_thm);
=TEX
%%%%
%%%%
=SML
val ⦏ℤ_≤_square_thm⦎ = save_thm ( "ℤ_≤_square_thm", (
set_goal([], ⌜∀i: ℤ⦁ i ≤ i*i⌝);
a(REPEAT strip_tac THEN cases_tac⌜i ≤ ℕℤ 0⌝);
(* *** Goal "1" *** *)
a(strip_asm_tac(∀_elim⌜i⌝ℤ_0_≤_square_thm)
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(bc_thm_tac ℤ_0_less_times_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
=SML
set_goal([], ⌜∀m i⦁
	¬ℕℤ 4 * m + ℕℤ 1 = ℕℤ 4 * i
⌝);
a(once_rewrite_tac[ℤ_times_comm_thm] THEN contr_tac);
a(lemma_tac⌜ℕℤ 0 = ℕℤ 1⌝
	THEN1 pure_once_rewrite_tac(map (rewrite_rule[]) [
		list_∀_elim
		[⌜m * ℕℤ 4 + ℕℤ 1⌝, ⌜ℕℤ 4⌝, ⌜m⌝, ⌜ℕℤ 1⌝]
		ℤ_div_mod_unique_thm,
		list_∀_elim
		[⌜i * ℕℤ 4⌝, ⌜ℕℤ 4⌝, ⌜i⌝, ⌜ℕℤ 0⌝]
		ℤ_div_mod_unique_thm]));
a(asm_rewrite_tac[]);
val ⦏ℤ_mod_4_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
val ⦏a_finite_thm⦎ = save_thm ( "a_finite_thm", (
set_goal([], ⌜∀p A⦁
	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
⇒	A ∈ Finite
⌝);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(bc_thm_tac ⊆_finite_thm
	THEN ∃_tac ⌜{x : ℤ | ~p ≤ x ∧ x ≤ p} ×
		{x : ℤ | ~p ≤ x ∧ x ≤ p} ×
		{x : ℤ | ~p ≤ x ∧ x ≤ p} ⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(REPEAT (bc_thm_tac (finite_bc_rule ×_finite_size_thm) THEN REPEAT strip_tac)
	THEN rewrite_tac[ℤ_interval_finite_thm]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN rewrite_tac[×_def]);
a(lemma_tac⌜ℕℤ 0 ≤ x3 * x3⌝ THEN1 rewrite_tac[ℤ_0_≤_square_thm]);
a(lemma_tac⌜ℕℤ 0 < x1 * x2⌝ THEN1 all_fc_tac[ℤ_0_less_0_less_times_thm]);
a(lemma_tac⌜x2 ≤ x1 * x2⌝ THEN1 all_fc_tac[ℤ_0_less_times_thm]);
a(lemma_tac⌜x1 ≤ x1 * x2⌝ THEN1 all_fc_tac[ℤ_0_less_times_thm1]);
a(lemma_tac⌜x3 ≤ x3 * x3 ∧ ~x3 ≤ ~x3 * ~x3⌝
	THEN1 rewrite_tac[ℤ_≤_square_thm]);
a(PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏f_involution_a_thm⦎ = save_thm ( "f_involution_a_thm", (
set_goal([], ⌜∀p A f⦁
	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
⇒	(λ(x, y, z)⦁ (y, x, ~z)) ∈ Involution A
⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[involution_def]
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The following tactic is parameterised by a list of terms of
the form $x = (a, b)$ where $x$, $a$ and $b$ are variables
and each $x$ is expected to occur free in the goal.
It replace each $x$ by the corresponding pair $(a, b)$.
The tactic is useful in bridging the gap between the definitions
in the theory (which tend to use the form $(a, b)$ for clarity when
arithmetic needs to be done on the components of the pair)
and the conjectures (which use the form $x$ wherever
possible for brevity and generality).
=SML
local
val fst_tm = ⌜Fst : 'a × 'b → 'a⌝;
val snd_tm = ⌜Snd : 'a × 'b → 'b⌝;
val a_ty = ⓣ'a⌝;
val b_ty = ⓣ'b⌝;
val def_thm = get_spec fst_tm;
in
fun ⦏pair_tac⦎ (tm : TERM) : TACTIC = (
	let	val (x, ab) = dest_eq tm;
		val (a, b) = dest_pair ab;
		val lemma = list_mk_∃ ([a, b], tm);
		val type_map = [(type_of a, a_ty), (type_of b, b_ty)];
		val fst_witness = mk_app(inst [] type_map fst_tm, x);
		val snd_witness = mk_app(inst [] type_map snd_tm, x);
	in	PC_T1 "basic_hol" lemma_tac lemma THEN_LIST
		[	∃_tac fst_witness THEN
			∃_tac snd_witness THEN DROP_ASMS_T discard_tac THEN
			pure_rewrite_tac[def_thm] THEN REPEAT strip_tac,
			var_elim_asm_tac tm]
	end
);
end;
=TEX
=SML
val ⦏size_a_size_b_thm⦎ = save_thm ( "size_a_size_b_thm", (
set_goal([], ⌜∀p m A B⦁
	p = ℕℤ 4 * m + ℕℤ 1
∧	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
∧	B = {(x, y, z) | (x, y, z) ∈ A ∧ z > ℕℤ 0}
⇒	#A = 2 * #B
⌝);
a(REPEAT strip_tac THEN bc_thm_tac involution_size_thm);
a(∃_tac⌜λ(x, y, z) : ℤ × ℤ × ℤ⦁ (y, x, ~z)⌝);
a(ALL_FC_T rewrite_tac[f_involution_a_thm, a_finite_thm]);
a(REPEAT ∧_tac THEN_TRY ∀_tac
	THEN all_var_elim_asm_tac1
	THEN1 PC_T1 "sets_ext1" prove_tac[]
	THEN1 (REPEAT strip_tac
		THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]));
a(pair_tac⌜x = (a, bc)⌝ THEN rewrite_tac[]);
a(pair_tac⌜bc = (b, c)⌝ THEN rewrite_tac[] THEN REPEAT strip_tac
	THEN_TRY PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜¬c = ℕℤ 0⌝
	THEN_LIST [id_tac, PC_T1 "ℤ_lin_arith" asm_prove_tac[]]);
a(swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]);
a(conv_tac(RAND_C eq_sym_conv) THEN rewrite_tac[ℤ_mod_4_lemma]);
pop_thm()
));

=TEX
=SML
val ⦏size_a_size_c_thm⦎ = save_thm ( "size_a_size_c_thm", (
set_goal([], ⌜∀p A C⦁
	(∀i⦁ ¬p = i * i)
∧	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
∧	C = {(x, y, z) | (x, y, z) ∈ A ∧ (x - y) + z > ℕℤ 0}
⇒	#A = 2 * #C
⌝);
a(REPEAT strip_tac THEN bc_thm_tac involution_size_thm);
a(∃_tac⌜λ(x, y, z) : ℤ × ℤ × ℤ⦁ (y, x, ~z)⌝);
a(ALL_FC_T rewrite_tac[f_involution_a_thm, a_finite_thm]);
a(REPEAT ∧_tac THEN_TRY ∀_tac
	THEN all_var_elim_asm_tac1
	THEN1 PC_T1 "sets_ext1" prove_tac[]
	THEN1 (REPEAT strip_tac
		THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]));
a(pair_tac⌜x = (a, bc)⌝ THEN rewrite_tac[]);
a(pair_tac⌜bc = (b, c)⌝ THEN rewrite_tac[] THEN REPEAT strip_tac
	THEN_TRY PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜¬c = b + ~a⌝
	THEN_LIST [id_tac, PC_T1 "ℤ_lin_arith" asm_prove_tac[]]);
a(contr_tac THEN all_var_elim_asm_tac1);
a(swap_nth_asm_concl_tac 4 THEN strip_tac);
a(∃_tac⌜a + b⌝ THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏size_b_size_c_thm⦎ = save_thm ( "size_b_size_c_thm", (
set_goal([], ⌜∀p m A B C⦁
	p = ℕℤ 4 * m + ℕℤ 1
∧	(∀i⦁ ¬p = i * i)
∧	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
∧	B = {(x, y, z) | (x, y, z) ∈ A ∧ z > ℕℤ 0}
∧	C = {(x, y, z) | (x, y, z) ∈ A ∧ (x - y) + z > ℕℤ 0}
⇒	#B = #C
⌝);
a(REPEAT strip_tac
	THEN all_fc_tac[size_a_size_b_thm, size_a_size_c_thm]
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏g_involution_c_thm⦎ = save_thm ( "g_involution_c_thm", (
set_goal([], ⌜∀p A C⦁
	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
∧	C = {(x, y, z) | (x, y, z) ∈ A ∧ (x - y) + z > ℕℤ 0}
⇒	(λ(x, y, z)⦁ ((x - y) + z, y, ℕℤ 2*y - z)) ∈ Involution C
⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[involution_def]
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏size_c_thm⦎ = save_thm ( "size_c_thm", (
set_goal([], ⌜∀p m A C⦁
	p = ℕℤ 4 * m + ℕℤ 1
∧	ℕℤ 1 < p
∧	(∀a b⦁ ℕℤ 0 < a ∧ ℕℤ 0 < b ∧ p = (ℕℤ 4 * a + b) * b ⇒ b = ℕℤ 1)
∧	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
∧	C = {(x, y, z) | (x, y, z) ∈ A ∧ (x - y) + z > ℕℤ 0}
⇒	∃k⦁ #C = 2*k + 1
⌝);
a(REPEAT strip_tac THEN bc_thm_tac involution_fixed_singleton_thm);
a(lemma_tac⌜C ⊆ A⌝ THEN1 (asm_rewrite_tac[] THEN PC_T1 "sets_ext1" prove_tac[]));
a(all_fc_tac[a_finite_thm]);
a(∃_tac⌜(m, ℕℤ 1, ℕℤ 1)⌝
	THEN ∃_tac⌜(λ(x, y, z)⦁ ((x - y) + z, y, ℕℤ 2*y - z))⌝
	THEN1 ALL_FC_T rewrite_tac[g_involution_c_thm, ⊆_finite_thm]);
a(PC_T1 "sets_ext1" rewrite_tac[fixed_def]);
a(LIST_DROP_NTH_ASM_T [1, 2] discard_tac
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[ℤ_plus_assoc_thm]
	THEN REPEAT_UNTIL is_⇒ strip_tac
	THEN strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜x3 = x2⌝ THEN1 PC_T1 "ℤ_lin_arith" asm_prove_tac[]
	THEN all_var_elim_asm_tac);
a(lemma_tac⌜x2 = ℕℤ 1⌝
	THEN1 (DROP_NTH_ASM_T 7 bc_thm_tac THEN ∃_tac⌜x1⌝)
	THEN1 PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN REPEAT strip_tac);
a(PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏h_involution_b_thm⦎ = save_thm ( "h_involution_b_thm", (
set_goal([], ⌜∀p A B⦁
	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
∧	B = {(x, y, z) | (x, y, z) ∈ A ∧ z > ℕℤ 0}
⇒	(λ(x, y, z)⦁ (y, x, z)) ∈ Involution B
⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[involution_def]
	THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏h_fixed_in_b_thm⦎ = save_thm ( "h_fixed_in_b_thm", (
set_goal([], ⌜∀p m A B⦁
	p = ℕℤ 4 * m + ℕℤ 1
∧	ℕℤ 1 < p
∧	(∀i⦁ ¬p = i * i)
∧	(∀a b⦁ ℕℤ 0 < a ∧ ℕℤ 0 < b ∧ p = (ℕℤ 4 * a + b) * b ⇒ b = ℕℤ 1)
∧	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
∧	B = {(x, y, z) | (x, y, z) ∈ A ∧ z > ℕℤ 0}
⇒	¬B ∩ Fixed (λ(x, y, z)⦁ (y, x, z)) = {}
⌝);
a(REPEAT strip_tac THEN bc_thm_tac involution_odd_size_thm);
a(lemma_tac⌜∃C⦁
	C = {(x, y, z) | (x, y, z) ∈ A ∧ (x - y) + z > ℕℤ 0}⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜B ⊆ A⌝ THEN1 (asm_rewrite_tac[] THEN PC_T1 "sets_ext1" prove_tac[]));
a(all_fc_tac[a_finite_thm]);
a(all_fc_tac[size_c_thm]);
a(∃_tac⌜k⌝ THEN ALL_FC_T rewrite_tac[h_involution_b_thm, ⊆_finite_thm]);
a(ALL_FC_T asm_rewrite_tac[size_b_size_c_thm]);
pop_thm()
));

=TEX
=SML
val ⦏two_squares_lemma⦎ = save_thm ( "two_squares_lemma", (
set_goal([], ⌜∀p m⦁
	p = ℕℤ 4 * m + ℕℤ 1
∧	ℕℤ 1 < p
∧	(∀i⦁ ¬p = i * i)
∧	(∀a b⦁ ℕℤ 0 < a ∧ ℕℤ 0 < b ∧ p = (ℕℤ 4 * a + b) * b ⇒ b = ℕℤ 1)
⇒	∃a b⦁p = a*a + b*b
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃A B C⦁
	A = {(x, y, z) | ℕℤ 0 < x ∧ ℕℤ 0 < y ∧ ℕℤ 4*x*y + z*z = p}
∧	B = {(x, y, z) | (x, y, z) ∈ A ∧ z > ℕℤ 0}
∧	C = {(x, y, z) | (x, y, z) ∈ A ∧ (x - y) + z > ℕℤ 0}⌝
	THEN1 REPEAT (prove_∃_tac THEN strip_tac));
a(ALL_FC_T (MAP_EVERY ante_tac) [h_fixed_in_b_thm]);
a(all_var_elim_asm_tac1
	THEN PC_T1 "sets_ext1" rewrite_tac[fixed_def]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac);
a(∃_tac⌜ℕℤ 2 * x1⌝ THEN ∃_tac⌜x3⌝ THEN PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));
=TEX
\section{PROOFS IN THE THEORY {\em infcomb}}

=SML
open_theory "infcomb";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=SML
val ⦏infinite_def⦎ = get_spec⌜Infinite⌝;
=TEX
=SML
val ⦏infinite_lemma1⦎ = (* save_thm *) snd ("infinite_lemma1", (
set_goal([], ⌜∀a⦁ a ∈ Infinite ⇒ ∃f : ℕ → 'a⦁ OneOne f ∧ ∀i⦁ f i ∈ a⌝);
a(rewrite_tac[infinite_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∃g⦁g 0 = {} ∧ ∀i⦁ g (i + 1) = {εx⦁x ∈ a \ g i} ∪ g i⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜¬a = {}⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac1 THEN all_fc_tac[empty_finite_thm]));
a(lemma_tac⌜∀i⦁ g i ∈ Finite⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(induction_tac⌜i⌝ THEN asm_rewrite_tac[empty_finite_thm]);
a(bc_thm_tac singleton_∪_finite_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(lemma_tac⌜∀i⦁ g i ⊆ a⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(induction_tac⌜i⌝ THEN asm_rewrite_tac[]);
a(asm_rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀y b⦁{y} ∪ b ⊆ a ⇔ y ∈ a ∧ b ⊆ a⌝]);
a(lemma_tac⌜¬g i = a⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac1 THEN asm_prove_tac[]));
a(all_ε_tac THEN REPEAT_N 2 (POP_ASM_T ante_tac) THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∀i⦁ (ε x⦁ x ∈ a \ g i) ∈ a \ g i⌝ THEN1 strip_tac);
a(lemma_tac⌜g i ⊆ a ∧ ¬g i = a⌝ THEN1 (asm_rewrite_tac[] THEN
	contr_tac THEN all_var_elim_asm_tac1 THEN asm_prove_tac[]));
a(all_ε_tac THEN REPEAT_N 2 (POP_ASM_T ante_tac) THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜∀i j⦁ i < j ⇒ (ε x⦁ x ∈ a \ g i) ∈ g j⌝);
(* *** Goal "2.2.2.1" *** *)
a(rewrite_tac[rewrite_rule[≤_def] less_def] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(induction_tac⌜i'⌝ THEN1 asm_rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀y b⦁ y ∈ {y} ∪ b⌝]);
(* *** Goal "2.2.2.1" *** *)
a(asm_rewrite_tac[pc_rule1"lin_arith" prove_rule[]⌜(i + 1) + i' + 1 = ((i + 1) + i') + 1⌝]);
a(bc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀y a b⦁y ∈ b ⇒ y ∈ a ∪ b⌝] THEN strip_tac);
(* *** Goal "2.2.2.2" *** *)
a(∃_tac⌜λi⦁ε x⦁ x ∈ a \ g i⌝ THEN rewrite_tac[one_one_def] THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(strip_asm_tac (list_∀_elim[⌜x1⌝, ⌜x2⌝] less_cases_thm) THEN all_asm_fc_tac[]);
(* *** Goal "2.2.2.2.1.1" *** *)
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜x2⌝) THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.1.2" *** *)
a(POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 (rewrite_thm_tac o eq_sym_rule));
a(DROP_NTH_ASM_T 3 (ante_tac o ∀_elim⌜x1⌝) THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.2" *** *)
a(DROP_NTH_ASM_T 2 (ante_tac o ∀_elim⌜i⌝) THEN REPEAT strip_tac);
pop_thm()
));
=TEX
=SML
val ⦏infinite_thm⦎ = save_thm("infinite_thm", (
set_goal([], ⌜∀a⦁ a ∈ Infinite ⇔ ∃f : ℕ → 'a⦁ OneOne f ∧ ∀i⦁ f i ∈ a⌝);
a(rewrite_tac[taut_rule⌜∀p q⦁ (p ⇔ q) ⇔ (p ⇒ q) ∧ (q ⇒ p)⌝, infinite_lemma1]
	THEN rewrite_tac[infinite_def, one_one_def] THEN contr_tac);
a(lemma_tac⌜{x | ∃i⦁ i < #a + 1 ∧ x = f i} ∈ Finite ∧
	#{x | ∃i⦁ i < #a + 1 ∧ x = f i} = #{i | i < #a + 1}⌝
		THEN1 (bc_thm_tac bijection_finite_size_thm THEN rewrite_tac[range_finite_size_thm]));
(* *** Goal "1" *** *)
a(∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[range_finite_size_thm]);
a(lemma_tac⌜{x | ∃i⦁ i < #a + 1 ∧ x = f i} ∈ Finite ∧ #{x | ∃i⦁ i < #a + 1 ∧ x = f i} ≤ #a⌝
		THEN1 (bc_thm_tac ⊆_finite_size_thm THEN REPEAT strip_tac));
(* *** Goal "2.1" *** *)
a(PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));
=TEX
=SML
val ⦏infinite_non_empty_thm⦎ = save_thm("infinite_non_empty_thm", (
set_goal([], ⌜∀a⦁ a ∈ Infinite ⇒ ∃x⦁ x ∈ a⌝);
a(REPEAT strip_tac THEN all_fc_tac[infinite_thm]);
a(asm_prove_tac[]);
pop_thm()
));
=TEX
=SML
val ⦏ℕ_infinite_thm⦎ = save_thm("ℕ_infinite_thm", (
set_goal([], ⌜Universe : ℕ SET ∈ Infinite⌝);
a(rewrite_tac[infinite_thm]);
a(∃_tac⌜λi⦁i⌝ THEN rewrite_tac[one_one_def]);
pop_thm()
));
=TEX
=SML
val ⦏infinite_diff_finite_thm⦎ = save_thm("infinite_diff_finite_thm", (
set_goal([], ⌜∀a b⦁ a ∈ Infinite ∧ b ∈ Finite ⇒ a \ b ∈ Infinite⌝);
a(rewrite_tac[infinite_def] THEN contr_tac);
a(lemma_tac⌜b ∪ (a \ b) ∈ Finite⌝ THEN1 asm_rewrite_tac[∪_finite_thm]);
a(lemma_tac⌜a ⊆ b ∪ (a \ b)⌝ THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
pop_thm()
));
=TEX
=SML
val ⦏min_infinite_thm⦎ = save_thm("min_infinite_thm", (
set_goal([], ⌜∀a⦁ a ∈ Infinite ⇒ Min a ∈ a ∧ ∀i⦁ i ∈ a ⇒ Min a ≤ i⌝);
a(REPEAT strip_tac THEN all_fc_tac[infinite_non_empty_thm]);
(* *** Goal "1" *** *)
a(all_fc_tac[min_∈_thm]);
(* *** Goal "2" *** *)
a(all_fc_tac[min_≤_thm]);
pop_thm()
));
=TEX
=SML
val ⦏infinite_diff_singleton_thm⦎ = save_thm("infinite_diff_singleton_thm", (
set_goal([], ⌜∀a x⦁ a ∈ Infinite ⇒ a \ {x} ∈ Infinite⌝);
a(REPEAT strip_tac THEN bc_thm_tac infinite_diff_finite_thm
	THEN asm_rewrite_tac[singleton_finite_thm]);
pop_thm()
));
=TEX
=SML
val ⦏infinite_unbounded_thm⦎ = save_thm("infinite_unbounded_thm", (
set_goal([], ⌜∀a i⦁ a ∈ Infinite ⇒ ∃j : ℕ⦁ j ∈ a ∧ i < j⌝);
a(rewrite_tac[infinite_def] THEN contr_tac);
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[]);
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{j | j < i + 1}⌝);
a(rewrite_tac[range_finite_size_thm] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜x⌝ THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML
=TEX
=SML
val ⦏infinite_one_one_image_thm⦎ = save_thm("infinite_one_one_image_thm", (
set_goal([], ⌜∀a f⦁ a ∈ Infinite ∧ OneOne f ⇒ {y | ∃x⦁ x ∈ a ∧ y = f x} ∈ Infinite⌝);
a(rewrite_tac[infinite_thm, one_one_def] THEN REPEAT strip_tac);
a(∃_tac⌜λi⦁ f(f' i)⌝ THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜f' i⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏ordered_enumeration_lemma1⦎ = snd (* save_thm *) ("ordered_enumeration_lemma1", (
set_goal([], ⌜∀a : ℕ ℙ; i j⦁ i ∈ a ∧ i < j ⇒
	 #{k | k ∈ a ∧ k < i} < #{k | k ∈ a ∧ k < j}⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜{k | k ∈ a ∧ k < i} ⊆ {k | k ∈ a ∧ k < j}⌝ THEN1
	(PC_T1 "sets_ext1" REPEAT strip_tac THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(lemma_tac⌜{k | k ∈ a ∧ k < j} ∈ Finite⌝ THEN1 
	(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{k | k < j}⌝
		THEN rewrite_tac[range_finite_size_thm]
			THEN PC_T1 "sets_ext" asm_prove_tac[]));
a(LEMMA_T⌜{k|k ∈ a ∧ k < i} ∈ Finite ∧ # {k|k ∈ a ∧ k < i} ≤ # {k|k ∈ a ∧ k < j}⌝
	(strip_asm_tac o rewrite_rule[pc_rule1"lin_arith" prove_rule[]
		⌜∀m n:ℕ⦁m ≤ n ⇔ m < n ∨ m = n⌝]));
(* *** Goal "1" *** *)
a(bc_thm_tac ⊆_finite_size_thm THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(i_contr_tac THEN all_fc_tac[⊆_size_eq_thm]);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" rewrite_tac[]);
a(strip_tac THEN ∃_tac⌜i⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
=SML
val ⦏ordered_enumeration_lemma2⦎ = snd (* save_thm *) ("ordered_enumeration_lemma2", (
set_goal([], ⌜∀a : ℕ ℙ; i j⦁
		j ∈ a ∧ #{k | k ∈ a ∧ k < i} < #{k | k ∈ a ∧ k < j}
	⇒ i < j⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜i⌝, ⌜j⌝] less_cases_thm)
	THEN1 all_var_elim_asm_tac1);
a(contr_tac THEN lemma_tac⌜i = j ∨ j < i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN1 all_var_elim_asm_tac1);
a(all_fc_tac[ordered_enumeration_lemma1] THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML

val ⦏ordered_enumeration_thm⦎ = save_thm("ordered_enumeration_thm", (
set_goal([], ⌜∀a : ℕ ℙ⦁ a ∈ Infinite ⇒ ∃ f : ℕ → ℕ⦁
		a = {i | ∃m⦁ f m = i}
	∧	(∀m n⦁ m < n ⇒ f m < f n)⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜∀i⦁ {j | j ∈ a ∧ j < i} ∈ Finite⌝ THEN1
	(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm THEN ∃_tac ⌜{j : ℕ | j < i}⌝
		THEN rewrite_tac[range_finite_size_thm] THEN PC_T1 "sets_ext1" prove_tac[]));
a(lemma_tac⌜∀n⦁∃i⦁i ∈ a ∧ #{j | j ∈ a ∧ j < i} = n⌝ THEN1 strip_tac);
a(induction_tac⌜n⌝);
(* *** Goal "1.1" *** *)
a(fc_tac[min_infinite_thm]);
a(∃_tac⌜Min a⌝ THEN REPEAT strip_tac);
a(LEMMA_T ⌜∀i⦁ # {j|j ∈ a ∧ j < i} = 0 ⇔ {j|j ∈ a ∧ j < i} = {}⌝ rewrite_thm_tac
	THEN1 (strip_tac THEN bc_thm_tac size_0_thm THEN asm_rewrite_tac[]));
a(PC_T1 "sets_ext1" asm_rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜∀x y⦁¬(x ∈ a ∧ x < y) ⇔ x ∈ a ⇒ y ≤ x⌝]);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜{j | j < i + 1} ∈ Finite⌝ THEN1 rewrite_tac[range_finite_size_thm]);
a(all_fc_tac[infinite_diff_finite_thm]);
a(DROP_NTH_ASM_T 6 discard_tac THEN fc_tac[min_infinite_thm]);
a(∃_tac⌜Min(a \ {j|j < i + 1})⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜{j|j ∈ a ∧ j < Min (a \ {j|j < i + 1})} = {i} ∪ {j|j ∈ a ∧ j < i}⌝
		rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY all_var_elim_asm_tac1));
(* *** Goal "1.2.1" *** *)
a(spec_nth_asm_tac 6 ⌜x⌝ THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(spec_nth_asm_tac 3 ⌜i⌝ THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.3" *** *)
a(spec_nth_asm_tac 5 ⌜x⌝ THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.4" *** *)
a(spec_nth_asm_tac 8 ⌜i⌝);
a(PC_T1 "predicates" lemma_tac⌜¬i ∈ {j | j ∈ a ∧ j < i}⌝ THEN1 rewrite_tac[]);
a(ALL_FC_T asm_rewrite_tac[size_singleton_∪_thm]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∃f⦁ ∀ n⦁ f n ∈ a ∧ # {j|j ∈ a ∧ j < f n} = n⌝ THEN1 prove_∃_tac);
a(DROP_NTH_ASM_T 2 discard_tac);
a(∃_tac⌜f⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(∃_tac⌜#{j | j ∈ a ∧ j < x}⌝);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o ∀_elim⌜#{j | j ∈ a ∧ j < x}⌝));
a(strip_asm_tac (list_∀_elim[⌜f (# {j|j ∈ a ∧ j < x})⌝, ⌜x⌝] less_cases_thm)
	THEN i_contr_tac
	THEN all_fc_tac[ordered_enumeration_lemma1]
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(all_var_elim_asm_tac1 THEN asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a(bc_thm_tac ordered_enumeration_lemma2);
a(∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
=SML
val ⦏finite_size_to_finite_rule⦎ : THM -> THM = (
	let	val pattern = ⌜a ∈ Finite ∧ p⌝;
	in	fn thm => 
			let	val thm1 = (undisch_rule o all_∀_elim) thm;
				val _ = term_match (concl thm1) pattern;
				val thm2 = (all_∀_intro o all_disch_rule o ∧_left_elim) thm1;
			in	thm2
			end
	end
);

=TEX
=SML
val ⦏infinite_pigeon_hole_thm⦎ = save_thm("infinite_pigeon_hole_thm", (
set_goal([], ⌜∀a b; f : 'a → 'b⦁
		a ∈ Infinite
	∧	b ∈ Finite
	∧	(∀x⦁x ∈ a ⇒ f x ∈ b)
	⇒	(∃y⦁ y ∈ b ∧ {x | x ∈ a ∧ f x = y} ∈ Infinite)⌝);
a(rewrite_tac[infinite_def] THEN contr_tac);
a(lemma_tac⌜a = ⋃{s | ∃y⦁ y ∈ b ∧ s = {x | x ∈ a ∧ f x = y}}⌝);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_asm_fc_tac[]);
a(∃_tac⌜{z | z ∈ a ∧ f z = f x}⌝ THEN asm_rewrite_tac[]);
a(∃_tac⌜f x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜a ∈ Finite⌝ THEN POP_ASM_T once_rewrite_thm_tac);
a(bc_thm_tac ⋃_finite_thm);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac (finite_size_to_finite_rule surjection_finite_size_thm));
a(∃_tac⌜λy⦁ {x | x ∈ a ∧ f x = y}⌝ THEN ∃_tac⌜b⌝ THEN REPEAT strip_tac);
a(rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(asm_prove_tac[]);
pop_thm()
));
=TEX
=SML
val ⦏infinite_ramsey_thm⦎ = save_thm("infinite_ramsey_thm", (
set_goal([], ⌜∀n X C; m : ℕ⦁
		X ∈ Infinite ∧ (∀a⦁ C a < m)
	⇒	(∃Y c⦁	Y ⊆ X ∧ Y ∈ Infinite ∧ c < m
		∧	∀a⦁ a ⊆ Y ∧ a ∈ Finite ∧ #a = n ⇒ C a = c)⌝);
a(strip_tac THEN induction_tac⌜n:ℕ⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜X⌝ THEN ∃_tac⌜C{}⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[size_0_thm]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∀Y⦁	Y ∈ Infinite
	⇒	∃Z x c⦁
			x ∈ Y ∧ Z ⊆ Y \ {x} ∧ Z ∈ Infinite ∧ c < m'
		∧	∀a⦁ a ⊆ {x} ∪ Z ∧ a ∈ Finite ∧ #a = n + 1 ∧ x ∈ a ⇒ C a = c⌝);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 2 discard_tac THEN REPEAT strip_tac THEN all_fc_tac[infinite_non_empty_thm]);
a(lemma_tac⌜Y \ {x} ∈ Infinite⌝ THEN1 (bc_thm_tac infinite_diff_singleton_thm THEN REPEAT strip_tac));
a(lemma_tac⌜∀a⦁ (λa⦁ C (a ∪ {x})) a < m'⌝ THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [4, 5] discard_tac THEN all_asm_fc_tac[]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[]));
a(∃_tac⌜Y'⌝ THEN ∃_tac⌜x⌝ THEN ∃_tac⌜c⌝ THEN REPEAT strip_tac);
a(LEMMA_T ⌜a = (a \ {x}) ∪ {x}⌝ once_rewrite_thm_tac THEN1
	(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(DROP_NTH_ASM_T 4 ante_tac THEN  PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜a⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.3" *** *)
a(LEMMA_T ⌜#a = #(a \ {x}) + #{x} ⌝
	(fn thm => (ante_tac o eq_sym_rule) thm THEN asm_rewrite_tac[size_singleton_thm]));
a(bc_thm_tac size_⊆_diff_thm THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∃Y⦁
	Y 0 = X
∧	∀i⦁
	Y(i+1) = (ε Z⦁ ∃x c⦁ x ∈ Y i ∧ Z ⊆ Y i \ {x} ∧ Z ∈ Infinite ∧ c < m'
		∧	∀a⦁ a ⊆ {x} ∪ Z ∧ a ∈ Finite ∧ #a = n + 1 ∧ x ∈ a ⇒ C a = c)⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∀i⦁ Y i ∈ Infinite⌝);
(* *** Goal "2.2.1" *** *)
a(strip_tac THEN induction_tac⌜i:ℕ⌝ THEN asm_rewrite_tac[]);
a(all_ε_tac);
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜∀i⦁ ∃x c⦁
		x ∈ Y i ∧ Y (i+1) ⊆ Y i \ {x} ∧ c < m'
	 ∧	∀a⦁ a ⊆ {x} ∪ Y(i+1) ∧ a ∈ Finite ∧ #a = n + 1 ∧ x ∈ a ⇒ C a = c⌝);
(* *** Goal "2.2.2.1" *** *)
a(REPEAT strip_tac THEN asm_rewrite_tac[] THEN all_ε_tac);
(* *** Goal "2.2.2.1.1" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.1.2" *** *)
a(∃_tac⌜x⌝ THEN ∃_tac⌜c⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(lemma_tac⌜∃xs cs⦁ 
		(∀i⦁ xs i ∈ Y i ∧ Y (i+1) ⊆ Y i \ {xs i})
	∧	(∀i⦁cs i < m')
	∧	(∀i⦁ ∀a⦁ a ⊆ {xs i} ∪ Y(i+1) ∧ a ∈ Finite ∧ #a = n + 1 ∧ xs i ∈ a ⇒ C a = cs i)⌝
 THEN prove_∃_tac THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜i''⌝));
a(∃_tac⌜x⌝ THEN REPEAT strip_tac THEN ∃_tac⌜c⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [4, 6, 8] discard_tac);
a(lemma_tac⌜∀i j⦁i < j ⇒ Y j ⊆ Y i \ {xs i}⌝);
(* *** Goal "2.2.2.2.2.1" *** *)
a(rewrite_tac[rewrite_rule[≤_def] less_def] THEN REPEAT_N 3 strip_tac THEN all_var_elim_asm_tac1);
a(induction_tac⌜i'⌝ THEN1 asm_rewrite_tac[]);
a(rewrite_tac[plus_assoc_thm1]);
a(bc_tac[pc_rule1 "sets_ext1" prove_rule[] ⌜∀a b c⦁a ⊆ b ∧b ⊆ c⇒ a ⊆ c⌝]
	THEN ∃_tac ⌜Y ((i + 1) + i')⌝ THEN asm_rewrite_tac[]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[] ⌜(i + 1) + i' = (i + i') + 1⌝]);
a(bc_tac[pc_rule1 "sets_ext1" prove_rule[] ⌜∀a b c⦁a ⊆ b ∧ b ⊆ c⇒ a ⊆ c⌝]
	THEN ∃_tac ⌜Y ((i + i') + 1) \ {xs((i + i') + 1)}⌝ THEN1 asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.2.2.2.2" *** *)
a(lemma_tac⌜∀i j⦁i < j ⇒ xs j ∈ Y i \ {xs i}⌝);
(* *** Goal "2.2.2.2.2.2.1" *** *)
a(REPEAT_N 3 strip_tac THEN all_asm_fc_tac[]);
a(bc_tac[pc_rule1 "sets_ext1" prove_rule[] ⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]
	THEN ∃_tac ⌜Y j⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.2.2.2" *** *)
a(lemma_tac⌜∀i j⦁ i ≤ j ⇒ Y j ⊆ Y i⌝);
(* *** Goal "2.2.2.2.2.2.2.2.1" *** *)
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[] ⌜∀i j:ℕ⦁ i ≤ j ⇔ i = j ∨ i < j⌝]
	THEN REPEAT strip_tac THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.2.2.2.2.2" *** *)
a(lemma_tac⌜OneOne xs⌝ THEN1 (rewrite_tac[one_one_def] THEN REPEAT strip_tac));
(* *** Goal "2.2.2.2.2.2.2.2.1" *** *)
a(strip_asm_tac(list_∀_elim[⌜x1⌝, ⌜x2⌝] less_cases_thm) THEN i_contr_tac);
(* *** Goal "2.2.2.2.2.2.2.2.1.1" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.2.2.2.1.2" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
(* *** Goal "2.2.2.2.2.2.2.2.2" *** *)
a((ante_tac o rewrite_rule [ℕ_infinite_thm, range_finite_size_thm] o
	list_∀_elim[⌜Universe : ℕ SET⌝, ⌜{i | i < m'}⌝, ⌜cs⌝]) infinite_pigeon_hole_thm
	THEN asm_rewrite_tac[] THEN strip_tac);
a(rename_tac[(⌜y⌝, "c")] THEN all_fc_tac[infinite_one_one_image_thm]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[]));
a(∃_tac⌜{x | ∃i⦁cs i = c ∧ x = xs i}⌝ THEN REPEAT strip_tac THEN1 ∃_tac⌜c⌝);
(* *** Goal "2.2.2.2.2.2.2.2.2.1" *** *)
a(all_fc_tac[ordered_enumeration_thm] THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN cases_tac ⌜a = {}⌝ THEN1 asm_rewrite_tac[size_empty_thm]);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x a b⦁ x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_var_elim_asm_tac1);
a(lemma_tac⌜Min {i | xs i ∈ a} ∈ {i | xs i ∈ a}⌝ THEN1
	(bc_thm_tac min_∈_thm THEN ∃_tac⌜i⌝ THEN REPEAT strip_tac));
a(DROP_NTH_ASM_T 3 discard_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x a b⦁ x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(GET_NTH_ASM_T 12 (fn th => all_fc_tac[rewrite_rule[one_one_def] th])
	THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 14 bc_thm_tac THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀b⦁ x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]
	THEN1 all_var_elim_asm_tac1);
a(LEMMA_T⌜Min {i|xs i ∈ a} ≤ i'⌝ ante_tac THEN1 (bc_thm_tac min_≤_thm THEN asm_rewrite_tac[]));
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[] ⌜∀i j:ℕ⦁ i ≤ j ⇔ i = j ∨ i < j⌝]
	THEN strip_tac THEN1 all_var_elim_asm_tac1);
a(bc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x a b⦁ x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(∃_tac⌜Y i'⌝ THEN asm_rewrite_tac[]);
a(LIST_GET_NTH_ASM_T [15] bc_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.2.2.2.2.2.2.2.2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(bc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x a b⦁ x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(∃_tac⌜Y i⌝ THEN asm_rewrite_tac[]);
a(LIST_GET_NTH_ASM_T [5] bc_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
\Hide{
=SML
local 
	open	ListerSupport;
	val ⦏sections⦎ = [LSBanner, LSThms];
	val {print=pt, out=ot, out1=ot1} = gen_theory_lister sections;
	fun output_banner (thyn : string) = "THEOREMS IN THE THEORY " ^ (case thyn of "-" => get_current_theory_name () | _ => thyn);
	fun output_theorems (par : {out_file:string, theory:string}) : unit = (
		(open_theory o #theory) par;
		(ot output_banner par) handle ex => reraise ex "z_output_theory"
	);
in
	val _ = output_theorems{out_file="wrk0731.th.doc", theory="fincomb"};
	val _ = output_theorems{out_file="wrk0732.th.doc", theory="infcomb"};
end;
=TEX
} %\Hide
\end{document}

=TEX
%%%%
%%%%
=IGN

