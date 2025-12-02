=IGN
********************************************************************************
wrk076.doc: this file is supplementary material for the ProofPower system

Copyright (c) 2006 Lemma 1 Ltd.

This file is supplied under the GNU General Public Licence (GPL) version 2.

See the file LICENSE supplied with ProofPower source for the terms of the GPL
or visit the OpenSource web site at http://www.opensource.org/

Contact: Rob Arthan < rda@lemma-one.com >
********************************************************************************
$Id: wrk076.doc,v 1.36 2012/06/05 16:19:35 rda Exp rda $
********************************************************************************
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\usepackage{A4}
\usepackage{url}
%
% Macro for cloak-and-dagger work:
%
\def\Hide#1{\relax}
%
% Macros for various mathematical odds and ends:
%
\def\Func#1{{\mathsf{#1}}}
\def\GA{\Func{GA}}
\def\O{\Func{O}}
\def\Pin{\Func{Pin}}
\def\Spin{\Func{Spin}}
\def\Zero{\mathbf{0}}
\def\One{\mathbf{1}}
\def\x{\mathbf{x}}
\def\y{\mathbf{y}}
\def\z{\mathbf{z}}
\def\N{\mathbb{N}}
\def\D{\mathbb{D}}
\def\B{\mathbb{B}}
\def\R{\mathbb{R}}
\def\Z{\mathbb{Z}}
\def\Q{\mathbb{Q}}
\def\E#1{\mathbf{e}_{#1}}
\def\F#1{\mathbf{f}_{#1}}
%
% Macros for the tables of theorem names
%
\def\ThmsII#1#2{%
{\vertbarfalse
\begin{center}
\begin{minipage}[t]{0.48\hsize}
#1
\end{minipage}
\begin{minipage}[t]{0.48\hsize}
#2
\end{minipage}
\end{center}}}
%
\def\ThmsIII#1#2#3{%
{\vertbarfalse
\begin{center}
\begin{minipage}[t]{0.32\hsize}
#1
\end{minipage}
\begin{minipage}[t]{0.32\hsize}
#2
\end{minipage}
\begin{minipage}[t]{0.32\hsize}
#3
\end{minipage}
\end{center}}}
%
%  article red tape:
%
\title{Mathematical Case Studies: the Geometric Algebra\thanks{
First posted 30 October 2006;
for full changes history see: \protect\url{https://github.com/RobArthan/pp-contrib}.
}}
\author{Rob Arthan}
\date{\FormatDate{\VCDate}}
\makeindex
\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This document is one of a series of mathematical case studies in  {\ProductHOL}.
It gives a construction of the Geometric Algebra $GA$.
\end{abstract}
\vfill
\begin{centering}

\bf Copyright \copyright\ : Lemma 1 Ltd 2006--\number\year \\
Reference: LEMMA1/HOL/WRK076; Current git revision: \VCVersion%


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
In \cite{Harrison05a}, Harrison advocates an approach to Euclidean geometry in HOL using a type constructor to model the individual Euclidean spaces $\R^{N}$, for finite $N$.
In this document, we set up the framework for an alternative approach where one works in a fixed type that contains all of the $\bbR^{n}$ for all $n \in \N$.
In fact we do more than that: we construct a system which can be viewed as the natural and in some sense final algebraic structure in the chain that begins
$\mathbb N, Z, Q, R, C, \ldots$.
This structure is known as the {\em geometric algebra}.
To quote Macdonald~\cite{Macdonald06}:

\begin{quotation}
\it
Geometric algebra is nothing less than a new approach to geometry.
Geometric objects (points, lines, planes, [\ldots]) are represented by members of an algebra, a {\em geometric algebra}, rather than by equations. Geometric operations (rotate, translate, intersect, [\ldots]) on the objects are represented by algebraic operations in the algebra, rather than by matrix operations.
Geometric algebra is {\em coordinate-free:} coordinates are needed only when specific objects or operations are under consideration.
\end{quotation}

Let me now give a potted account of geometric algebra.
The finite-dimensional geometric algebra $\GA(n)$ is paremeterised by the natural numbers $n$.
$\GA(n)$ is an associative algebra over the real numbers with a two-sided unit $\One$.
It is commutative iff. $n \le 1$.
Not all elements of $\GA(n)$ have multiplicative inverses, but many do and if $\x$ does have an inverse, it is written as $\x^{-1}$.



Real multiples $\lambda\One$ of the unit element in $\GA(n)$ are called {\em scalars} and are ordered by taking $\lambda\One < \mu\One$ iff.  $\lambda < \mu$.
Under this ordering, the subalgebra of scalars is isomorphic as an ordered field with the real numbers.

$\GA(n)$ is generated as an algebra by an $n$-dimensional subspace called $\R^{n}$ whose members are called {\em vectors}.
If $\x \in \R^{n}$, then $\x^2$ is a scalar.
It is easy to see that every non-zero vector has an inverse.

The {\em inner product} of vectors $\x$ and $\y$ is defined by $\x.\y = \frac{1}{2}(\x\y + \y\x)$ and is a scalar.
The inner product is a bilinear form, i.e., it satisfies the conditions $(\lambda\x).(\mu\y) = (\lambda\mu)(\x.\y)$, $(\x + \y).\z = \x.\z + \y.\z$,
$\x.(\y + \z) = \x.\y + \x.\z$.
Vectors $\x$ and $\y$ are said to be {\em orthogonal} iff. $\x.\y = 0$.
$\x$ and $\y$ are orthogonal iff. they anti-commute, i.e., iff. $\x\y = -\y\x$.

The {\em outer product} of vectors $\x$ and $\y$ is defined by $\x\land\y=\frac{1}{2}(\x\y -\y\x)$, so that $\x\y = \x.\y + \x\land\y$, which is a scalar iff. it is 0.
Vectors $\x$ and $\y$ are said to be {\em collinear} iff. $\x \land \y = 0$.
Thus, when $\x$ and $\y$ are orthogonal, $\x\y = \x \land \y$, while when they are collinear, $\x\y = \x . \y$.

In traditional vector algebra, the inner and outer products are taken as separate fundamental notions, but in the geometric algebra, the multiplication combines them into a united whole.
But the multiplication does much more than this.
As one example, we may think of a vector $\x$ as defining a notion of direction and magnitude in the line comprising all points $\lambda\x$ for $\lambda \in \R$.
Now, if $\x$ and $\y$ are orthogonal vectors, one can think of the product $\x\y$ as defining a notion of orientation and area in the plane spanned by $\x$ and $\y$.
More general products $\x_1\x_2 \ldots \x_k$ of $k$ pairwise orthogonal vectors are called $k$-blades and can be thought of as providing an oriented notion of volume in the $k$-dimensional space spanned by the $\x_i$.

For another example on the power of the geometric algebra, let $\O(n)$ denote the set of all orthogonal mappings from the subspace $\R^n$ to itself (where, by definition, an orthogonal mapping is one which preserves all inner products).
In linear algebra, $\O(n)$ is shown, with some considerable coordinate-rich work, to be given by a certain group of $n \times n$ matrices.

Now geometrically, it is not hard to see that $\O(n)$ is generated by reflections in hyperplanes, and then in the geometric algebra it is very easy to see that, for each non-zero vector $\y$, the mapping $\x \mapsto -\y\x\y^{-1}$ maps $\R^n$ to itself via reflection in the hyperplane perpendicular to $\y$.
Thus the geometric algebra instantly gives us a notation for orthogonal mappings without a coordinate or a matrix in sight.
In fact, $\GA(n)$ has a multiplicative subgroup, $\Pin(n)$, which is the universal covering group of the topological group $\O(n)$.
(As a topological space, $\Pin(n)$ has two connected components. The component of $\Pin(n)$ containing 1 is the {\em spinor} group $\Spin(n)$ beloved of physicists.)

The above discussion deals with the case of a positive definite orthogonal space $\R^n$.
There is also much interest in semidefinite orthogonal spaces in which $\x.\x$ can be negative and earlier drafts of this document did indeed follow the construction of~\cite{Arthan06b}. 
However, for simplicity, it now deals with the positive definite case only\footnote{
In fact, $\GA(\infty, \infty)$ is isomorphic to a subalgebra of $\GA(\infty)$ and we propose to work in such a subalgebra to deal with the semidefinite case.
A suitable subalgebra is the one generated by the elements $f_0 = e_0, f_{(-1)} = e_{123}, f_1 = e_4, f_{(-2)} = e_{567}, f_{2} = e_8, \ldots$.
If one makes the $f_i, i \in \Z$, take the r\^{o}le of the $e_i$ that generate $\GA(\infty, \infty)$ in \cite{Arthan06b}, then it is routine to check that the generators obey the laws of $\GA(\infty, \infty)$.}.

Simple explicit constructions of the geometric algebras have been given by Macdonald~\cite{Macdonald02}, and by the author~\cite{Arthan06b}.
As noted in~\cite{Arthan06b} the union of all of the $\GA(n)$ can be constructed in one step giving what I will now refer to as {\em the} geometric algebra, $\GA = \GA(\infty)$.


=SML
force_delete_theory"geomalg" handle Fail _ => ();
open_theory"numbers";
new_theory"geomalg";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℝ"];
=TEX

\section{THE GEOMETRIC ALGEBRA}

\subsection{Preliminaries}

It is very convenient to have available the symmetric difference operator for sets.
We follow Z in writing the symmetric difference of $a$ and $b$ as
=INLINEFT
a ⊖ b
=TEX
.
This operator is provided in {\Product} as pf version 2.7.7 so some ML trickery is used here to suppress the following definitions when they are not needed.
\Hide{
=SML
if (get_spec ⌜$⊖⌝; true) handle Fail _ => false
then () else (
=TEX
}
=SML
declare_infix(250, "⊖");
=TEX

ⓈHOLCONST
│ $⊖ : 'a SET → 'a SET → 'a SET
├──────
│ ∀a b⦁ a ⊖ b = (a \ b) ∪ (b \ a)
■
\Hide{
=SML
()) (* end of if ... *);
=TEX
}
The development of the theory begins with various simple facts about symmetric differences.
Symmetric difference makes the lattice of sets into a commutative group.
The script includes a conversion
=INLINEFT
⊖_nf_conv
=TEX
\ which gives a normal form for this group.

\ThmsIII{%
=GFT
⊖_group_thm
⊖_comm_thm
⊖_assoc_thm
=TEX
}{%
=GFT
⊖_lemmas
⊖_finite_thm
size_⊖_lemma
=TEX
}{%
=GFT
⊖_finite_size_thm
⊖_infinite_thm
=TEX
}

The following is based on the function $\sigma$ of~\cite{Arthan06b} for use in specifying the multiplication in $\GA$.

ⓈHOLCONST
│ ⦏Sign⋎G⦎ : ℕ SET → ℕ SET → ℝ
├──────
│ ∀ I J⦁	Sign⋎G I J =
│	~(ℕℝ 1) ^ #{(i, j) | i ∈ I ∧ j ∈ J ∧ j < i}
■

After a lemma, we have {\em sign\_g\_thm} which is lemma 1 of~\cite{Arthan06b}.
The proof given is a little bit more long-winded and general than the simplified version recorded in~\cite{Arthan06b}.
As a utility we also have the theorem that says the values taken on by $\sigma$ are $\pm1$ and the calculations that give the values of $\E{i}^2$ and $\E{i}\E{j}$.

\ThmsIII{%
=GFT
ℝ_ℕ_exp_mod_2_thm
sign_g_thm
=TEX
}{%
=GFT
sign_g_cases_thm
sign_singleton_thm
=TEX
}{%
=GFT
sign_singletons_thm
=TEX
}
=TEX
\subsection{The Type Definition}
$\GA$ in HOL will be a subtype of the type of all real-valued functions on sets of natural numbers (specifically, it will comprise the functions whose support is a finite set of finite sets).
The following type abbreviation captures this.
=SML
declare_type_abbrev("_GA", [], ⓣℕ SET → ℝ⌝);
=TEX
ⓈHOLCONST
│	⦏_IsGARep⦎ : _GA → BOOL
├
│	∀u⦁ _IsGARep u ⇔ Supp u ∈ Finite ∧ Supp u ⊆ Finite
■
We can now introduce the new type:
=SML

val ⦏ga_def⦎ = new_type_defn(["GA", "ga_def"], "GA", [],
	tac_proof(([], ⌜∃u⦁ _IsGARep u⌝),
		∃_tac⌜(λI⦁ℕℝ 0)⌝
	THEN	rewrite_tac[get_spec⌜_IsGARep⌝, get_spec⌜Supp⌝,
		pc_rule1"sets_ext" prove_rule[]⌜{x|F} = {}⌝,
		empty_finite_thm]));
=TEX
\newpage
\subsection{Specifying the Operations on the Type}\label{ops}
We now introduce the operations on the type $\GA$.
First of all, we define the fixity of the infix operators.
=SML
app declare_infix[(300, "+⋎G"), (310, "*⋎G"), (310, "*⋎S")];
=TEX

Now we define the operations.
The following is adapted from definition~2 of~\cite{Arthan06b}.
The function
=INLINEFT
Mon⋎G
=TEX
\ maps a finite set of natural numbers $I$ to the monomial basis element $\E{I}$ of~\cite{Arthan06b}.
The definition has four conjuncts:
the first conjunct says that $\GA$ is an associative real algebra with a two-sided unit (cf. the check-list in~\cite{Macdonald02});
the second conjunct gives the rule for multiplying monomials;
the third conjunct says that the monomials
=INLINEFT
Mon⋎G I
=TEX
\ as $I$ ranges over finite sets of natural numbers generate $\GA$ as a linear space, or, more precisely, it says that if $V$ is a linear subspace of $\GA$ that contains each of these monomials, then $V = \GA$;
the final conjunct says that the monomials
=INLINEFT
Mon⋎G I
=TEX
\ as $I$ ranges over finite sets of natural numbers are linearly independent, or more precisely, it says that for each $J$, there is a linear subspace of $\GA$ that contains 
=INLINEFT
Mon⋎G I
=TEX
\ for all $I \not= J$, but does not contain
=INLINEFT
Mon⋎G J
=TEX
.


ⓈHOLCONST
│ $⦏+⋎G⦎ : GA → GA → GA;	⦏~⋎G⦎ : GA → GA;	⦏0⋎G⦎ : GA;
│				$⦏*⋎S⦎ : ℝ → GA → GA;
│ $⦏*⋎G⦎ : GA → GA → GA;	⦏1⋎G⦎ : GA;		⦏Mon⋎G⦎ : ℕ SET → GA
├──────
│ (∀u v w a b⦁
│	 	u +⋎G v = v +⋎G u
│	∧ 	(u +⋎G v) +⋎G w = u +⋎G v +⋎G w
│	∧ 	u +⋎G 0⋎G = u ∧ u +⋎G ~⋎G u = 0⋎G
│	∧ 	ℕℝ 1 *⋎S u = u ∧ a *⋎S (b *⋎S u) = (a * b) *⋎S u
│	∧ 	a *⋎S (u +⋎G v) = a *⋎S u +⋎G a *⋎S v
│	∧ 	(a + b) *⋎S u = a *⋎S u +⋎G b *⋎S u
│	∧ 	(u *⋎G v) *⋎G w = u *⋎G (v *⋎G w)
│	∧	u *⋎G (v +⋎G w) = u *⋎G v +⋎G u *⋎G w
│	∧	(v +⋎G w) *⋎G u = v *⋎G u +⋎G w *⋎G u
│	∧	(a *⋎S u) *⋎G v = a *⋎S u *⋎G v
│	∧	u *⋎G (a *⋎S v) = a *⋎S u *⋎G v
│	∧	1⋎G *⋎G u = u ∧ u *⋎G 1⋎G = u ∧ 1⋎G = Mon⋎G {})
│ ∧ (∀I J⦁	I ∈ Finite ∧ J ∈ Finite
│	⇒	Mon⋎G I *⋎G Mon⋎G J = Sign⋎G I J *⋎S Mon⋎G(I ⊖ J))
│ ∧ (∀V⦁	(∀I⦁ I ∈ Finite ⇒ Mon⋎G I ∈ V)
│	∧	(∀a u⦁ u ∈ V ⇒ a *⋎S u ∈ V)
│	∧	(∀u v⦁ u ∈ V ∧ v ∈ V ⇒ u +⋎G v ∈ V)
│	⇒	(∀u⦁ u ∈ V))
│ ∧ (∀J⦁	J ∈ Finite
│	⇒	∃V⦁	(∀I⦁ ¬I = J ∧ I ∈ Finite ⇒ Mon⋎G I ∈ V)
│ 		∧	(∀a u⦁ u ∈ V ⇒ a *⋎S u ∈ V)
│ 		∧	(∀u v⦁ u ∈ V ∧ v ∈ V ⇒ u +⋎G v ∈ V)
│ 		∧	¬Mon⋎G J ∈ V)
■

We now define various derived operations.
The first two are binary subtraction and exponentiation with a natural number exponent:
=SML
declare_infix(305, "-⋎G");
ⓈHOLCONST
│ $⦏-⋎G⦎ : GA → GA → GA
├──────
│ ∀u v⦁ u -⋎G v = u +⋎G ~⋎G v
■
=SML
declare_infix(320, "^⋎G");
ⓈHOLCONST
│ $⦏^⋎G⦎ : GA → ℕ → GA
├──────
│	(∀u⦁ u ^⋎G 0 = 1⋎G)
│ ∧	(∀u m⦁ u ^⋎G (m+1) = u *⋎G u ^⋎G m)
■

The function
=INLINEFT
E⋎G
=TEX
\ that maps an natural number $i$ to the element $\E{i}$ of~\cite{Arthan06b}.

ⓈHOLCONST
│ ⦏E⋎G⦎ : ℕ → GA
├──────
│ ∀ m⦁ E⋎G m = Mon⋎G {m}
■
The following function gives the embedding of the naturals in $\GA$.
(Since it is so widely used, we will usually use the alias $\Gamma$ for this function, see below).

ⓈHOLCONST
│ ⦏ℕ⋎G⦎ : ℕ → GA
├──────
│ ℕ⋎G 0 = 0⋎G ∧ ∀ m⦁ ℕ⋎G (m+1) = ℕ⋎G m +⋎G 1⋎G
■

We now define aliases for the embedding of the naturals and for the ring operations on $\GA$ etc., (but not for the scalar multiplication since that does not work well with the current treatment of overloading in \ProductHOL).

=SML
declare_alias("Γ", ⌜ℕ⋎G⌝);
declare_alias("+", ⌜$+⋎G⌝);
declare_alias("*", ⌜$*⋎G⌝);
declare_alias("~", ⌜~⋎G⌝);
declare_alias("-", ⌜$-⋎G⌝);
declare_alias("^", ⌜$^⋎G⌝);
=TEX

Many of the theorems in the following block mimic ones provided in the developmet of the real numbers, up to the point where the non-commutativity of multiplication in $\GA$ begins to make a significant difference.

\ThmsIII{%
=GFT
ga_ops_def
ga_plus_assoc_thm
ga_plus_comm_thm
ga_plus_zero_thm
ga_plus_order_thm
ga_plus_0_thm
ga_0_1_thm
ga_plus_minus_thm
ga_eq_thm
Γ_plus_homomorphism_thm
ga_one_scale_thm
=TEX
}{%
=GFT
ga_scale_scale_assoc_thm
ga_scale_plus_distrib_thm
ga_plus_scale_distrib_thm
ga_times_assoc_thm
ga_times_plus_distrib_thm
ga_plus_times_distrib_thm
ga_scale_times_assoc_thm
ga_one_times_thm
ga_times_one_thm
ga_mon_times_mon_thm 
ga_minus_clauses
=TEX
}{%
=GFT
ga_minus_eq_thm
ga_0_times_thm
ga_0_scale_thm
ga_scale_0_thm
ga_minus_1_scale_thm
ga_ℕ_exp_clauses
ga_minus_scale_thm
ga_scale_minus_thm
ga_one_mon_thm
ga_mon_span_thm
ga_mon_indep_thm
=TEX
}

\subsection{Some Linear Space Notions}
(Note: we use the term {\em linear space} for the usual notion of a vector space to avoid confusion with the privileged role of the 1-vectors in $\GA$).

We define the notion of a linear subspace of $\GA$:

ⓈHOLCONST
│ ⦏Subspace⋎G⦎ : GA SET SET
├──────
│ ∀V⦁	V ∈ Subspace⋎G ⇔
│		0⋎G ∈ V
│	∧	(∀a u⦁ u ∈ V ⇒ a *⋎S u ∈ V)
│	∧	(∀u v⦁ u ∈ V ∧ v ∈ V ⇒ u + v ∈ V)
■
The linear space spanned by a subset of $\GA$ is defined as follows:

ⓈHOLCONST
│ ⦏Span⋎G⦎ : GA SET → GA SET
├──────
│ ∀X⦁	Span⋎G X = ⋂{V | V ∈ Subspace⋎G ∧ X ⊆ V}
■
A set $X$ is linearly independent iff. the spans of its proper subsets are proper subsets of its span.
ⓈHOLCONST
│ ⦏Indep⋎G⦎ : GA SET SET
├──────
│ ∀X⦁ X ∈ Indep⋎G ⇔ ∀Y⦁Y ⊆ X ∧ Span⋎G Y = Span⋎G X ⇒ Y = X
■
\ThmsIII{%
=GFT
finite_friend_thm
ga_mon_not_0_thm
ga_mon_1_thm
ga_mon_subgroup_thm
ga_vec_generators_thm
ga_vec_relations_thm
=TEX
}{%
=GFT
ga_vec_indep_thm
ga_span_subspace_thm
ga_⊆_span_thm
ga_span_⊆_thm
ga_trivial_subspaces_thm
ga_mon_span_bc_thm
=TEX
}{%
=GFT
ga_span_mon_thm
ga_span_mono_thm
ga_indep_thm
ga_mon_indep_thm1
=TEX
}
\subsection{Some Simple Geometric Notions}
In this section we define some simple geometric notions.
We restrict some of these to vectors, the set of vectors being the span of the $\E{i}$.
ⓈHOLCONST
│ $⦏Vector⋎G⦎ : GA SET
├──────
│ Vector⋎G = Span⋎G {e | ∃m⦁e = E⋎G m}
■

Vectors $u$ and $v$ are orthogonal, written $u \perp v$, if they anticommute:

=SML
declare_infix(200, "⊥");
ⓈHOLCONST
│ $⦏⊥⦎ : GA → GA → BOOL
├──────
│ ∀u v⦁ u ⊥ v ⇔ u ∈ Vector⋎G ∧ v ∈ Vector⋎G ∧ u * v = ~ v * u
■

With these definitions in hand, it is purely a matter of algebra to prove the theorem of Pythagoras, which in the geometric algebra becomes a theorem about the squares {\em of} the sides, not the squares {\em on} the sides:

{\vertbarfalse
=GFT
pythagoras_thm ⊢ ∀ u v: GA⦁ u ⊥ v ⇒ (u - v) ^ 2 = u ^ 2 + v ^ 2
=TEX
}


{\raggedright
\bibliographystyle{plain}
\bibliography{fmu}}

=TEX
\newpage
\section{OPERATIONS ON THE REPRESENTATION TYPE}\label{representatives}

The proof of the consistency of the specification of the operations of $\GA$ in section~\ref{ops} is made tolerable by introducing constants for the representatives of the operations on the representation type.
This appendix gives the definitons of these operations.

We adopt the convention of using an initial `\_' to distinguish operations on the representation type from corresponding operations on the new type.
=SML
declare_infix(300, "_+⋎G");
=TEX

ⓈHOLCONST
│ $⦏_+⋎G⦎ : _GA → _GA → _GA
├──────
│ ∀ v w⦁ v _+⋎G w = λK⦁ v K + w K
■
ⓈHOLCONST
│ ⦏_~⋎G⦎ : _GA → _GA
├──────
│ ∀ v⦁ _~⋎G v = λK⦁ ~(v K)
■
=SML
declare_infix(310, "_*⋎G");
=TEX

ⓈHOLCONST
│ $⦏_*⋎G⦎ : _GA → _GA → _GA
├──────
│ ∀ v w⦁
│	v _*⋎G w = λK⦁
│	Σ {(I, J) | I ∈ Supp v ∧ J ∈ Supp w ∧ K = I ⊖ J}
│	(λ(I, J)⦁ Sign⋎G I J * v I * w J)
■
=SML
declare_infix(310, "_*⋎S");
=TEX

ⓈHOLCONST
│ $⦏_*⋎S⦎ : ℝ → _GA → _GA
├──────
│ ∀ c v⦁ c _*⋎S v = λK⦁c * v K
■

ⓈHOLCONST
│ ⦏_0⋎G⦎ : _GA
├──────
│ _0⋎G = λK⦁ ℕℝ 0
■
ⓈHOLCONST
│ ⦏_1⋎G⦎ : _GA
├──────
│ _1⋎G = χ{{}}
■

\appendix
{%\HOLindexOff
\let\Section\section
\let\subsection\Hide
\def\section#1{\Section{#1}\label{listing}}
\let\subsection\Hide
\include{wrk076.th}}

\twocolumn[\section*{INDEX}\label{INDEX}]
\addcontentsline{toc}{section}{INDEX}
{\small\printindex}

\end{document} %% COMMENT THIS LINE OUT TO TYPESET THE PROOF SCRIPTS
=TEX
%%%%
%%%%
=SML
=SML
=TEX
%%%%
%%%%

=TEX

=SML

val ⦏⊖_def⦎ = get_spec⌜$⊖⌝;
val ⦏⊖_def1⦎ = tac_proof(([],
	⌜∀a b⦁a ⊖ b = (a \ b) ∪ (b \ a)⌝),
	PC_T1 "sets_ext" rewrite_tac[⊖_def] THEN taut_tac);
=TEX
=SML

val ⦏sign_g_def⦎ = get_spec⌜Sign⋎G⌝;
val ⦏plus_g_def⦎ = get_spec⌜$_+⋎G⌝;
val ⦏minus_g_def⦎ = get_spec⌜_~⋎G⌝;
val ⦏times_g_def⦎ = get_spec⌜$_*⋎G⌝;
val ⦏times_s_def⦎ = get_spec⌜$_*⋎S⌝;
val ⦏zero_g_def⦎ = get_spec⌜_0⋎G⌝;
val ⦏one_g_def⦎ = get_spec⌜_1⋎G⌝;
val ⦏is_ga_rep_def⦎ = get_spec⌜_IsGARep⌝;
=TEX
=SML

val ⦏mod_2_clauses⦎ = rewrite_rule[] (∀_elim⌜2⌝mod_clauses);
=TEX
%%%%
%%%%

=SML

val ⦏⊖_group_thm⦎ = save_thm( "⊖_group_thm", (
set_goal([], ⌜∀a b c⦁
	a ⊖ {} = a
∧	{} ⊖ a = a
∧	a ⊖ b = b ⊖ a
∧	a ⊖ b ⊖ c = (a ⊖ b) ⊖ c⌝);
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊖_comm_thm⦎ = save_thm( "⊖_comm_thm", (
set_goal([], ⌜∀a b⦁ a ⊖ b = b ⊖ a⌝);
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊖_assoc_thm⦎ = save_thm( "⊖_assoc_thm", (
set_goal([], ⌜∀a b c⦁
	(a ⊖ b) ⊖ c = a ⊖ b ⊖ c⌝);
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊖_lemmas⦎ = save_thm( "⊖_lemmas", (
set_goal([], ⌜∀a b⦁
	a ⊖ {} = a
∧	{} ⊖ a = a
∧	a ⊖ a = {}
∧	a ⊖ a = {}⌝);
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊖_inverse_thm⦎ = (* save_thm *) snd("⊖_inverse_thm", (
set_goal([], ⌜∀a b c⦁ a = b ⊖ c ⇔ c = b ⊖ a⌝);
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
set_goal([], ⌜
	a ⊖ a  = {}
∧	a ⊖ a ⊖ b = b
∧	{} ⊖ a = a
∧	a ⊖ {} = a
∧	a ⊖ {} ⊖ b = a ⊖ b⌝);
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
val ⦏⊖_simp_thm⦎ = pop_thm();
val ⦏⊖_simp_conv⦎ =
	let	val conv1 = FIRST_C(
			map (simple_eq_match_conv o all_∀_intro)
			(strip_∧_rule ⊖_simp_thm));
	in	conv1 THEN_C REPEAT_C conv1
	end;
fun ⦏⊖_nf_conv⦎ (ty : TYPE) = sort_conv term_order
	(inst_type_rule[(ty, ⓣ'a⌝)] ⊖_comm_thm)
	(inst_type_rule[(ty, ⓣ'a⌝)] ⊖_assoc_thm)
	⊖_simp_conv fail_conv;
=IGN
⊖_nf_conv ⓣ'a⌝ ⌜b ⊖ a⌝;
⊖_nf_conv  ⓣ'a⌝ ⌜a ⊖ b⌝;
⊖_nf_conv ⓣ'a⌝  ⌜a ⊖ b ⊖ a⌝;
⊖_nf_conv ⓣ'a⌝  ⌜a ⊖ b ⊖ (c ⊖ {}) ⊖ {} ⊖ {} ⊖ c ⊖ a⌝;
⊖_nf_conv ℕ ⌜(x ⊖ (x ⊖ z) ⊖ {1})⌝;
=TEX
%%%%
%%%%

=SML

val ⦏⊖_eq_∪_thm⦎ = (* save_thm *) snd("⊖_eq_∪_thm", (
set_goal([], ⌜∀a b⦁
	a ∩ b = {} ⇔ a ⊖ b = a ∪ b⌝);
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊖_finite_thm⦎ = save_thm( "⊖_finite_thm", (
set_goal([], ⌜∀a b⦁ a ∈ Finite ∧ b ∈ Finite ⇒ a ⊖ b ∈ Finite⌝);
a(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm
	THEN ∃_tac⌜a ∪ b⌝
	THEN asm_rewrite_tac[⊖_def1, ∪_finite_thm]
	THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏size_⊖_lemma⦎ = save_thm( "size_⊖_lemma", (
set_goal([], ⌜∀f a b⦁
	f {} = 0
∧	(∀a b⦁ a ∈ Finite ∧ b ∈ Finite
	⇒	f(a ∪ b) + f(a ∩ b) = f a + f b)
∧	a ∈ Finite
∧	b ∈ Finite
⇒	f(a ⊖ b) + 2*f(a ∩ b) = f a + f b
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜a ∪ b ∈ Finite⌝ THEN1 asm_rewrite_tac[∪_finite_thm]);
a(lemma_tac⌜a ∩ b ∈ Finite⌝ THEN1 ALL_FC_T rewrite_tac[∩_finite_thm]);
a(lemma_tac⌜a ⊖ b ∈ Finite⌝ THEN1 all_fc_tac[⊖_finite_thm]);
a(LIST_SPEC_NTH_ASM_T 6 [⌜a ⊖ b⌝, ⌜a ∩ b⌝] ante_tac);
a(LIST_SPEC_NTH_ASM_T 6 [⌜a⌝, ⌜b⌝] ante_tac);
a(DROP_NTH_ASM_T 6 discard_tac);
a(LEMMA_T ⌜(a ⊖ b) ∪ a ∩ b = a ∪ b ∧ (a ⊖ b) ∩ a ∩ b = {}⌝
	asm_rewrite_thm_tac
	THEN1 (rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]));
a(PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊖_finite_size_thm⦎ = save_thm( "⊖_finite_size_thm", (
set_goal([], ⌜∀a b⦁
	a ∈ Finite
∧	b ∈ Finite
⇒	a ⊖ b ∈ Finite
∧	#(a ⊖ b) + 2 * #(a ∩ b) = #a + #b
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜a ∪ b⌝);
a(asm_rewrite_tac[∪_finite_thm, ⊖_def1]
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(bc_thm_tac size_⊖_lemma);
a(asm_rewrite_tac[size_empty_thm, size_∪_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊖_infinite_thm⦎ = save_thm( "⊖_infinite_thm", (
set_goal([], ⌜∀a b⦁
	¬a ∈ Finite
∧	b ∈ Finite
⇒	¬a ⊖ b ∈ Finite
⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜b⌝ THEN1 asm_rewrite_tac[⊖_lemmas]);
a(swap_nth_asm_concl_tac 2);
a(bc_thm_tac ⊆_finite_thm THEN1 ∃_tac ⌜{x} ∪ (a ⊖ ({x} ∪ b'))⌝
	THEN asm_rewrite_tac[∪_finite_thm, singleton_finite_thm]);
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_g_lemma1⦎ = (* save_thm *) snd("sign_g_lemma1", (
set_goal([], ⌜∀t a b c⦁
	(∀a⦁t a {} = 0)
∧	(∀a b c⦁a ∈ Finite ∧ b ∈ Finite ∧ c ∈ Finite
	⇒	t a (b ∪ c) + t a (b ∩ c) = t a b + t a c)
∧	a ∈ Finite ∧ b ∈ Finite ∧ c ∈ Finite
⇒	t a (b ⊖ c) + 2 * t a (b ∩ c) = t a b + t a c
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac size_⊖_lemma THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_g_lemma2⦎ = (* save_thm *) snd("sign_g_lemma2", (
set_goal([], ⌜∀t a b c⦁
	(∀a⦁t {} a = 0)
∧	(∀a b c⦁a ∈ Finite ∧ b ∈ Finite ∧ c ∈ Finite
	⇒	t (a ∪ b) c + t (a ∩ b) c = t a c + t b c)
∧	a ∈ Finite ∧ b ∈ Finite ∧ c ∈ Finite
⇒	t (a ⊖ b) c + 2 * t (a ∩ b) c = t a c + t b c
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac(rewrite_rule[](∀_elim⌜λx y⦁ t y x⌝ sign_g_lemma1)));
a(asm_rewrite_tac[] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_g_lemma4⦎ = (* save_thm *) snd("sign_g_lemma4", (
set_goal([], ⌜∀t a b c⦁
	(∀a⦁t a {} = 0)
∧	(∀a b c⦁a ∈ Finite ∧ b ∈ Finite ∧ c ∈ Finite
	⇒	t a (b ∪ c) + t a (b ∩ c) = t a b + t a c)
∧	(∀a⦁t {} a = 0)
∧	(∀a b c⦁a ∈ Finite ∧ b ∈ Finite ∧ c ∈ Finite
	⇒	t (a ∪ b) c + t (a ∩ b) c = t a c + t b c)
∧	a ∈ Finite ∧ b ∈ Finite ∧ c ∈ Finite
⇒	(t a b + t (a ⊖ b) c) Mod 2 = (t a (b ⊖ c) + t b c) Mod 2
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜
	((t a b + t (a ⊖ b) c) + 2 * t (a ∩ b) c) Mod 2 =
	((t a (b ⊖ c) + t b c) + 2 * t a (b ∩ c)) Mod 2⌝
	(accept_tac o rewrite_rule[mod_2_clauses]));
a(LEMMA_T ⌜((t a (b ⊖ c) + t b c) + 2 * t a (b ∩ c)) =
	((t a b + t (a ⊖ b) c) + 2 * t (a ∩ b) c)⌝
	rewrite_thm_tac);
a(conv_tac(RIGHT_C (rewrite_conv[plus_assoc_thm])));
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜∀i j k:ℕ⦁(i + j) + k = j + i + k⌝]);
a(ALL_FC_T rewrite_tac[sign_g_lemma1, sign_g_lemma2]);
a(PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ℝ_ℕ_exp_mod_2_thm⦎ = save_thm( "ℝ_ℕ_exp_mod_2_thm", (
set_goal([], ⌜∀m⦁
	 ~(ℕℝ 1) ^ m = ~(ℕℝ 1) ^ (m Mod 2)
⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜m⌝ mod_2_cases_thm)
	THEN ALL_FC_T asm_rewrite_tac[mod_2_0_ℝ_ℕ_exp_thm, mod_2_1_ℝ_ℕ_exp_thm]
	THEN rewrite_tac[ℝ_ℕ_exp_0_1_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_g_lemma5⦎ = (* save_thm *) snd("sign_g_lemma5", (
set_goal([], ⌜∀I J K:ℕ SET⦁
	{(i, j)|i ∈ I ∪ J ∧ j ∈ K ∧ j < i} =
	{(i, j)|i ∈ I ∧ j ∈ K ∧ j < i} ∪
	{(i, j)|i ∈ J ∧ j ∈ K ∧ j < i}
∧	{(i, j)|i ∈ I ∧ j ∈ J ∪ K ∧ j < i} =
	{(i, j)|i ∈ I ∧ j ∈ J ∧ j < i} ∪
	{(i, j)|i ∈ I ∧ j ∈ K ∧ j < i}
∧	{(i, j)|i ∈ I ∩ J ∧ j ∈ K ∧ j < i} =
	{(i, j)|i ∈ I ∧ j ∈ K ∧ j < i} ∩
	{(i, j)|i ∈ J ∧ j ∈ K ∧ j < i}
∧	{(i, j)|i ∈ I ∧ j ∈ J ∩ K ∧ j < i} =
	{(i, j)|i ∈ I ∧ j ∈ J ∧ j < i} ∩
	{(i, j)|i ∈ I ∧ j ∈ K ∧ j < i}
⌝);
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_g_lemma6⦎ = (* save_thm *) snd("sign_g_lemma6", (
set_goal([], ⌜∀I J:ℕ SET⦁
	I ∈ Finite ∧ J ∈ Finite
⇒	{(i, j)|i ∈ I ∧ j ∈ J ∧ j < i} ∈ Finite
⌝);
a(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm);
a(∃_tac⌜I × J⌝ THEN ALL_FC_T rewrite_tac[×_finite_size_thm]);
a(rewrite_tac[×_def] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_g_thm⦎ = save_thm( "sign_g_thm", (
set_goal([], ⌜∀I J K:ℕ SET⦁
	I ∈ Finite
∧	J ∈ Finite
∧	K ∈ Finite
⇒	Sign⋎G I J * Sign⋎G (I ⊖ J) K
=	Sign⋎G I (J ⊖ K) * Sign⋎G J K
⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[
	sign_g_def,
	conv_rule(ONCE_MAP_C eq_sym_conv) ℝ_ℕ_exp_plus_thm]);
a(once_rewrite_tac[ℝ_ℕ_exp_mod_2_thm]);
a(bc_thm_tac(prove_rule[]⌜∀x:ℝ; i j :ℕ⦁ i = j ⇒ x^i = x^j⌝));
a(bc_thm_tac(rewrite_rule[](∀_elim⌜λa b:ℕ SET⦁# {(i, j)|i ∈ a ∧ j ∈ b ∧ j < i}⌝ sign_g_lemma4)));
a(asm_rewrite_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜{(i, j)|F} = {}⌝,
	size_empty_thm]);
a(DROP_ASMS_T discard_tac THEN rewrite_tac[sign_g_lemma5]);
a(REPEAT strip_tac THEN bc_thm_tac size_∪_thm
	THEN ALL_FC_T rewrite_tac[sign_g_lemma6]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_g_cases_thm⦎ = save_thm( "sign_g_cases_thm", (
set_goal([], ⌜∀I J⦁
	 Sign⋎G I J = ℕℝ 1 ∨ Sign⋎G I J = ~(ℕℝ 1)
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[sign_g_def]);
a(strip_asm_tac (∀_elim⌜# {(i, j)|i ∈ I ∧ j ∈ J ∧ j < i}⌝ mod_2_cases_thm)
	THEN ALL_FC_T asm_rewrite_tac[mod_2_0_ℝ_ℕ_exp_thm, mod_2_1_ℝ_ℕ_exp_thm]
	THEN rewrite_tac[ℝ_ℕ_exp_0_1_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_singleton_thm⦎ = save_thm( "sign_singleton_thm", (
set_goal([], ⌜ ∀i⦁ Sign⋎G {i} {i} = ℕℝ 1 ⌝);
a(REPEAT strip_tac THEN rewrite_tac[sign_g_def]);
a(LEMMA_T ⌜{(i', j)|i' = i ∧ j = i ∧ j < i'} = {}⌝ rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" REPEAT strip_tac
		THEN all_var_elim_asm_tac1));
a(rewrite_tac[size_empty_thm, ℝ_ℕ_exp_0_1_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏sign_singletons_thm⦎ = save_thm( "sign_singletons_thm", (
set_goal([], ⌜ ∀i j⦁ ¬i = j ⇒ Sign⋎G {i} {j} =
	if i < j then ℕℝ 1 else ~(ℕℝ 1) ⌝);
a(REPEAT strip_tac THEN rewrite_tac[sign_g_def]);
a(PC_T1 "predicates" cases_tac⌜i < j⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜{(i', j')| i' = i ∧ j' = j ∧ j' < i'} = {}⌝ rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" REPEAT strip_tac
		THEN all_var_elim_asm_tac1
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(rewrite_tac[size_empty_thm, ℝ_ℕ_exp_0_1_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜{(i', j')| i' = i ∧ j' = j ∧ j' < i'} = {(i, j)}⌝ rewrite_thm_tac
	THEN1 (PC_T "sets_ext1" strip_tac
		THEN REPEAT strip_tac
		THEN all_var_elim_asm_tac1
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(rewrite_tac[size_singleton_thm, ℝ_ℕ_exp_0_1_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_g_finite_thm⦎ = (* save_thm *) snd("times_g_finite_thm", (
set_goal([], ⌜∀v w K⦁
	Supp v ∈ Finite ∨ Supp w ∈ Finite
⇒	 {(I, J)|I ∈ Supp v ∧ J ∈ Supp w ∧ K = I ⊖ J} ∈ Finite
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm);
a(∃_tac⌜{(I, J) | I ∈ Supp v ∧ K = I ⊖ J}⌝
	THEN REPEAT strip_tac
	THEN_LIST [id_tac,  PC_T1 "sets_ext1" prove_tac[]]);
a(lemma_tac⌜{(I, J)|I ∈ Supp v ∧ K = I ⊖ J} ∈ Finite ∧
	#{(I, J)|I ∈ Supp v ∧ K = I ⊖ J} = #(Supp v)⌝
	THEN1 bc_thm_tac bijection_finite_size_thm);
a(once_rewrite_tac[⊖_inverse_thm]);
a(∃_tac⌜λI⦁(I, I ⊖ K)⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN rewrite_tac[]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1
	THEN REPEAT strip_tac);
a(∃_tac⌜x1⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm);
a(∃_tac⌜{(I, J) | J ∈ Supp w ∧ K = I ⊖ J}⌝
	THEN REPEAT strip_tac
	THEN_LIST [id_tac,  PC_T1 "sets_ext1" prove_tac[]]);
a(lemma_tac⌜{(I, J)| J ∈ Supp w ∧ K = I ⊖ J} ∈ Finite ∧
	#{(I, J)| J ∈ Supp w ∧ K = I ⊖ J} = #(Supp w)⌝
	THEN1 bc_thm_tac bijection_finite_size_thm);
a(once_rewrite_tac[⊖_group_thm]);
a(once_rewrite_tac[⊖_inverse_thm]);
a(∃_tac⌜λJ⦁(J ⊖ K, J)⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN rewrite_tac[]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1
	THEN REPEAT strip_tac);
a(∃_tac⌜x2⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏supp_times_s_thm⦎ = (* save_thm *) snd("supp_times_s_thm", (
set_goal([], ⌜∀c v⦁
	¬c = ℕℝ 0 ⇒ Supp (c _*⋎S v) = Supp v
⌝);
a(REPEAT strip_tac THEN PC_T1 "sets_ext1" rewrite_tac[supp_def, times_s_def]
	THEN ∀_tac);
a(cases_tac⌜v x = ℕℝ 0⌝ THEN asm_rewrite_tac[ℝ_times_eq_0_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏supp_zero_one_g_thm⦎ = (* save_thm *) snd("supp_zero_one_g_thm", (
set_goal([], ⌜∀A⦁
	Supp _0⋎G = {}
∧	Supp _1⋎G = {{}}
⌝);
a(rewrite_tac[zero_g_def, one_g_def, supp_χ_thm, supp_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_g_def1⦎ = (* save_thm *) snd("times_g_def1", (
set_goal([], ⌜∀v w⦁
	Supp v ∈ Finite
⇒	v _*⋎G w =
	λK⦁ Σ (Supp v) (λ I⦁ Sign⋎G I (K ⊖ I) * v I * w (K ⊖ I))
⌝);
a(REPEAT strip_tac THEN rewrite_tac[times_g_def]);
a(lemma_tac⌜{(I, J)|I ∈ Supp v ∧ J ∈ Supp w ∧ x = I ⊖ J} ∈ Finite⌝
	THEN1 ALL_FC_T asm_rewrite_tac[times_g_finite_thm]);
a(conv_tac eq_sym_conv);
a(bc_thm_tac ind_sum_transfer_thm);
a(rename_tac[(⌜x⌝, "K")] THEN ∃_tac⌜λI⦁ (I, K ⊖ I)⌝
	THEN PC_T1 "predicates" asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac);
a(rewrite_tac[ℝ_times_eq_0_thm, supp_def]
	THEN taut_tac);
(* *** Goal "2" *** *)
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "3" *** *)
a(rewrite_tac[]);
(* *** Goal "4" *** *)
a(lemma_tac⌜∀a b c:ℕ SET⦁((a ⊖ b) ⊖ a) = b⌝
	THEN1 (rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]));
a(∃⋎1_tac⌜Fst y⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_g_def2⦎ = (* save_thm *) snd("times_g_def2", (
set_goal([], ⌜∀v w⦁
	Supp w ∈ Finite
⇒	v _*⋎G w =
	λK⦁ Σ (Supp w) (λ J⦁ Sign⋎G (K ⊖ J) J * v (K ⊖ J) * w J)
⌝);
a(REPEAT strip_tac THEN rewrite_tac[times_g_def]);
a(lemma_tac⌜{(I, J)|I ∈ Supp v ∧ J ∈ Supp w ∧ x = I ⊖ J} ∈ Finite⌝
	THEN1 ALL_FC_T asm_rewrite_tac[times_g_finite_thm]);
a(conv_tac eq_sym_conv);
a(bc_thm_tac ind_sum_transfer_thm);
a(rename_tac[(⌜x⌝, "K")] THEN ∃_tac⌜λJ⦁ (K ⊖ J, J)⌝
	THEN PC_T1 "predicates" asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac);
a(rewrite_tac[ℝ_times_eq_0_thm, supp_def]
	THEN taut_tac);
(* *** Goal "2" *** *)
a(rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "3" *** *)
a(rewrite_tac[]);
(* *** Goal "4" *** *)
a(lemma_tac⌜∀a b c:ℕ SET⦁((b ⊖ a) ⊖ a) = b⌝
	THEN1 (rewrite_tac[⊖_def1] THEN PC_T1 "sets_ext1" prove_tac[]));
a(∃⋎1_tac⌜Snd y⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏zero_times_s_thm⦎ = (* save_thm *) snd("zero_times_s_thm", (
set_goal([], ⌜∀v⦁
	ℕℝ 0 _*⋎S v = _0⋎G
⌝);
a(REPEAT strip_tac THEN rewrite_tac[zero_g_def, times_s_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏zero_times_g_thm⦎ = (* save_thm *) snd("zero_times_g_thm", (
set_goal([], ⌜∀v⦁
	_0⋎G _*⋎G v = _0⋎G
∧	v _*⋎G _0⋎G = _0⋎G
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[times_g_def]);
a(rewrite_tac[supp_zero_one_g_thm, pc_rule1 "sets_ext1" prove_rule[]
	⌜{(a, b)|F} = {}⌝,
	ind_sum_def]);
a(rewrite_tac[zero_g_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏plus_g_comm_thm⦎ = (* save_thm *) snd("plus_g_comm_thm", (
set_goal([], ⌜∀u v⦁
	u _+⋎G v = v _+⋎G u
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[plus_g_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏plus_g_assoc_thm⦎ = (* save_thm *) snd("plus_g_assoc_thm", (
set_goal([], ⌜∀u v w⦁
	(u _+⋎G v) _+⋎G w = u _+⋎G (v _+⋎G w)
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[plus_g_def, ℝ_plus_assoc_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏plus_g_0_thm⦎ = (* save_thm *) snd("plus_g_0_thm", (
set_goal([], ⌜∀u⦁
	u _+⋎G _0⋎G = u
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[plus_g_def, zero_g_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏plus_g_minus_g_thm⦎ = (* save_thm *) snd("plus_g_minus_g_thm", (
set_goal([], ⌜∀u⦁
	u _+⋎G (_~⋎G u) = _0⋎G
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[plus_g_def, minus_g_def, zero_g_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏one_times_s_thm⦎ = (* save_thm *) snd("one_times_s_thm", (
set_goal([], ⌜∀u⦁
	ℕℝ 1 _*⋎S u = u
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[times_s_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_s_times_s_thm⦎ = (* save_thm *) snd("times_s_times_s_thm", (
set_goal([], ⌜∀a b u⦁
	a _*⋎S (b _*⋎S u) = (a * b) _*⋎S u
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[times_s_def, ℝ_times_assoc_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_s_plus_g_distrib_thm⦎ = (* save_thm *) snd("times_s_plus_g_distrib_thm", (
set_goal([], ⌜∀a u v⦁
	a _*⋎S (u _+⋎G v) = (a _*⋎S u) _+⋎G (a _*⋎S v)
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[times_s_def, plus_g_def, ℝ_times_plus_distrib_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏plus_times_s_distrib_thm⦎ = (* save_thm *) snd("plus_times_s_distrib_thm", (
set_goal([], ⌜∀a b u⦁
	(a + b) _*⋎S u = (a _*⋎S u) _+⋎G (b _*⋎S u)
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[times_s_def, plus_g_def, ℝ_times_plus_distrib_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_g_assoc_thm⦎ = (* save_thm *) snd("times_g_assoc_thm", (
set_goal([], ⌜∀u v w⦁
	Supp u ∈ Finite ∧ Supp u ⊆ Finite
∧	Supp v ∈ Finite ∧ Supp v ⊆ Finite
∧	Supp w ∈ Finite ∧ Supp w ⊆ Finite
⇒	(u _*⋎G v) _*⋎G w = u _*⋎G (v _*⋎G w)
⌝);
a(REPEAT strip_tac);
a(PC_T1 "predicates" (ALL_FC_T rewrite_tac) [times_g_def2]);
a(PC_T1 "predicates" (ALL_FC_T rewrite_tac) [times_g_def1]);
a(LEMMA_T ⌜∀f; c:ℝ⦁Σ (Supp v) f * c = Σ (Supp v) (λI⦁f I * c)⌝
	rewrite_thm_tac
	THEN1 (once_rewrite_tac[ℝ_times_comm_thm]
		THEN ALL_FC_T rewrite_tac[ind_sum_const_times_thm]));
a(LEMMA_T ⌜∀f; c:ℝ⦁c * Σ (Supp v) f = Σ (Supp v) (λJ⦁c * f J)⌝
	rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[ind_sum_const_times_thm]);
a(LEMMA_T ⌜∀f; c:ℝ⦁c * Σ (Supp w) f = Σ (Supp w) (λJ⦁c * f J)⌝
	rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[ind_sum_const_times_thm]);
a(ALL_FC_T rewrite_tac[rewrite_rule[](∀_elim⌜(λ (K, L)⦁ Sign⋎G (x ⊖ K) K * (Sign⋎G ((x ⊖ K) ⊖ L) L * u ((x ⊖ K) ⊖ L) * v L) * r K)⌝
ind_sum_×_thm)]);
a(ALL_FC_T rewrite_tac[rewrite_rule[](∀_elim⌜λ(I, J)⦁Sign⋎G I (x ⊖ I) * u I * Sign⋎G ((x ⊖ I) ⊖ J) J * v ((x ⊖ I) ⊖ J) * w J⌝
ind_sum_×_thm)]);
a(lemma_tac⌜(Supp w × Supp v) ∈ Finite ∧ (Supp u × Supp w) ∈ Finite⌝
	THEN1 ALL_FC_T rewrite_tac[×_finite_size_thm]);
a(bc_thm_tac ind_sum_transfer_thm);
a(∃_tac⌜λ(K, L)⦁ ((x ⊖ K) ⊖ L, K)⌝
	THEN asm_rewrite_tac[]
	THEN rewrite_tac[×_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_times_eq_0_thm, supp_def]
	THEN taut_tac);
(* *** Goal "2" *** *)
a(conv_tac(ONCE_MAP_C(⊖_nf_conv(hd(snd(dest_ctype(type_of⌜x⌝)))))));
a(lemma_tac⌜Fst x' ∈ Finite ∧ Snd x' ∈ Finite⌝
	THEN1 LIST_DROP_NTH_ASM_T[6, 8]
		(PC_T1 "sets_ext1" (ALL_FC_T rewrite_tac)));
a(lemma_tac⌜Fst x' ⊖ Snd x' ∈ Finite⌝
	THEN1 all_fc_tac[⊖_finite_size_thm]);
a(cases_tac⌜¬x ∈ Finite⌝);
(* *** Goal "2.1" *** *)
a(lemma_tac⌜¬x ⊖ Fst x' ⊖ Snd x' ∈ Finite⌝
	THEN1 all_fc_tac[⊖_infinite_thm]);
a(cases_tac⌜x ⊖ Fst x' ⊖ Snd x' ∈ Supp u⌝
	THEN1 LIST_DROP_NTH_ASM_T[16]
		(PC_T1 "sets_ext1" all_fc_tac));
a(POP_ASM_T ante_tac THEN rewrite_tac[supp_def]);
a(STRIP_T rewrite_thm_tac);
(* *** Goal "2.2" *** *)
a(rewrite_tac[∀_elim⌜Sign⋎G (x ⊖ Fst x' ⊖ Snd x') (Snd x')⌝
	ℝ_times_order_thm]
	THEN rewrite_tac[ℝ_times_assoc_thm1]);
a(lemma_tac⌜x ⊖ Fst x' ⊖ Snd x' ∈ Finite⌝
	THEN1 all_fc_tac[⊖_finite_size_thm]);
a(LEMMA_T ⌜x ⊖ Fst x' = (x ⊖ Fst x' ⊖ Snd x') ⊖ Snd x'⌝
	rewrite_thm_tac
	THEN1 (conv_tac  (ONCE_MAP_C(⊖_nf_conv(hd(snd(dest_ctype(type_of⌜x⌝))))))
		THEN strip_tac));
a(ALL_FC_T rewrite_tac[sign_g_thm]);
a(LEMMA_T ⌜(Snd x' ⊖ Fst x') = (Fst x' ⊖ Snd x')⌝
	rewrite_thm_tac
	THEN1 (conv_tac  (ONCE_MAP_C(⊖_nf_conv(hd(snd(dest_ctype(type_of⌜x⌝))))))
		THEN strip_tac));
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "3" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_times_eq_0_thm]
	THEN REPEAT strip_tac);
a(∃⋎1_tac⌜(Snd y, (x ⊖ Fst y) ⊖ Snd y)⌝
	THEN1 asm_rewrite_tac[supp_def]
	THEN conv_tac  (ONCE_MAP_C(⊖_nf_conv(hd(snd(dest_ctype(type_of⌜x⌝)))))));
a(REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(lemma_tac⌜Fst y ∈ Finite ∧ Snd y ∈ Finite⌝
	THEN1 LIST_DROP_NTH_ASM_T[14, 10]
		(PC_T1 "sets_ext1" (ALL_FC_T rewrite_tac)));
a(lemma_tac⌜Fst y ⊖ Snd y ∈ Finite⌝
	THEN1 all_fc_tac[⊖_finite_size_thm]);
a(cases_tac⌜¬x ∈ Finite⌝);
(* *** Goal "3.1.1" *** *)
a(lemma_tac⌜¬x ⊖ Fst y ⊖ Snd y ∈ Finite⌝
	THEN1 all_fc_tac[⊖_infinite_thm]);
a(cases_tac⌜x ⊖ Fst y ⊖ Snd y ∈ Supp v⌝
	THEN1 LIST_DROP_NTH_ASM_T[18]
		(PC_T1 "sets_ext1" all_fc_tac));
a(POP_ASM_T ante_tac THEN rewrite_tac[supp_def]);
a(STRIP_T rewrite_thm_tac);
(* *** Goal "3.1.2" *** *)
a(rewrite_tac[∀_elim⌜Sign⋎G (Fst y) (x ⊖ Fst y ⊖ Snd y)⌝
	ℝ_times_order_thm]
	THEN rewrite_tac[ℝ_times_assoc_thm1]);
a(lemma_tac⌜x ⊖ Fst y ⊖ Snd y ∈ Finite⌝
	THEN1 all_fc_tac[⊖_finite_size_thm]);
a(LEMMA_T ⌜x ⊖ Snd y = Fst y ⊖ (x ⊖ Fst y ⊖ Snd y)⌝
	rewrite_thm_tac
	THEN1 (conv_tac  (ONCE_MAP_C(⊖_nf_conv(hd(snd(dest_ctype(type_of⌜x⌝))))))
		THEN strip_tac));
a(ALL_FC_T rewrite_tac[sign_g_thm]);
a(conv_tac(ONCE_MAP_C(⊖_nf_conv(hd(snd(dest_ctype(type_of⌜x⌝)))))));
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "3.2" *** *)
a(DROP_NTH_ASM_T 3 (rewrite_thm_tac o eq_sym_rule));
a(asm_rewrite_tac[]);
a(conv_tac(ONCE_MAP_C(⊖_nf_conv(hd(snd(dest_ctype(type_of⌜x⌝))))))
	THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_g_plus_g_distrib_thm⦎ = (* save_thm *) snd("times_g_plus_g_distrib", (
set_goal([], ⌜∀u v w⦁
	Supp u ∈ Finite
⇒	u _*⋎G (v _+⋎G w) = (u _*⋎G v) _+⋎G (u _*⋎G w)
∧	(v _+⋎G w) _*⋎G u = (v _*⋎G u) _+⋎G (w _*⋎G u)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(PC_T1 "predicates" (ALL_FC_T rewrite_tac)[times_g_def1, times_g_def2]);
a(rewrite_tac[plus_g_def, ℝ_times_plus_distrib_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(EXTEND_PC_T1 "'sho_rw" (ALL_FC_T rewrite_tac)[ind_sum_plus_thm]);
(* *** Goal "2" *** *)
a(EXTEND_PC_T1 "'sho_rw" (ALL_FC_T rewrite_tac)[ind_sum_plus_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_s_times_g_assoc_thm⦎ = (* save_thm *) snd("times_s_times_g_assoc_thm", (
set_goal([], ⌜∀u v a⦁
	Supp u ∈ Finite
∧	Supp v ∈ Finite
⇒	(a _*⋎S u) _*⋎G v = a _*⋎S (u _*⋎G v)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(cases_tac⌜a = ℕℝ 0⌝ THEN1 PC_T1 "predicates" asm_rewrite_tac[zero_times_s_thm, zero_times_g_thm]);
a(lemma_tac⌜Supp (a _*⋎S u) ∈ Finite⌝
	THEN1 ALL_FC_T asm_rewrite_tac[supp_times_s_thm]);
a(PC_T1 "predicates" (ALL_FC_T rewrite_tac)[times_g_def1]);
a(ALL_FC_T rewrite_tac[supp_times_s_thm]);
a(∀_tac THEN rewrite_tac[times_s_def]);
a(rewrite_tac[∀_elim⌜a⌝ℝ_times_order_thm]);
a(pure_rewrite_tac[prove_rule[]
	⌜ (λ I⦁ a * Sign⋎G I (x ⊖ I) * u I * v (x ⊖ I)) =
	λI⦁a * (λ I⦁ Sign⋎G I (x ⊖ I) * u I * v (x ⊖ I)) I ⌝]);
a(ALL_FC_T rewrite_tac[ind_sum_const_times_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_g_times_s_assoc_thm⦎ = (* save_thm *) snd("times_g_times_s_assoc_thm", (
set_goal([], ⌜∀u v a⦁
	Supp u ∈ Finite
∧	Supp v ∈ Finite
⇒	u _*⋎G (a _*⋎S v) = a _*⋎S (u _*⋎G v)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(cases_tac⌜a = ℕℝ 0⌝ THEN1 PC_T1 "predicates" asm_rewrite_tac[zero_times_s_thm, zero_times_g_thm]);
a(lemma_tac⌜Supp (a _*⋎S v) ∈ Finite⌝
	THEN1 ALL_FC_T asm_rewrite_tac[supp_times_s_thm]);
a(PC_T1 "predicates" (ALL_FC_T rewrite_tac)[times_g_def1]);
a(ALL_FC_T rewrite_tac[supp_times_s_thm]);
a(∀_tac THEN rewrite_tac[times_s_def]);
a(rewrite_tac[∀_elim⌜a⌝ℝ_times_order_thm]);
a(pure_rewrite_tac[prove_rule[]
	⌜ (λ I⦁ a * Sign⋎G I (x ⊖ I) * u I * v (x ⊖ I)) =
	λI⦁a * (λ I⦁ Sign⋎G I (x ⊖ I) * u I * v (x ⊖ I)) I ⌝]);
a(ALL_FC_T rewrite_tac[ind_sum_const_times_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏one_g_times_g_thm⦎ = (* save_thm *) snd("one_g_times_g_thm", (
set_goal([], ⌜∀u⦁
	_1⋎G _*⋎G u = u
∧	u _*⋎G _1⋎G = u
⌝);
a(REPEAT ∀_tac);
a(lemma_tac⌜Supp _1⋎G ∈ Finite⌝
	THEN1 rewrite_tac[supp_zero_one_g_thm, singleton_finite_thm]);
a(ALL_FC_T rewrite_tac[times_g_def1, times_g_def2]);
a(rewrite_tac[supp_zero_one_g_thm, ind_sum_singleton_thm,
	sign_g_def, ⊖_lemmas,
	pc_rule1 "sets_ext1" prove_rule[] ⌜{i|F} = {} ∧ {(i, j) | F} = {}⌝,
	size_empty_thm, one_g_def, χ_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏minus_one_times_g_thm⦎ = (* save_thm *) snd("minus_one_times_g_thm", (
set_goal([], ⌜∀u⦁~ (ℕℝ 1) _*⋎S u = _~⋎G u⌝);
a(rewrite_tac[times_s_def, minus_g_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏minus_g_minus_g_thm⦎ = (* save_thm *) snd("minus_g_minus_g_thm", (
set_goal([], ⌜∀u⦁_~⋎G(_~⋎G u) = u⌝);
a(rewrite_tac[minus_g_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_g_singleton_lemma⦎ = (* save_thm *) snd("times_g_singleton_lemma", (
set_goal([], ⌜∀I i j⦁
	I ⊖ {i} = {j} ⇔ i = j ∧ I = {} ∨ ¬i = j ∧ I = {i; j}
⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule[⊖_def1] 
⌜∀a b c⦁a ⊖ b = c ⇔ a = b ⊖ c⌝]);
a(REPEAT_UNTIL is_∨ strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1);
a(cases_tac⌜i = j⌝ THEN asm_rewrite_tac[⊖_lemmas]);
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule[] 
⌜{i; j} = {i} ∪ {j}⌝]);
a(lemma_tac⌜¬j = i⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac1));
a(LEMMA_T ⌜{i} ∩ {j} = {}⌝ ante_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(rewrite_tac[⊖_eq_∪_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[⊖_lemmas]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule[] 
⌜{i; j} = {i} ∪ {j}⌝]);
a(lemma_tac⌜¬j = i⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac1));
a(LEMMA_T ⌜{i} ∩ {j} = {}⌝ ante_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(rewrite_tac[⊖_eq_∪_thm] THEN STRIP_T rewrite_thm_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏app_if_thm⦎ = save_thm( "app_if_thm", (
set_goal([], ⌜∀p f g x⦁
	(if p then f else g) x = if p then f x else g x
⌝);
a(REPEAT strip_tac);
a(cases_tac⌜p⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏plus_g_finitary_thm⦎ = (* save_thm *) snd("plus_g_finitary_thm", (
set_goal([], ⌜∀u v⦁
	Supp u ∈ Finite ∧ Supp u ⊆ Finite
∧	Supp v ∈ Finite ∧ Supp v ⊆ Finite
⇒	Supp (u _+⋎G v) ∈ Finite ∧ Supp (u _+⋎G v) ⊆ Finite
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac⌜Supp (u _+⋎G v) ⊆ Supp u ∪ Supp v⌝
	THEN1 rewrite_tac[plus_g_def, supp_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜Supp u ∪ Supp v⌝
	THEN asm_rewrite_tac[∪_finite_thm]);
(* *** Goal "2" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀b c d⦁b ⊆ d ∧ c ⊆ d ⇒ b ∪ c ⊆ d⌝]
	THEN all_fc_tac[
		pc_rule1 "sets_ext1" prove_rule[]
		⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏χ_finite_finitary_thm⦎ = (* save_thm *) snd("χ_finite_finitary_thm", (
set_goal([], ⌜∀I⦁
	I ∈ Finite
⇒	Supp(χ{I}) ∈ Finite ∧ Supp(χ{I}) ⊆ Finite
⌝);
a(REPEAT strip_tac THEN rewrite_tac[supp_χ_thm, singleton_finite_thm]);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏zero_one_finitary_thm⦎ = (* save_thm *) snd("zero_one_finitary_thm", (
set_goal([], ⌜
	(Supp(_0⋎G) ∈ Finite ∧ Supp(_0⋎G) ⊆ Finite)
∧	Supp(_1⋎G) ∈ Finite ∧ Supp(_1⋎G) ⊆ Finite
⌝);
a(rewrite_tac[supp_zero_one_g_thm, empty_finite_thm, singleton_finite_thm]);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN REPEAT strip_tac);
a(asm_rewrite_tac[empty_finite_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_s_finitary_thm⦎ = (* save_thm *) snd("times_s_finitary_thm", (
set_goal([], ⌜∀a u⦁
	Supp u ∈ Finite ∧ Supp u ⊆ Finite
⇒	Supp (a _*⋎S u) ∈ Finite ∧ Supp (a _*⋎S u) ⊆ Finite
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(cases_tac⌜a = ℕℝ 0⌝);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[zero_times_s_thm, zero_times_g_thm,
	supp_zero_one_g_thm, empty_finite_thm]);
(* *** Goal "2" *** *)
a(ALL_FC_T asm_rewrite_tac[supp_times_s_thm]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏supp_times_g_thm⦎ = (* save_thm *) snd("supp_times_g_thm", (
set_goal([], ⌜∀u v⦁
	Supp u ∈ Finite
∧	Supp u ∈ Finite
⇒	Supp (u _*⋎G v) ⊆ {K | ∃I J⦁ I ∈ Supp u ∧ J ∈ Supp v ∧ K = I ⊖ J}
⌝);
a(REPEAT strip_tac THEN rewrite_tac[times_g_def]);
a(conv_tac(LEFT_C(once_rewrite_conv[supp_def])));
a(PC_T1 "sets_ext" once_rewrite_tac[]
	THEN contr_tac);
a(swap_nth_asm_concl_tac 2 THEN rewrite_tac[]);
a(bc_thm_tac ind_sum_0_bc_thm);
a(REPEAT strip_tac THEN1 bc_thm_tac times_g_finite_thm
	THEN1 REPEAT strip_tac);
a(i_contr_tac THEN asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏supp_times_g_finite_thm⦎ = (* save_thm *) snd("supp_times_g_finite_thm", (
set_goal([], ⌜∀u v⦁
	Supp u ∈ Finite ∧ Supp u ⊆ Finite
∧	Supp v ∈ Finite ∧ Supp v ⊆ Finite
⇒	Supp (u _*⋎G v) ∈ Finite 
⌝);
a(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm);
a(∃_tac⌜{K | ∃I J⦁ I ∈ Supp u ∧ J ∈ Supp v ∧ K = I ⊖ J}⌝
	THEN1 ALL_FC_T rewrite_tac[supp_times_g_thm]);
a(lemma_tac⌜{K | ∃I J⦁ I ∈ Supp u ∧ J ∈ Supp v ∧ K = I ⊖ J} ∈ Finite
	∧ #{K | ∃I J⦁ I ∈ Supp u ∧ J ∈ Supp v ∧ K = I ⊖ J} ≤ #(Supp u × Supp v)⌝);
a(bc_thm_tac surjection_finite_size_thm
	THEN ALL_FC_T rewrite_tac[×_finite_size_thm]);
a(∃_tac⌜λ(I, J)⦁ I ⊖ J⌝ THEN rewrite_tac[]);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜(I, J)⌝ THEN asm_rewrite_tac[×_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏times_g_finitary_thm⦎ = (* save_thm *) snd("times_g_finitary_thm", (
set_goal([], ⌜∀u v⦁
	Supp u ∈ Finite ∧ Supp u ⊆ Finite
∧	Supp v ∈ Finite ∧ Supp v ⊆ Finite
⇒	Supp (u _*⋎G v) ∈ Finite ∧ Supp (u _*⋎G v) ⊆ Finite
⌝);
a(REPEAT strip_tac THEN1 ALL_FC_T rewrite_tac[supp_times_g_finite_thm]);
a(bc_thm_tac(pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝)
	THEN ∃_tac⌜{K | ∃I J⦁ I ∈ Supp u ∧ J ∈ Supp v ∧ K = I ⊖ J}⌝
	THEN ALL_FC_T rewrite_tac[supp_times_g_thm]);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
a(all_fc_tac[⊖_finite_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏supp_minus_g_thm⦎ = (* save_thm *) snd("supp_minus_g_thm", (
set_goal([], ⌜∀u⦁
	Supp (_~⋎G u) = Supp u
⌝);
a(REPEAT strip_tac THEN rewrite_tac[supp_def, minus_g_def]);
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN PC_T1"ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏χ_times_g_χ_thm⦎ = (* save_thm *) snd("χ_times_g_χ_thm", (
set_goal([], ⌜∀I J⦁
	χ{I} _*⋎G χ{J} = (λK⦁ Sign⋎G I J * χ{I ⊖ J} K)
⌝);
a(REPEAT strip_tac THEN rewrite_tac[times_g_def, supp_χ_thm]);
a(cases_tac⌜x = I ⊖ J⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜ {(I', J')|I' = I ∧ J' = J ∧ I ⊖ J = I' ⊖ J'} = {(I, J)}⌝
	rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" once_rewrite_tac[]
		THEN prove_tac[]));
a(rewrite_tac[ind_sum_singleton_thm, χ_def]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜ {(I', J')|I' = I ∧ J' = J ∧ x = I' ⊖ J'} = {}⌝
	rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" once_rewrite_tac[]
		THEN REPEAT strip_tac
		THEN all_var_elim_asm_tac1));
a(asm_rewrite_tac[χ_def, ind_sum_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏χ_finite_induction_thm⦎ = (* save_thm *) snd("χ_finite_induction_thm", (
set_goal([], ⌜∀V⦁
	(∀a u⦁ u ∈ V ⇒ a _*⋎S u ∈ V)
∧	(∀u v⦁ u ∈ V ∧ v ∈ V ⇒ u _+⋎G v ∈ V)
∧	(∀I a⦁ I ∈ Finite ⇒ χ{I} ∈ V)
⇒	(∀u⦁ Supp u ∈ Finite ∧ Supp u ⊆ Finite ⇒ u ∈ V)
⌝);
a(rewrite_tac[plus_g_def, times_s_def] THEN REPEAT strip_tac);
a(LEMMA_T ⌜∀A v⦁A ⊆ Supp u ∧ Supp v = A ⇒ v ∈ V⌝
	(fn th => bc_thm_tac th
		THEN ∃_tac⌜Supp u⌝ THEN rewrite_tac[]));
a(REPEAT strip_tac);
a(lemma_tac⌜A ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm
		THEN ∃_tac ⌜Supp u⌝ THEN asm_rewrite_tac[]));
a(LIST_DROP_NTH_ASM_T [2, 3] (MAP_EVERY ante_tac));
a(intro_∀_tac(⌜v⌝, ⌜v⌝));
a(finite_induction_tac⌜A⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(PC_T1"sets_ext1" rewrite_tac[supp_def]);
a(REPEAT strip_tac
	THEN PC_T1 "predicates" lemma_tac⌜v = λK⦁ℕℝ 0⌝
	THEN1 asm_rewrite_tac[]
	THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜{}:ℕ SET⌝));
a(rewrite_tac[empty_finite_thm] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 6 (ante_tac o list_∀_elim[⌜ℕℝ 0⌝, ⌜χ{{}:ℕ SET}⌝]));
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(PC_T1 "predicates" lemma_tac
	⌜∃w a⦁ v = (λ K⦁ w K + (λ K⦁ a * χ {x} K) K)
	∧ Supp w = A⌝);
(* *** Goal "2.1" *** *)
a(∃_tac⌜λK⦁if K = x then ℕℝ 0 else v K⌝ THEN ∃_tac⌜v x⌝);
a(rewrite_tac[χ_def] THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(cases_tac⌜x' = x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[supp_def]);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1.2.1" *** *)
a(swap_nth_asm_concl_tac 1);
a(cases_tac⌜x' = x⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 3 (ante_tac o ∀_elim⌜x'⌝));
a(asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" once_rewrite_tac[]);
a(asm_rewrite_tac[]);
(* *** Goal "2.1.2.2" *** *)
a(cases_tac⌜x' = x⌝ THEN1 all_var_elim_asm_tac1);
a(asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 3 (ante_tac o ∀_elim⌜x'⌝));
a(asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" once_rewrite_tac[]);
a(asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(PC_T "predicates" all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 9 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜w⌝));
a(asm_rewrite_tac[] THEN STRIP_T bc_thm_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b c⦁a ∪ b ⊆ c ⇒ b ⊆ c⌝]);
(* *** Goal "2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [8, 9] bc_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀x b c⦁{x} ∪ b ⊆ c ⇒ x ∈ c⌝]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀x b c⦁x ∈ b ∧ b ⊆ c ⇒ x ∈ c⌝]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏χ_finite_independent_thm⦎ = (* save_thm *) snd("χ_finite_independent_thm", (
set_goal([], ⌜∀J⦁
	J ∈ Finite
⇒	∃V⦁
	(∀a u⦁ u ∈ V ⇒ a _*⋎S u ∈ V)
∧	(∀u v⦁ u ∈ V ∧ v ∈ V ⇒ u _+⋎G v ∈ V)
∧	(∀I a⦁ ¬I = J ∧ I ∈ Finite ⇒ χ{I} ∈ V)
∧	¬χ{J} ∈ V
⌝);
a(REPEAT strip_tac);
a(∃_tac⌜{u | Supp u ∈ Finite ∧ Supp u ⊆ Finite ∧ u J = ℕℝ 0}⌝);
a(rewrite_tac[χ_def, prove_rule[]⌜∀I⦁I = J ⇔ J = I⌝]);
a(REPEAT strip_tac
	THEN_TRY ALL_FC_T rewrite_tac[times_s_finitary_thm,
		plus_g_finitary_thm,
		χ_finite_finitary_thm]
	THEN_TRY asm_rewrite_tac[times_s_def, plus_g_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();

*)
push_consistency_goal ⌜$+⋎G⌝;
a (strip_asm_tac (pure_rewrite_rule[is_ga_rep_def] (simple_⇒_match_mp_rule type_lemmas_thm ga_def)));
a(∃_tac⌜(
	(λu v⦁ abs(rep u _+⋎G rep v)),
	(λu⦁ abs(_~⋎G(rep u))),
	abs _0⋎G,
	(λa u⦁ abs(a _*⋎S rep u)),
	(λu v⦁ abs(rep u _*⋎G rep v)),
	abs _1⋎G,
	(λI⦁abs(χ{I})))⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT ∧_tac THEN REPEAT ∀_tac);
(* *** Goal "1" *** *)
a(conv_tac(LEFT_C (rewrite_conv[∀_elim⌜rep u⌝ plus_g_comm_thm])));
a(asm_rewrite_tac[one_times_s_thm]);
a(LEMMA_T⌜∀x y⦁
	rep(abs(rep x _+⋎G rep y)) = rep x _+⋎G rep y
∧	rep(abs(rep x _*⋎G rep y)) = rep x _*⋎G rep y⌝
	rewrite_thm_tac);
(* *** Goal "1.1" *** *)
a(REPEAT ∀_tac);
a(TOP_ASM_T(rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(∧_tac THEN_LIST
	[bc_thm_tac plus_g_finitary_thm,
	bc_thm_tac times_g_finitary_thm]
	THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(LEMMA_T ⌜
	rep(abs _0⋎G) = _0⋎G
∧	rep(abs _1⋎G) = _1⋎G⌝ rewrite_thm_tac);
(* *** Goal "1.2.1" *** *)
a(TOP_ASM_T(rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(rewrite_tac[zero_one_finitary_thm]);
(* *** Goal "1.2.2" *** *)
a(rewrite_tac[plus_g_0_thm, plus_g_assoc_thm,
	one_g_times_g_thm]);
a(LEMMA_T⌜∀x⦁
	rep(abs(_~⋎G(rep x))) = _~⋎G (rep x)⌝
	rewrite_thm_tac);
(* *** Goal "1.2.2.1" *** *)
a(REPEAT ∀_tac);
a(TOP_ASM_T(rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(rewrite_tac[supp_minus_g_thm] THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.2" *** *)
a(asm_rewrite_tac[plus_g_minus_g_thm]);
a(LEMMA_T⌜∀s x⦁
	rep(abs(s _*⋎S rep x)) = s _*⋎S rep x⌝
	rewrite_thm_tac);
(* *** Goal "1.2.2.2.1" *** *)
a(REPEAT ∀_tac);
a(TOP_ASM_T(rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(bc_thm_tac times_s_finitary_thm
	THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.2.2" *** *)
a(rewrite_tac[times_s_times_s_thm,
	times_s_plus_g_distrib_thm,
	plus_times_s_distrib_thm, one_g_def]);
a(lemma_tac⌜
	(Supp (rep u) ∈ Finite ∧ Supp (rep u) ⊆ Finite)
∧	(Supp (rep v) ∈ Finite ∧ Supp (rep v) ⊆ Finite)
∧	(Supp (rep w) ∈ Finite ∧ Supp (rep w) ⊆ Finite)⌝
	THEN1 asm_rewrite_tac[]);
a(PC_T1 "predicates" (ALL_FC_T rewrite_tac)[
	times_g_assoc_thm,
	times_g_plus_g_distrib_thm,
	times_s_times_g_assoc_thm,
	times_g_times_s_assoc_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜I ⊖ J ∈ Finite⌝ THEN1 all_fc_tac[⊖_finite_thm]);
a(LEMMA_T⌜Supp(χ{I}) ∈ Finite ∧ Supp(χ{I}) ⊆ Finite⌝
	ante_tac
	THEN1 (bc_thm_tac χ_finite_finitary_thm
		THEN REPEAT strip_tac));
a(LEMMA_T⌜Supp(χ{J}) ∈ Finite ∧ Supp(χ{J}) ⊆ Finite⌝
	ante_tac
	THEN1 (bc_thm_tac χ_finite_finitary_thm
		THEN REPEAT strip_tac));
a(LEMMA_T⌜Supp(χ{I ⊖ J}) ∈ Finite ∧ Supp(χ{I ⊖ J}) ⊆ Finite⌝
	ante_tac
	THEN1 (bc_thm_tac χ_finite_finitary_thm
		THEN REPEAT strip_tac));
a(PC_T1 "predicates" asm_rewrite_tac[]);
a(PC_T1 "predicates" REPEAT strip_tac);
a(PC_T1 "predicates" asm_rewrite_tac[times_s_def, χ_times_g_χ_thm]);
(* *** Goal "3" *** *)
a(REPEAT strip_tac);
a(LEMMA_T⌜u = abs(rep u)⌝ once_rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜Supp(rep u) ∈ Finite ∧ Supp(rep u) ⊆ Finite ∧ abs(rep u) ∈ V⌝);
a(LEMMA_T⌜∀x⦁Supp x ∈ Finite ∧ Supp x ⊆ Finite ⇒
	Supp x ∈ Finite ∧ Supp x ⊆ Finite ∧ abs x ∈ V⌝
	bc_thm_tac THEN_LIST [id_tac, asm_rewrite_tac[]]);
a(bc_thm_tac(rewrite_rule[]
	(∀_elim⌜{x | Supp x ∈ Finite ∧ Supp x ⊆ Finite ∧ abs x ∈ V}⌝ χ_finite_induction_thm)));
a(REPEAT strip_tac
	THEN_TRY ALL_FC_T asm_rewrite_tac[
		χ_finite_finitary_thm,
		times_s_finitary_thm,
		plus_g_finitary_thm]);
(* *** Goal "3.1" *** *)
a(DROP_NTH_ASM_T 8 discard_tac);
a(DROP_NTH_ASM_T 5 (ante_tac o list_∀_elim[⌜a⌝, ⌜abs u⌝]));
a(DROP_NTH_ASM_T 6 (ante_tac o ∀_elim⌜u⌝));
a(PC_T1 "predicates"asm_rewrite_tac[]);
a(STRIP_T (PC_T1 "predicates" rewrite_thm_tac));
(* *** Goal "3.2" *** *)
a(DROP_NTH_ASM_T 11 discard_tac);
a(DROP_NTH_ASM_T 7 (ante_tac o list_∀_elim[⌜abs u⌝, ⌜abs v⌝]));
a(GET_NTH_ASM_T 9 (ante_tac o ∀_elim⌜u⌝));
a(DROP_NTH_ASM_T 9 (ante_tac o ∀_elim⌜v⌝));
a(PC_T1 "predicates"asm_rewrite_tac[]);
a(STRIP_T (PC_T1 "predicates" rewrite_thm_tac));
a(STRIP_T (PC_T1 "predicates" rewrite_thm_tac));
(* *** Goal "3.3" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
(* *** Goal "4" *** *)
a(REPEAT strip_tac THEN all_fc_tac[χ_finite_independent_thm]);
a(∃_tac⌜{u | rep u ∈ V}⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "4.1" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(LEMMA_T⌜Supp(χ{I}) ∈ Finite ∧ Supp(χ{I}) ⊆ Finite⌝
	ante_tac
	THEN1 (bc_thm_tac χ_finite_finitary_thm
		THEN REPEAT strip_tac));
a(PC_T1 "predicates" asm_rewrite_tac[] THEN STRIP_T asm_rewrite_thm_tac);
(* *** Goal "4.2" *** *)
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(LEMMA_T⌜rep(abs(a _*⋎S rep u)) = a _*⋎S rep u⌝
	asm_rewrite_thm_tac);
a(GET_NTH_ASM_T 7 (rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(bc_thm_tac times_s_finitary_thm THEN asm_rewrite_tac[]);
(* *** Goal "4.3" *** *)
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(LEMMA_T⌜rep(abs(rep u _+⋎G rep v)) = rep u _+⋎G rep v⌝
	asm_rewrite_thm_tac);
a(GET_NTH_ASM_T 11 (rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(bc_thm_tac plus_g_finitary_thm THEN asm_rewrite_tac[]);
(* *** Goal "4.4" *** *)
a(LEMMA_T⌜rep(abs(χ{J})) = χ{J}⌝ asm_rewrite_thm_tac);
a(GET_NTH_ASM_T 6 (rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(bc_thm_tac χ_finite_finitary_thm THEN asm_rewrite_tac[]);
val _ = save_consistency_thm ⌜$+⋎G⌝ (pop_thm());
val ⦏ga_ops_def⦎ = save_thm("ga_ops_def", get_spec ⌜$+⋎G⌝);
=TEX
%%%%
%%%%

=SML

val ⦏ga_e_def⦎ = get_spec⌜E⋎G⌝;
val ⦏ga_subtract_def⦎ = get_spec⌜$-⋎G⌝;
val ⦏ga_ℕ_exp_def⦎ = get_spec⌜$^⋎G⌝;
val ⦏Γ_def⦎ = get_spec⌜ℕ⋎G⌝;
val ⦏ga_vector_def⦎ = get_spec⌜Vector⋎G⌝;
val ⦏⊥_def⦎ = get_spec⌜$⊥⌝;
=TEX
%%%%
%%%%

=SML

val [	⦏ga_plus_comm_thm⦎,
	⦏ga_plus_assoc_thm⦎,
	⦏ga_plus_zero_thm⦎,
	⦏ga_plus_minus_thm1⦎ ] =
	map all_∀_intro(
		strip_∧_rule(
			all_∀_elim(∧_left_elim ga_ops_def))to 3);
val _ = save_thm("ga_plus_assoc_thm", ga_plus_assoc_thm);
val ⦏ga_plus_assoc_thm1⦎ = save_thm("ga_plus_assoc_thm1", conv_rule (ONCE_MAP_C eq_sym_conv) ga_plus_assoc_thm);
val _ = save_thm("ga_plus_comm_thm", ga_plus_comm_thm);
val _ = save_thm("ga_plus_zero_thm", ga_plus_zero_thm);
=TEX
%%%%
%%%%

=SML

val ⦏ga_plus_order_thm⦎ = (
set_goal([], ⌜∀x y z:GA⦁
	y + x = x + y
∧	(x + y) + z = x + y + z
∧	y + x + z = x + y + z	⌝);
a(REPEAT ∀_tac THEN rewrite_tac[ga_plus_assoc_thm]);
a(rewrite_tac[∀_elim⌜y⌝ ga_plus_comm_thm, ga_plus_assoc_thm]);
save_pop_thm"ga_plus_order_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_plus_0_thm⦎ = (
set_goal([], ⌜∀x:GA⦁ x + Γ 0 = x ∧ Γ 0 + x = x⌝);
a(rewrite_tac[Γ_def, ga_plus_zero_thm, ∀_elim⌜0⋎G⌝ ga_plus_comm_thm]);
save_pop_thm"ga_plus_0_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_0_1_thm⦎ = (
set_goal([], ⌜0⋎G = Γ 0 ∧ 1⋎G = Γ 1⌝);
a(pure_once_rewrite_tac[prove_rule [] ⌜1 = 0 + 1⌝]);
a(pure_rewrite_tac[Γ_def]);
a(rewrite_tac[∀_elim⌜0⋎G⌝ ga_plus_comm_thm, ga_plus_zero_thm]);
save_pop_thm"ga_0_1_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_plus_minus_thm⦎ = (
set_goal([], ⌜∀ x : GA ⦁ x + ~ x = Γ 0 ∧ ~x + x = Γ 0⌝);
a(∀_tac);
a(rewrite_tac[∀_elim⌜x⌝ ga_plus_order_thm]);
a(rewrite_tac[Γ_def, ga_plus_minus_thm1]);
save_pop_thm"ga_plus_minus_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_eq_thm⦎ = (
set_goal([], ⌜∀ x y : GA ⦁ x = y ⇔ x + ~y = Γ 0⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[ga_plus_minus_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜(x + ~ y) + y = Γ 0 + y⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(rewrite_tac[ga_plus_assoc_thm, ga_plus_minus_thm, ga_plus_0_thm]);
save_pop_thm"ga_eq_thm"
);
=TEX
%%%%
%%%%
=SML

val ⦏Γ_plus_homomorphism_thm⦎ = (
set_goal([], ⌜∀ m n : ℕ ⦁ Γ(m + n) = Γ m + Γ n⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[Γ_def, ga_0_1_thm, ga_plus_0_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[plus_assoc_thm1, Γ_def, ga_plus_assoc_thm]);
save_pop_thm"Γ_plus_homomorphism_thm"
);
=TEX
%%%%
%%%%

=SML

val [	⦏ga_one_scale_thm⦎,
	⦏ga_scale_scale_assoc_thm⦎,
	⦏ga_scale_plus_distrib_thm⦎,
	⦏ga_plus_scale_distrib_thm⦎,
	⦏ga_times_assoc_thm⦎,
	⦏ga_times_plus_distrib_thm⦎,
	⦏ga_plus_times_distrib_thm⦎,
	⦏ga_scale_times_assoc_thm⦎,
	⦏ga_times_scale_assoc_thm⦎,
	⦏ga_one_times_thm⦎,
	⦏ga_times_one_thm⦎,
	⦏ga_one_mon_thm⦎ ] =
		map (conv_rule (TRY_C (rewrite_conv[ga_0_1_thm])) o all_∀_intro)(
		strip_∧_rule(
			all_∀_elim(∧_left_elim ga_ops_def)) from 4);
val _ = save_thm("ga_one_scale_thm", ga_one_scale_thm);
val _ = save_thm("ga_scale_scale_assoc_thm", ga_scale_scale_assoc_thm);
val _ = save_thm("ga_scale_plus_distrib_thm", ga_scale_plus_distrib_thm);
val _ = save_thm("ga_plus_scale_distrib_thm", ga_plus_scale_distrib_thm);
val _ = save_thm("ga_times_assoc_thm", ga_times_assoc_thm);
val _ = save_thm("ga_times_plus_distrib_thm", ga_times_plus_distrib_thm);
val _ = save_thm("ga_plus_times_distrib_thm", ga_plus_times_distrib_thm);
val _ = save_thm("ga_scale_times_assoc_thm", ga_scale_times_assoc_thm);
val _ = save_thm("ga_times_scale_assoc_thm", ga_times_scale_assoc_thm);
val _ = save_thm("ga_one_times_thm", ga_one_times_thm);
val _ = save_thm("ga_times_one_thm", ga_times_one_thm);
val _ = save_thm("ga_one_mon_thm", ga_one_mon_thm);
=TEX
%%%%
%%%%

=SML
=TEX
%%%%
%%%%

=SML

val ⦏ga_minus_clauses⦎ = (
set_goal([], ⌜∀x y : GA⦁
		~ (~ x) = x
	∧	x + ~ x = Γ 0
	∧	~ x + x = Γ 0
	∧	~ (x + y) = ~ x + ~ y
	∧ 	~(Γ 0) = (Γ 0)⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[ga_plus_minus_thm]);
a(lemma_tac⌜∀x:GA⦁~(~ x) = x⌝);
(* *** Goal "1" *** *)
a(strip_tac THEN once_rewrite_tac[ga_eq_thm]);
a(once_rewrite_tac[ga_plus_comm_thm]);
a(rewrite_tac[ga_plus_minus_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[] THEN strip_tac);
(* *** Goal "2.1" *** *)
a(conv_tac eq_sym_conv THEN once_rewrite_tac[ga_eq_thm]);
a(asm_rewrite_tac[∀_elim⌜~ y⌝ga_plus_order_thm]);
a(rewrite_tac[∀_elim⌜y⌝ga_plus_order_thm, ga_plus_minus_thm, ga_plus_0_thm]);
(* *** Goal "2.2" *** *)
a(conv_tac eq_sym_conv THEN once_rewrite_tac[ga_eq_thm]);
a(asm_rewrite_tac[ga_plus_0_thm]);
save_pop_thm"ga_minus_clauses"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_minus_eq_thm⦎ = (
set_goal([], ⌜∀x y : GA⦁~x = ~y ⇔ x = y⌝);
a(REPEAT ∀_tac);
a(conv_tac(LEFT_C eq_sym_conv));
a(once_rewrite_tac[ga_eq_thm]);
a(rewrite_tac[ga_minus_clauses, ∀_elim⌜x⌝ga_plus_order_thm]);
save_pop_thm"ga_minus_eq_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_0_times_thm⦎ = (
set_goal([], ⌜∀u⦁ Γ 0 * u = Γ 0⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜(u + Γ 0)*u = u*u⌝ ante_tac
	THEN1 rewrite_tac[ga_plus_0_thm, ga_minus_clauses]);
a(rewrite_tac[ga_plus_times_distrib_thm]);
a(conv_tac (LEFT_C (once_rewrite_conv[ga_eq_thm])));
a(rewrite_tac[∀_elim⌜Γ 0 * u⌝ ga_plus_order_thm,
	ga_minus_clauses, ga_plus_0_thm]);
save_pop_thm"ga_0_times_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_0_scale_thm⦎ = (
set_goal([], ⌜∀u⦁ ℕℝ 0 *⋎S u = Γ 0⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜(ℕℝ 1 + ℕℝ 0) *⋎S u = u⌝ ante_tac
	THEN1 rewrite_tac[ga_one_scale_thm]);
a(pure_rewrite_tac[ga_plus_scale_distrib_thm, ga_one_scale_thm]);
a(conv_tac (LEFT_C (once_rewrite_conv[ga_eq_thm])));
a(rewrite_tac[∀_elim⌜ℕℝ 0 *⋎S u⌝ ga_plus_order_thm,
	ga_minus_clauses, ga_plus_0_thm]);
save_pop_thm"ga_0_scale_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_scale_0_thm⦎ = (
set_goal([], ⌜∀a⦁ a *⋎S Γ 0 = Γ 0⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜a *⋎S (Γ 0 + Γ 0) = a *⋎S Γ 0⌝ ante_tac
	THEN1 rewrite_tac[ga_plus_0_thm]);
a(pure_rewrite_tac[ga_scale_plus_distrib_thm]);
a(conv_tac (LEFT_C (once_rewrite_conv[ga_eq_thm])));
a(rewrite_tac[ga_plus_assoc_thm,
	ga_minus_clauses, ga_plus_0_thm]);
save_pop_thm"ga_scale_0_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_minus_1_scale_thm⦎ = (
set_goal([], ⌜∀u⦁ ~(ℕℝ 1) *⋎S u = ~u⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜(ℕℝ 1 + ~(ℕℝ 1)) *⋎S u + ~u = Γ 0 + ~u⌝ ante_tac
	THEN1 rewrite_tac[ga_0_scale_thm]);
a(pure_rewrite_tac[ga_plus_scale_distrib_thm, ga_one_scale_thm]);
a(rewrite_tac[∀_elim⌜~ (ℕℝ 1) *⋎S u⌝ ga_plus_order_thm,
	ga_minus_clauses, ga_plus_0_thm]);
save_pop_thm"ga_minus_1_scale_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_ℕ_exp_clauses⦎ = (
set_goal([], ⌜∀u:GA⦁ u ^ 0 = Γ 1 ∧ u ^ 1 = u ∧ u ^ 2 = u*u⌝);
a(rewrite_tac[ga_ℕ_exp_def, ga_0_1_thm]);
a(pure_rewrite_tac[prove_rule[]⌜2 = 1 + 1⌝, ga_ℕ_exp_def]);
a(once_rewrite_tac[prove_rule[]⌜1 = 0 + 1⌝]);
a(pure_rewrite_tac[ga_ℕ_exp_def, ga_0_1_thm, ga_times_one_thm]);
a(REPEAT strip_tac);
save_pop_thm"ga_ℕ_exp_clauses"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_minus_scale_thm⦎ = save_thm( "ga_minus_scale_thm", (
set_goal([], ⌜
∀u : GA⦁ ~u = ~(ℕℝ 1) *⋎S u
⌝);
a(REPEAT strip_tac THEN conv_tac eq_sym_conv); a(once_rewrite_tac[ga_eq_thm]);
a(LEMMA_T ⌜~(~ u) = ℕℝ 1 *⋎S u⌝ rewrite_thm_tac
	THEN1 rewrite_tac[ga_minus_clauses, ga_ops_def]);
a(rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv)
	ga_plus_scale_distrib_thm,
	ga_0_scale_thm]);
pop_thm()
));

val ⦏ga_scale_minus_thm⦎ = save_thm ("ga_scale_minus_thm",
	conv_rule(ONCE_MAP_C eq_sym_conv) ga_minus_scale_thm);
=TEX
%%%%
%%%%

=SML

val [	⦏ga_mon_times_mon_thm⦎,
	⦏ga_mon_span_thm⦎,
	⦏ga_mon_indep_thm⦎ ] =
		strip_∧_rule(
			∧_right_elim ga_ops_def);

val _ = save_thm("ga_mon_span_thm", ga_mon_span_thm);
val _ = save_thm("ga_mon_indep_thm", ga_mon_indep_thm);
val _ = save_thm("ga_mon_times_mon_thm ", ga_mon_times_mon_thm );
=TEX
%%%%
%%%%

=SML

val ⦏finite_friend_thm⦎ = (
set_goal([], ⌜∀b⦁ b ∈ Finite ⇒ ∃a⦁a ∈ Finite ∧ ¬a = b⌝);
a(REPEAT strip_tac);
a(cases_tac⌜{} = b⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(∃_tac⌜{x}⌝ THEN1 PC_T1 "sets_ext1" rewrite_tac[singleton_finite_thm]
	THEN prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜{}⌝ THEN asm_rewrite_tac[empty_finite_thm]);
save_pop_thm"finite_friend_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_mon_not_0_thm⦎ = (
set_goal([], ⌜∀I⦁ I ∈ Finite ⇒ ¬Mon⋎G I = Γ 0⌝);
a(REPEAT strip_tac);
a(all_fc_tac[ga_mon_indep_thm]);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
a(all_fc_tac[finite_friend_thm]);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(LEMMA_T ⌜ℕℝ 0 *⋎S Mon⋎G a ∈ V⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(rewrite_tac[ga_0_scale_thm]);
save_pop_thm"ga_mon_not_0_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_mon_1_thm⦎ = (
set_goal([], ⌜Mon⋎G {} = Γ 1⌝);
a(accept_tac(eq_sym_rule ga_one_mon_thm));
save_pop_thm"ga_mon_1_thm"
);
=TEX
%%%%
%%%%

=SML

val ⦏ga_vec_times_vec_thm⦎ = (* save_thm *) snd("ga_vec_times_vec_thm", (
set_goal([], ⌜∀i j⦁
	E⋎G i *⋎G E⋎G j =
	if	i < j
	then	Mon⋎G{i; j}
	else if	j < i
	then	~(ℕℝ 1) *⋎S Mon⋎G{i; j}
	else	 Γ 1
⌝);
a(REPEAT strip_tac THEN rewrite_tac[ga_e_def]);
a(lemma_tac⌜{i} ∈ Finite ∧ {j} ∈ Finite⌝
	THEN1 rewrite_tac[singleton_finite_thm]);
a(ALL_FC_T rewrite_tac[ga_mon_times_mon_thm]);
a(cases_tac⌜i = j⌝
	THEN1 (all_var_elim_asm_tac1
		THEN rewrite_tac[]));
(* *** Goal "1" *** *)
a(rewrite_tac[sign_singleton_thm, ⊖_lemmas,
	ga_mon_1_thm]);
a(PC_T1 "predicates" cases_tac⌜j < 0⌝ THEN asm_rewrite_tac[ga_one_scale_thm, ga_minus_1_scale_thm]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[sign_singletons_thm]);
a(LEMMA_T⌜{i} ⊖ {j} = {i; j}⌝ rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" rewrite_tac[⊖_def1]
		THEN REPEAT strip_tac
		THEN contr_tac
		THEN all_var_elim_asm_tac1));
a(PC_T1 "predicates" cases_tac⌜i < j⌝ THEN asm_rewrite_tac[ga_one_scale_thm]);
a(PC_T1 "predicates" lemma_tac ⌜j < i⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_mon_subgroup_thm⦎ = save_thm( "ga_mon_subgroup_thm", (
set_goal([], ⌜∀X⦁
	(∀i⦁E⋎G i ∈ X)
∧	(∀u⦁ u ∈ X ⇒ ~(ℕℝ 1) *⋎S u ∈ X)
∧	(∀u v⦁ u ∈ X ∧ v ∈ X ⇒ u * v ∈ X)
⇒	(∀I⦁ I ∈ Finite ⇒ Mon⋎G I ∈ X)
⌝);
a(REPEAT strip_tac);
a(finite_induction_tac ⌜I⌝);
(* *** Goal "1" *** *)
a(LEMMA_T⌜E⋎G 0 * E⋎G 0 ∈ X⌝ ante_tac
	THEN1 (POP_ASM_T bc_thm_tac THEN asm_rewrite_tac[]));
a(rewrite_tac[ga_mon_1_thm, ga_vec_times_vec_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜E⋎G x * Mon⋎G I ∈ X⌝ ante_tac
	THEN1 (DROP_NTH_ASM_T 4 bc_thm_tac THEN asm_rewrite_tac[]));
a(lemma_tac⌜{x} ∩ I = {}⌝ THEN1 
	(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" rewrite_tac[]
		THEN contr_tac THEN all_var_elim_asm_tac));
a(ALL_FC_T rewrite_tac[pc_rule1"sets_ext1" prove_rule[⊖_def1] 
	⌜∀A⦁A ∩ I = {} ⇒ A ∪ I = A ⊖ I⌝]);
a(rewrite_tac[ga_e_def]);
a(lemma_tac⌜{x} ∈ Finite⌝ THEN1 rewrite_tac[singleton_finite_thm]);
a(ALL_FC_T rewrite_tac[ga_mon_times_mon_thm]);
a(strip_asm_tac(list_∀_elim[⌜{x}⌝, ⌜I⌝] sign_g_cases_thm)
	THEN asm_rewrite_tac[ga_one_scale_thm]
	THEN REPEAT strip_tac);
a(LEMMA_T⌜~(ℕℝ 1) *⋎S (~ (ℕℝ 1) *⋎S Mon⋎G ({x} ⊖ I)) ∈ X⌝ ante_tac
	THEN1 (DROP_NTH_ASM_T 9 bc_thm_tac THEN asm_rewrite_tac[]));
a(rewrite_tac[ga_scale_scale_assoc_thm, ga_one_scale_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_vec_generators_thm⦎ = save_thm( "ga_vec_generators_thm", (
set_goal([], ⌜∀A⦁
	(∀i⦁ E⋎G i ∈ A)
∧	(∀u a⦁ u ∈ A ⇒ a *⋎S u ∈ A)
∧	(∀u v⦁ u ∈ A ∧ v ∈ A ⇒ u +⋎G v ∈ A)
∧	(∀u v⦁ u ∈ A ∧ v ∈ A ⇒ u *⋎G v ∈ A)
⇒	(∀u⦁ u ∈ A)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(bc_thm_tac ga_mon_span_thm THEN asm_rewrite_tac[]);
a(bc_thm_tac ga_mon_subgroup_thm THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_vec_relations_thm⦎ = save_thm( "ga_vec_relations_thm", (
set_goal([], ⌜∀i j⦁
	E⋎G i * E⋎G i = Γ 1
∧	(¬i = j ⇒ E⋎G i *⋎G E⋎G j = ~(E⋎G j * E⋎G i))
⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[ga_vec_times_vec_thm] THEN REPEAT strip_tac);
a(LEMMA_T⌜{j ; i} = {i; j}⌝ rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" rewrite_tac[]
		THEN REPEAT strip_tac
		THEN all_var_elim_asm_tac1));
a(PC_T1 "predicates" lemma_tac ⌜i < j ∧ ¬j < i ∨ ¬i < j ∧ j < i⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN asm_rewrite_tac[ga_minus_1_scale_thm, ga_minus_clauses]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀j⦁∃ V⦁
	(∀i⦁ ¬i = j ⇒ E⋎G i ∈ V)
∧	(∀a u⦁ u ∈ V ⇒ a *⋎S u ∈ V)
∧	(∀u v⦁ u ∈ V ∧ v ∈ V ⇒ u +⋎G v ∈ V)
∧	¬E⋎G j ∈ V
⌝);
a(REPEAT strip_tac THEN rewrite_tac[ga_e_def]);
a(lemma_tac⌜{j} ∈ Finite⌝ THEN1 rewrite_tac[singleton_finite_thm]);
a(all_fc_tac[ga_mon_indep_thm]);
a(∃_tac⌜V⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN rewrite_tac[singleton_finite_thm]);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜i⌝ THEN asm_rewrite_tac[]);
=TEX
%%%%
%%%%

=SML

val ⦏ga_vec_indep_thm⦎ = save_pop_thm "ga_vec_indep_thm";
val ⦏ga_subspace_def⦎ = rewrite_rule[ga_0_1_thm]
	(get_spec⌜Subspace⋎G⌝);
val ⦏ga_span_def⦎ = get_spec⌜Span⋎G⌝;
val ⦏ga_indep_def⦎ = get_spec⌜Indep⋎G⌝;
=TEX
%%%%
%%%%

=SML

val ⦏ga_span_subspace_thm⦎ = save_thm( "ga_span_subspace_thm", (
set_goal([], ⌜∀X⦁ Span⋎G X ∈ Subspace⋎G⌝);
a(rewrite_tac[ga_span_def, ga_subspace_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_GET_NTH_ASM_T[3, 5] bc_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(LIST_GET_NTH_ASM_T[2, 5] bc_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_⊆_span_thm⦎ = save_thm( "ga_⊆_span_thm", (
set_goal([], ⌜∀X⦁ X ⊆ Span⋎G X⌝);
a(PC_T1 "sets_ext1" rewrite_tac[ga_span_def] THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_span_⊆_thm⦎ = save_thm( "ga_span_⊆_thm", (
set_goal([], ⌜∀V⦁ V ∈ Subspace⋎G ∧ X ⊆ V ⇒ Span⋎G X ⊆ V⌝);
a(rewrite_tac[ga_span_def, ga_subspace_def] THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_trivial_subspaces_thm⦎ = save_thm( "ga_trivial_subspaces_thm", (
set_goal([], ⌜
	Universe ∈ Subspace⋎G
∧	{Γ 0} ∈ Subspace⋎G⌝);
a(rewrite_tac[ga_subspace_def] THEN REPEAT strip_tac
	THEN asm_rewrite_tac[ga_plus_0_thm, ga_scale_0_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_mon_span_bc_thm⦎ = save_thm( "ga_mon_span_bc_thm", (
set_goal([], ⌜∀V u⦁
	(∀ I⦁ I ∈ Finite ⇒ Mon⋎G I ∈ V)
∧	(∀ a u⦁ u ∈ V ⇒ a *⋎S u ∈ V)
∧	(∀ u v⦁ u ∈ V ∧ v ∈ V ⇒ u + v ∈ V)
⇒	u ∈ V⌝);
a(REPEAT strip_tac);
a(ante_tac(∀_elim⌜V⌝ga_mon_span_thm) THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_span_mon_thm⦎ = save_thm( "ga_span_mon_thm", (
set_goal([], ⌜
	Span⋎G {u | ∃I⦁ I ∈ Finite ∧ u = Mon⋎G I} = Universe⌝);
a(PC_T1 "sets_ext1" rewrite_tac[ga_span_def, ga_subspace_def]
	THEN REPEAT strip_tac);
a(bc_thm_tac ga_mon_span_bc_thm THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 2 bc_thm_tac);
a(∃_tac⌜I⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_span_mono_thm⦎ = save_thm( "ga_span_mono_thm", (
set_goal([], ⌜∀X Y⦁ X ⊆ Y ⇒ Span⋎G X ⊆ Span⋎G Y⌝);
a(PC_T1 "sets_ext1" rewrite_tac[ga_span_def]
	THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac
	THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_indep_thm⦎ = save_thm( "ga_indep_thm", (
set_goal([], ⌜∀X⦁ X ∈ Indep⋎G ⇔ ∀x⦁x ∈ X ⇒ ¬x ∈ Span⋎G (X \ {x})⌝);
a(rewrite_tac[ga_indep_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(contr_tac THEN lemma_tac⌜X \ {x} ⊆ X⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(all_fc_tac[ga_span_mono_thm]);
a(strip_asm_tac(∀_elim⌜X \ {x}⌝ga_⊆_span_thm));
a(lemma_tac⌜X ⊆ Span⋎G (X \ {x})⌝
	THEN1 (PC_T1 "sets_ext1" REPEAT strip_tac));
(* *** Goal "1.1" *** *)
a(cases_tac⌜x' = x⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜x' ∈ X \ {x}⌝ asm_tac THEN1 REPEAT strip_tac);
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜Span⋎G X ⊆ Span⋎G(X \ {x})⌝
	THEN1 (bc_thm_tac ga_span_⊆_thm
		THEN asm_rewrite_tac[ga_span_subspace_thm]));
a(all_fc_tac[pc_rule1 "sets_ext1"prove_rule[]
	⌜∀a b⦁a ⊆ b ∧ b ⊆ a ⇒ a = b⌝]);
a(LIST_DROP_NTH_ASM_T [10] all_fc_tac);
a(lemma_tac⌜¬x ∈ X⌝);
a(POP_ASM_T (once_rewrite_thm_tac o eq_sym_rule)	
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(bc_thm_tac (pc_rule1 "sets_ext1"prove_rule[]
	⌜∀a b⦁a ⊆ b ∧ b ⊆ a ⇒ a = b⌝));
a(REPEAT strip_tac THEN PC_T "sets_ext1" contr_tac);
a(lemma_tac⌜Y ⊆ X \ {x}⌝
	THEN1 (PC_T "sets_ext1" contr_tac
		THEN_TRY all_var_elim_asm_tac1
		THEN PC_T1 "sets_ext1" all_asm_fc_tac[]));
a(all_fc_tac[ga_span_mono_thm]);
a(strip_asm_tac(∀_elim⌜Y⌝ga_⊆_span_thm));
a(LIST_DROP_NTH_ASM_T [9] all_fc_tac);
a(strip_asm_tac(∀_elim⌜X⌝ga_⊆_span_thm));
a(lemma_tac⌜x  ∈ Span⋎G (X \ {x})⌝);
a(bc_thm_tac(pc_rule1 "sets_ext" prove_rule[]
	⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝));
a(∃_tac⌜Span⋎G Y⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ga_mon_indep_thm1⦎ = save_thm( "ga_mon_indep_thm1", (
set_goal([], ⌜
	{u | ∃I⦁ I ∈ Finite ∧ u = Mon⋎G I} ∈ Indep⋎G⌝);
a(rewrite_tac[ga_span_def, ga_subspace_def,
	ga_indep_thm]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(all_fc_tac[ga_mon_indep_thm]);
a(∃_tac⌜V⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[finite_friend_thm]);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(LEMMA_T ⌜ℕℝ 0 *⋎S Mon⋎G a ∈ V⌝ ante_tac
	THEN1 ALL_ASM_FC_T rewrite_tac[]);
a(rewrite_tac[ga_0_scale_thm]);
(* *** Goal "2" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(cases_tac⌜I' = I⌝ THEN1 all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏pythagoras_thm⦎ = save_thm( "pythagoras_thm", (
set_goal([], ⌜
∀u v : GA⦁
	u ⊥ v ⇒ (u - v)^2 = u^2 + v^2
⌝);
a(rewrite_tac[ga_subtract_def]);
a(REPEAT ∀_tac THEN rewrite_tac[
	⊥_def, ga_ℕ_exp_clauses, 
	ga_times_plus_distrib_thm,
	ga_plus_times_distrib_thm,
	ga_plus_assoc_thm, ga_minus_scale_thm,
	ga_scale_scale_assoc_thm, ga_one_scale_thm,
	ga_times_scale_assoc_thm, ga_scale_times_assoc_thm
] THEN REPEAT strip_tac);
a(POP_ASM_T(rewrite_thm_tac o eq_sym_rule));
a(LEMMA_T ⌜u * v + ~ (ℕℝ 1) *⋎S u * v + v * v = v * v⌝ rewrite_thm_tac);
a(rewrite_tac[ga_plus_assoc_thm1]);
a(LEMMA_T ⌜u * v + ~ (ℕℝ 1) *⋎S u * v = Γ 0⌝ 
	(fn th => rewrite_tac[th, ga_plus_0_thm]));
a(rewrite_tac(map(conv_rule(ONCE_MAP_C eq_sym_conv)) [
	ga_plus_times_distrib_thm,
	ga_scale_times_assoc_thm]));
a(rewrite_tac[ga_scale_minus_thm, ga_minus_clauses, ga_0_times_thm]);
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
		(ot output_banner par) handle ex => reraise ex "z_output_theory"
	);
in
	val _ = output_theorems{out_file="wrk076.th.doc", theory="geomalg"};
end;
=TEX
} %\Hide
\end{document}



