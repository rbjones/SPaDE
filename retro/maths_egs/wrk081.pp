=IGN
********************************************************************************
wrk080.doc: this file is supplementary material for the ProofPower system

Copyright (c) 2004 Lemma 1 Ltd.

This file is supplied under the GNU General Public Licence (GPL) version 2.

See the file LICENSE supplied with ProofPower source for the terms of the GPL
or visit the OpenSource web site at http:/www.opensource.org/

Contact: Rob Arthan < rda@lemma-one.com >
********************************************************************************
wrk080.doc,v 1.29 2010/03/03 11:35:32 rda Exp
********************************************************************************
=IGN
pp_make_database -f -p hol maths_egs
docsml wrk080
xpp wrk080.doc -d maths_egs -i wrk080 &
doctex wrk080 wrk080.th; texdvi -b wrk080; texdvi wrk080; texdvi wrk080
=TEX
\documentclass[11pt,a4paper,leqno]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}
\usepackage{url}
\def\N{\mathbb{N}}
\def\D{\mathbb{D}}
\def\B{\mathbb{B}}
\def\R{\mathbb{R}}
\def\Z{\mathbb{Z}}
\def\Q{\mathbb{Q}}
\def\Lim{\mbox{{\sf lim}}}
\def\LimInf{\mbox{{\sf lim inf}}}
\def\LimSup{\mbox{{\sf lim sup}}}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}

\def\LogName{\mbox{{\sf log}}}
\def\Log#1{\LogName(#1)}

\def\SinName{\mbox{{\sf sin}}}
\def\Sin#1{\SinName(#1)}

\def\CosName{\mbox{{\sf cos}}}
\def\Cos#1{\CosName(#1)}

\def\Abs#1{|#1|}

\def\SizeName{\#}
\def\Size#1{\#\left(#1\right)}

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
\title{Mathematical Case Studies: \\ --- \\ 
Universal Algebra in Action: \\
Semigroups and Groups\thanks{
Added to repo 19 September 2010;
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
This {\ProductHOL} script contains definitions and proofs concerning
semigroups and groups demonstrating the universal algebra framework.

\end{abstract}
\vfill
\begin{centering}

\bf Copyright \copyright\ : Lemma 1 Ltd 2010--\number\year \\
Reference: LEMMA1/HOL/WRK081; Current git revision: \VCVersion


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

\newpage
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
The companion document \cite{LEMMA1/HOL/WRK080} defines
a type capable of representing any algebraic variety
(i.e., a finitary algebraic structure defined by a set
of equational laws).
In this document we give examples of how one can form
subtypes of this type to represent particular varieties.
This is part of a series of case studies in formalising some basic pure  mathematics in {\ProductHOL}.
Other parts of the case study deal, for example, with real analysis \cite{LEMMA1/HOL/WRK066} and with topology \cite{LEMMA1/HOL/WRK067}.


This document is a {\Product} literate script. It contains all the metalanguage (ML) commands required to create several theories, populate them with the formal definitions and prove and record all the theorems.
The descriptions include all the formal definitions in the Z-like concrete syntax for specification in {\ProductHOL}.
and a discussion of the theorems that have been proved about the objects specified.
There is an index to the formal definitions and the theory listings in section~\ref{index}.

%%%%
%%%%
%%%%
%%%%
\section{GENERAL PRINCIPLES}
We plan eventually to construct polymorphic types that represent a wide range of algebraic varieties. These will
all be defined as subtypes of the polymorphic type of
general algebras
=INLINEFT
'a ALGEBRA
=TEX
\ defined in \cite{LEMMA1/HOL/WRK080}.
For each variety, we also define a universal variety
that can be viewed  as the product of all the varieties in
the class.
Since it is pleasant to reuse operator symbols in different
contexts (e.g., $+$ in rings, fields and polynomial rings), we adopt the conventions of table \ref{tags} for single letter tags for some well-known varieties.
So addition in the universal ring will be $+⋎A$ while addition in the universal field will be $+⋎F$.
The tags are also used to distinguish the representation and abstraction functions for the subtypes.
This will probably be extended later to allocate two letter tags for other varieties.

\begin{table}
\begin{center}
\begin{tabular}{|l|l|p{0.4\hsize}|}\hline
Tag & Variety & Notes \\\hline\hline
A	& rings			& French: {\it anneaux}; R taken by reals \\\hline
B	& boolean algebras	& \\\hline
C	& complex numbers	& \\\hline
D	& integral domains	& \\\hline
E	&			& \\\hline
F	& fields		& Or use K for German: k\"{o}rper \\\hline
G	& group			& \\\hline
H	&			& \\\hline
I	&			& \\\hline
J	&			& \\\hline
K	&			& \\\hline
L	& lattices		& \\\hline
M	& monoids		& \\\hline
N	& natural numbers	& no subscript in {\ProductHOL} \\\hline
O	&			& \\\hline
P	& polynomial rings	& \\\hline
Q	& rationals		& \\\hline
R	& reals	& (Already extant in {\ProductHOL}) \\\hline
S	& semigroup		& \\\hline
T	&			& \\\hline
U	&			& The algebras of \cite{LEMMA1/HOL/WRK080} \\\hline
V	& real vector spaces	& use VS for abstract vector spaces \\\hline
W	&			& \\\hline
X	&			& \\\hline
Y	&			& \\\hline
Z	& integers		& German: {\it zahlen} (Already extant in {\ProductHOL}) \\\hline
\end{tabular}
\end{center}
\caption{A tagging convention for selected varieties}
\label{tags}
\end{table}

The plan is to have a systematic way of defining a type representing
any variety of interest. Each variety is defined by a set of equational
laws, which will typically be finite. So let {\em widget} name the members
of a variety defined by a finite set of laws (so widget is ``group'' or ``ring'' etc.).
The specific lists, trees and $\lambda$-abstractions that are involved in defining
widgets using the framework of \cite{LEMMA1/HOL/WRK080} are all
trivially simplified by rewriting. We can specialise
the so-called universal algebra of \cite{LEMMA1/HOL/WRK080} to produce
what we call {\em the universal widget}, which is the polymorphic
object that can be viewed as the product of all widgets.
In this universal widgets we can reason about equational facts that
are true in all widgets. By defining nice syntax for the operators (specifically
infix syntax for binary operators), we can work fairly naturally in the universal widget.

Thus, having defined
=INLINEFT
.⋎S
=TEX
\ as the multiplication in the universal semigroup, we can state and
prove facts such as the following:
=GFT
∀a b c d⦁ (a .⋎S b) .⋎S (c .⋎S d) = a.⋎S b .⋎S c .⋎S d
=TEX
.
Reasoning that is conditional on special properties,
e.g., commutativity, can also be formulated. For example, we may write:
=GFT
∀S x y z⦁ 
	(∀x y⦁ Rep⋎USE (x .⋎S y) S = Rep⋎USE (y .⋎S x) S)
⇒	Rep⋎USE (x .⋎S y .⋎S z) S = Rep⋎USE (z .⋎S y .⋎S z) S
=TEX
. In fact we introduce an operator $V_S$ which gives the value at a given
semigroup of an element of the universal semigroup. So the above may be written:
=GFT
∀S x y z⦁ 
	(∀x y⦁ V⋎S S (x .⋎S y) = V⋎S S (y .⋎S x))
⇒	V⋎S S (x .⋎S y .⋎S z) = V⋎S S (z .⋎S y .⋎S x)
=TEX

=TEX
We can also define what the Coq community call ``big operators'': generalised
sum operators. Our current approach to this is to define the operators
at the general level and then to specialise them to particular instances.
(See the definition of the operators
=INLINEFT
Π⋎U
=TEX
\ and
=INLINEFT
Π⋎N
=TEX
\ below and the theorems about them in the theory listings.

In the present document we present this approach in action to three
varieties: semigroups, monoids, and what we call double monoids, i.e., sets
like rings or lattices equipped with two monoid operations.
 
\section{SEMIGROUPS}

First of all, we must give the the ML commands to  introduce the new theory ``semigroups'' as a child of the theory ``algebras'' of universal algebras.

=TEX
%%%%
%%%%
%%%%
%%%%
=SML
force_delete_theory"semigroups" handle Fail _ => ();
open_theory"algebras";
new_theory"semigroups";
set_merge_pcs["basic_hol1", "'sets_alg"];
=TEX

%%%%
%%%%

The following function gives the representation of the equation that
the $p$-th binary operator $\mu_{p2}$ in an algebra is associative (see \cite{LEMMA1/HOL/WRK080}
and note that at the leaves of an expression
tree the odd-numbered nodes are the variables and the even-numbered nodes are the constant symbols).

=SML
declare_infix(310, "oo");
=TEX

ⓈHOLCONST
│ ⦏AssocEq⦎ : ℕ → EQUATION
├──────
│ ∀p⦁	AssocEq p =
│	let	v i = MkTree(2*i + 1, [])
│	and	x oo y = MkTree(p, [x; y])
│	in	((v 0 oo v 1) oo v 2, v 0 oo (v 1 oo v 2))
■

A semigroup is an algebra in which the 0-th binary operator is required to be associative.


ⓈHOLCONST
│ ⦏SemigroupLaws⦎ : EQUATION SET
├──────
│ SemigroupLaws = {AssocEq 0}
■


We define the type of semigroups and the abstraction and representation functions for it as a subtype of the type of algebras.

=SML
new_type_defn(["SEMIGROUP", "semigroup_def"], "SEMIGROUP", ["'a"], (
set_goal([], ⌜∃sg⦁ (λA⦁ A ∈ Variety SemigroupLaws) sg
⌝);
a(rewrite_tac[variety_type_lemmas]);
pop_thm()));
=TEX


ⓈHOLCONST
│ ⦏Rep⋎S⦎	: 'a SEMIGROUP → 'a ALGEBRA;
│ ⦏Abs⋎S⦎ 	: 'a ALGEBRA → 'a SEMIGROUP
├──────
│(∀S⦁	Abs⋎S(Rep⋎S S) = S) ∧
│(∀K⦁	K ∈ Variety SemigroupLaws ⇔ Rep⋎S(Abs⋎S K) = K)
■


The elements of the universal semigroup will have the following type:

=SML
new_type_defn(["USE"], "USE", ["'a"], (
set_goal([], ⌜∃f⦁ (λg⦁ g ∈ Safe SemigroupLaws) f
⌝);
a(rewrite_tac[variety_type_lemmas]);
pop_thm()));
=TEX

The following are the abstraction and representation functions for the elements of the universal semigroup as a subtype of the carrier type of the universal algebra for the semigroup laws.

ⓈHOLCONST
│ ⦏Rep⋎USE⦎	: 'a USE → ('a ALGEBRA → 'a);
│ ⦏Abs⋎USE⦎ 	: ('a ALGEBRA → 'a) → 'a USE
├──────
│(∀x⦁	Abs⋎USE(Rep⋎USE x) = x) ∧
│(∀f⦁	f ∈ Safe SemigroupLaws ⇔ Rep⋎USE(Abs⋎USE f) = f)
■

Now we can define the universal semigroup:

ⓈHOLCONST
│ ⦏UnivSemigroup⦎ : 'a USE SEMIGROUP
├──────
│ UnivSemigroup =
│ Abs⋎S (MkAlgebra
│	Universe
│	(λp a⦁ Abs⋎USE(Op(UnivAlgebra SemigroupLaws) p (Map Rep⋎USE a)))
│	Arbitrary)
■
=IGN
type_of ⌜Abs⋎S⌝;
type_of ⌜Abs⋎USE⌝;

=TEX

Now we can define the universal semigroup operation:
=SML
declare_infix(310, ".⋎S");
=TEX

ⓈHOLCONST
│ ⦏$.⋎S⦎ : 'a USE → 'a USE → 'a USE
├──────
│ ∀ x y⦁ x .⋎S y = Op (Rep⋎S UnivSemigroup) 0 [x; y]
■


The following is general material on semigroups that is under development.
The analogous material will be added to the sections on other kinds of variety presently.
The $V$ function evaluates an element of the universal semigroup
in a specific semigroup. I.e., viewing the universal semigroup as the product
$\prod S$ of all semigroups, $V_S\,S$ is projection onto the factor $S$.

ⓈHOLCONST
│ ⦏V⋎S⦎ : 'a SEMIGROUP → 'a USE → 'a
├──────
│ ∀S x⦁ V⋎S S x = Rep⋎USE x (Rep⋎S S)
■

The $K$ function is reminiscent of the $K$ combinator and is used in
connection with the theorem $k\_lemma$ of \cite{LEMMA1/HOL/WRK080}.

ⓈHOLCONST
│ ⦏K⋎S⦎ : 'a SEMIGROUP → 'a USE → 'a ALGEBRA → 'a
├──────
│ ∀S x⦁ K⋎S S x = λL⦁ if L = Rep⋎S S then V⋎S S x else Def L
■


%%%%
%%%%
%%%%
%%%%
\section{MONOIDS}

We must give the the ML commands to  introduce the new theory ``monoids'' as a child of the theory ``semigroups''.

=TEX
%%%%
%%%%
%%%%
%%%%
=SML
force_delete_theory"monoids" handle Fail _ => ();
open_theory"semigroups";
new_theory"monoids";
set_merge_pcs["basic_hol1", "'sets_alg"];
=TEX

%%%%
%%%%

The following function gives the representation of the equations asserting that
the $p$-th nullary operator $\mu_{p0}$ in an algebra is
a two-sided unit for the $q$-th binary operator.

=SML
declare_infix(310, "oo");
=TEX

ⓈHOLCONST
│ ⦏UnitEq⦎ : ℕ → ℕ → EQUATION SET
├──────
│ ∀p q⦁	UnitEq p q =
│	let	v i = MkTree(2*i + 1, [])
│	and	e = MkTree(p, [])
│	and	x oo y = MkTree(q, [x; y])
│	in	{(e oo v 0, v 0); (v 0 oo e, v 0)}
■

A monoid satisfies the semigroup laws and and has the nullary operator $\mu_{p0}$ as two-sided unit:


ⓈHOLCONST
│ ⦏MonoidLaws⦎ : EQUATION SET
├──────
│ MonoidLaws = SemigroupLaws ∪ UnitEq 0 0
■


We define the type of monoids and the abstraction and representation functions for it as a subtype of the type of algebras.

=SML
new_type_defn(["MONOID", "monoid_def"], "MONOID", ["'a"], (
set_goal([], ⌜∃mnd⦁ (λA⦁ A ∈ Variety MonoidLaws) mnd
⌝);
a(rewrite_tac[variety_type_lemmas]);
pop_thm()));
=TEX


ⓈHOLCONST
│ ⦏Rep⋎M⦎	: 'a MONOID → 'a ALGEBRA;
│ ⦏Abs⋎M⦎ 	: 'a ALGEBRA → 'a MONOID
├──────
│(∀S⦁	Abs⋎M(Rep⋎M S) = S) ∧
│(∀K⦁	K ∈ Variety MonoidLaws ⇔ Rep⋎M(Abs⋎M K) = K)
■


The elements of the universal monoid will have the following type:

=SML
new_type_defn(["UME"], "UME", ["'a"], (
set_goal([], ⌜∃f⦁ (λg⦁ g ∈ Safe MonoidLaws) f
⌝);
a(rewrite_tac[variety_type_lemmas]);
pop_thm()));
=TEX

The following are the abstraction and representation functions for the elements of the universal monoid as a subtype of the carrier type of the universal algebra for the monoid laws.

ⓈHOLCONST
│ ⦏Rep⋎UME⦎	: 'a UME → ('a ALGEBRA → 'a);
│ ⦏Abs⋎UME⦎ 	: ('a ALGEBRA → 'a) → 'a UME
├──────
│(∀x⦁	Abs⋎UME(Rep⋎UME x) = x) ∧
│(∀f⦁	f ∈ Safe MonoidLaws ⇔ Rep⋎UME(Abs⋎UME f) = f)
■

Now we can define the universal monoid:

ⓈHOLCONST
│ ⦏UnivMonoid⦎ : 'a UME MONOID
├──────
│ UnivMonoid =
│ Abs⋎M (MkAlgebra
│	Universe
│	(λp a⦁ Abs⋎UME(Op(UnivAlgebra MonoidLaws) p (Map Rep⋎UME a)))
│	Arbitrary)
■

=TEX

Now we can define the universal monoid operation:
=SML
declare_infix(310, ".⋎M");
=TEX

ⓈHOLCONST
│ ⦏$.⋎M⦎ : 'a UME│ → 'a UME → 'a UME
├──────
│ ∀ x y⦁ x .⋎M y = Op (Rep⋎M UnivMonoid) 0 [x; y]
■

and the unit element for the universal monoid:

ⓈHOLCONST
│ ⦏$1⋎M⦎ : 'a UME
├──────
│ 1⋎M = Op (Rep⋎M UnivMonoid) 0 []
■


%%%%
%%%%
%%%%
%%%%
\section{DOUBLE MONOIDS}

We adopt the term {\em double monoid} for a structure like a ring or a
lattice possessing two monoid structures.

We first give the the ML commands to  introduce the new theory ``double-monoids'' as a child of the theory ``monoids''.

=TEX
%%%%
%%%%
%%%%
%%%%
=SML

force_delete_theory"double-monoids" handle Fail _ => ();
open_theory"monoids";
new_theory"double-monoids";
set_merge_pcs["basic_hol1", "'sets_alg"];
=TEX

%%%%
%%%%
The laws for a monoid are about the constant and binary operator named 0,
we want to assert they also hold if we rename that as 1:

ⓈHOLCONST
│ ⦏DoubleMonoidLaws⦎ : EQUATION SET
├──────
│	DoubleMonoidLaws = MonoidLaws ∪ RenameLaws (λx⦁ 1) MonoidLaws
■


We define the type of double monoids and the abstraction and representation functions for it as a subtype of the type of algebras.

=SML
new_type_defn(["DOUBLE_MONOID", "double_monoid_def"], "DOUBLE_MONOID", ["'a"], (
set_goal([], ⌜∃dmnd⦁ (λA⦁ A ∈ Variety DoubleMonoidLaws) dmnd
⌝);
a(rewrite_tac[variety_type_lemmas]);
pop_thm()));
=TEX


ⓈHOLCONST
│ ⦏Rep⋎DM⦎	: 'a DOUBLE_MONOID → 'a ALGEBRA;
│ ⦏Abs⋎DM⦎ 	: 'a ALGEBRA → 'a DOUBLE_MONOID
├──────
│(∀S⦁	Abs⋎DM(Rep⋎DM S) = S) ∧
│(∀K⦁	K ∈ Variety DoubleMonoidLaws ⇔ Rep⋎DM(Abs⋎DM K) = K)
■


The elements of the universal monoio will have the following type:

=SML
new_type_defn(["UDME"], "UDME", ["'a"], (
set_goal([], ⌜∃f⦁ (λg⦁ g ∈ Safe DoubleMonoidLaws) f
⌝);
a(rewrite_tac[variety_type_lemmas]);
pop_thm()));
=TEX

The following are the abstraction and representation functions for the elements of the universal monoid as a subtype of the carrier type of the universal algebra for the monoid laws.

ⓈHOLCONST
│ ⦏Rep⋎UDME⦎	: 'a UDME → ('a ALGEBRA → 'a);
│ ⦏Abs⋎UDME⦎ 	: ('a ALGEBRA → 'a) → 'a UDME
├──────
│(∀x⦁	Abs⋎UDME(Rep⋎UDME x) = x) ∧
│(∀f⦁	f ∈ Safe DoubleMonoidLaws ⇔ Rep⋎UDME(Abs⋎UDME f) = f)
■

Now we can define the universal monoid:

ⓈHOLCONST
│ ⦏UnivDoubleMonoid⦎ : 'a UDME DOUBLE_MONOID
├──────
│ UnivDoubleMonoid =
│ Abs⋎DM (MkAlgebra
│	Universe
│	(λp a⦁ Abs⋎UDME(Op(UnivAlgebra DoubleMonoidLaws) p (Map Rep⋎UDME a)))
│	Arbitrary)
■

=TEX

Now we can define the universal double monoid operations:
=SML
declare_infix(310, ".⋎DM0");
declare_infix(310, ".⋎DM1");
=TEX

ⓈHOLCONST
│ ⦏$.⋎DM0⦎ ⦏$.⋎DM1⦎ : 'a UDME → 'a UDME → 'a UDME
├──────
│ ∀ x y⦁
│	x .⋎DM0 y = Op (Rep⋎DM UnivDoubleMonoid) 0 [x; y]
│ ∧	x .⋎DM1 y = Op (Rep⋎DM UnivDoubleMonoid) 1 [x; y]
■

and the unit elements for the universal double monoid:

ⓈHOLCONST
│ ⦏$1⋎DM0⦎ ⦏1⋎DM1⦎: 'a UDME
├──────
│	1⋎DM0 = Op (Rep⋎DM UnivDoubleMonoid) 0 []
│ ∧	1⋎DM1 = Op (Rep⋎DM UnivDoubleMonoid) 1 []
■

%%%%
%%%%
%%%%
%%%%
\section{MISCELLANEOUS EXAMPLES}

We must give the the ML commands to  introduce the new theory ``alg-egs'' as a child of the theory ``monoids''.

=TEX
%%%%
%%%%
%%%%
%%%%
=SML
force_delete_theory"alg-egs" handle Fail _ => ();
open_theory"monoids";
new_theory"alg-egs";
new_parent"double-monoids";
set_merge_pcs["basic_hol1", "'sets_alg"];
=TEX
The additive semigroup of positive natural numbers (represented as natural numbers via
$n \mapsto n - 1$).

ⓈHOLCONST
│ ⦏PosNat⦎ : ℕ SEMIGROUP
├──────
│ PosNat = Abs⋎S (DefAlgebra Universe 1 [] [] [(0, (λm n⦁m + n + 1))])
■

The monoid of polymorphic lists under concatenation.

ⓈHOLCONST
│ ⦏ListMonoid⦎ : 'a LIST MONOID
├──────
│ ListMonoid = Abs⋎M (DefAlgebra Universe [] [(0, [])] [] [(0, $⁀)])
■

The multiplicative monoid of natural numbers:


ⓈHOLCONST
│ ⦏NatMult⦎ : ℕ MONOID
├──────
│ NatMult = Abs⋎M (DefAlgebra Universe 1 [(0, 1)] [] [(0, $*)])
■

A generic distributed product operation using the $p$-th binary operation
to combine elements with the $q$-th constant as the unit:

ⓈHOLCONST
│ ⦏Π⋎U⦎ : ℕ → ℕ → 'a ALGEBRA → 'a LIST → 'a
├──────
│ ∀p q K x xs⦁
│	Π⋎U p q K [] = Op K q []
│ ∧	Π⋎U p q K (Cons x xs) = Op K p [x; Π⋎U p q K xs]
■

Instantiating the generic product to multiplication of natural numbers:

ⓈHOLCONST
│ ⦏Π⋎N⦎ : ℕ LIST → ℕ
├──────
│ Π⋎N = Π⋎U 0 0 (Rep⋎M NatMult)
■

See the theory listing for theorems, including a fact about natural number products derived from a general fact
about the generic product, a general property of semigroups and a property of semigroups conditional on commutativity.
(The approach of the last theorem, in particular,
is somewhat ad hoc and more support could perhaps be given for this kind of work.)

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
\HOLindexOff
\include{wrk0811.th}
\include{wrk0812.th}
\include{wrk0813.th}
\include{wrk0814.th}}
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

%%%%
%%%%
\subsection{Semigroups}
=TEX
We begin by working through the definitions proving
consistency as necessary.
%%%%
%%%%
%%%%
%%%%
=SML
=TEX
=SML
val _ = open_theory "semigroups";
val _ = set_merge_pcs["basic_hol1", "'sets_alg"];
val ⦏assoc_eq_def⦎ = get_spec⌜AssocEq⌝;
val ⦏semigroup_laws_def⦎ = get_spec⌜SemigroupLaws⌝;
val ⦏semigroup_def⦎ = get_defn "-" "SEMIGROUP";
=TEX
=SML
save_consistency_thm ⌜Abs⋎S⌝ (
push_consistency_goal ⌜Abs⋎S⌝;
a (strip_asm_tac (rewrite_rule[](simple_⇒_match_mp_rule type_lemmas_thm semigroup_def)));
a (∃_tac ⌜(rep, abs)⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
pop_thm());
val ⦏abs_s_def⦎ = get_spec⌜Abs⋎S⌝;
val ⦏rep_s_def⦎ = get_spec⌜Rep⋎S⌝;
val ⦏use_def⦎ = get_defn "-" "USE";
=TEX
=SML
save_consistency_thm ⌜Abs⋎USE⌝ (
push_consistency_goal ⌜Abs⋎USE⌝;
a (strip_asm_tac (rewrite_rule[let_def](simple_⇒_match_mp_rule type_lemmas_thm use_def)));
a (∃_tac ⌜(rep, abs)⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
pop_thm());
val ⦏abs_use_def⦎ = get_spec⌜Abs⋎USE⌝;
val ⦏rep_use_def⦎ = get_spec⌜Rep⋎USE⌝;
val ⦏univ_semigroup_def⦎ = get_spec⌜UnivSemigroup⌝;
val ⦏univ_semigroup_op_def⦎ = get_spec⌜$.⋎S⌝;
val ⦏v_s_def⦎ = get_spec⌜V⋎S⌝;
val ⦏k_s_def⦎ = get_spec⌜K⋎S⌝;
=TEX

What follows is ripe for automation. It is a forward proof from
that the operator of the universal semigroup satisfies all the
semigroup law. Semigroups are a special case because there is
only one law; what we have to do for monoids is more typical.
%%%%
%%%%
=SML

val semigroup_thm1 = rewrite_rule[]
	(conv_rule
	(LEFT_C (rewrite_conv[abs_s_def, rep_s_def, abs_use_def, rep_use_def]))
	(list_∀_elim[
		⌜Abs⋎S : 'a USE ALGEBRA → 'a USE SEMIGROUP⌝,
		⌜Rep⋎S : 'a USE SEMIGROUP → 'a USE ALGEBRA⌝] 	(list_∀_elim[
			⌜SemigroupLaws⌝,
			⌜Abs⋎USE⌝,
			⌜Rep⋎USE⌝]variety_laws_lemma)));

val semigroup_thm2 = rewrite_rule[eq_sym_rule univ_semigroup_def]
	(once_rewrite_rule[eq_sym_rule (rewrite_rule[abs_s_def] semigroup_thm1)] semigroup_thm1);

val semigroup_thm3 = rewrite_rule[semigroup_thm1]
	let	val t = hd(snd(strip_app(concl semigroup_thm1)));
	in	∀_elim t(∧_right_elim rep_s_def)
	end;

val semigroup_thm4 =
	rewrite_conv[
		car_universe_thm,
		semigroup_thm3,
		univ_semigroup_def
	] ⌜Car (Rep⋎S UnivSemigroup)⌝;

=TEX
%%%%
%%%%
Note the following needs the proof contexts $basic\_hol1" and $'sets\_alg$.

=SML
val semigroup_thm5 =
	(rewrite_rule [
		semigroup_laws_def,
		assoc_eq_def,
		prove_rule[] ⌜∀f s t⦁
			(∀x y⦁ x = s ∧ y = t ⇒ (∀ I
         ⦁ f I x = f I y)) ⇔ (∀ I
         ⦁ f I s = f I t)⌝,
		semigroup_thm4,
		let_def,
		variety_def,
		derived_op_def,
		map_def] semigroup_thm2);
=TEX
Finally, we specialise to an interpration that interprets
the $v_n$ for small $n$ as distinct variables.
=SML
val semigroup_thm6 = all_∀_intro(rewrite_rule[]
	(∀_elim⌜λv⦁
		if	v = 0
		then	x : 'a USE
		else if	v = 1
		then	y
		else	z⌝ semigroup_thm5));
=TEX
We can now use this to show that the operator of the universal semigroup
does indeed satisfy the associative law: 
=SML

val ⦏univ_semigroup_assoc_thm⦎ = save_thm( "univ_semigroup_assoc_thm", (
set_goal([], ⌜∀x y z⦁
	(x .⋎S y) .⋎S z = x .⋎S (y .⋎S z)
⌝);
a(REPEAT strip_tac);
a(rewrite_tac[univ_semigroup_op_def, semigroup_thm6]);
pop_thm()));


=TEX

%%%%
%%%%
\subsection{Monoids}
=TEX
We begin by working through the definitions proving
consistency as necessary.
%%%%
%%%%
%%%%
%%%%
=SML
=TEX
=SML
val _ = open_theory "monoids";
val _ = set_merge_pcs["basic_hol1", "'sets_alg"];
val ⦏unit_eq_def⦎ = get_spec⌜UnitEq⌝;
val ⦏monoid_laws_def⦎ = get_spec⌜MonoidLaws⌝;
val ⦏monoid_def⦎ = get_defn "-" "MONOID";
=TEX
=SML
save_consistency_thm ⌜Abs⋎M⌝ (
push_consistency_goal ⌜Abs⋎M⌝;
a (strip_asm_tac (rewrite_rule[](simple_⇒_match_mp_rule type_lemmas_thm monoid_def)));
a (∃_tac ⌜(rep, abs)⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
pop_thm());
val ⦏abs_m_def⦎ = get_spec⌜Abs⋎M⌝;
val ⦏rep_m_def⦎ = get_spec⌜Rep⋎M⌝;
val ⦏ume_def⦎ = get_defn "-" "UME";
=TEX
=SML
save_consistency_thm ⌜Abs⋎UME⌝ (
push_consistency_goal ⌜Abs⋎UME⌝;
a (strip_asm_tac (rewrite_rule[let_def](simple_⇒_match_mp_rule type_lemmas_thm ume_def)));
a (∃_tac ⌜(rep, abs)⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
pop_thm());
val ⦏abs_ume_def⦎ = get_spec⌜Abs⋎UME⌝;
val ⦏rep_ume_def⦎ = get_spec⌜Rep⋎UME⌝;
val ⦏univ_monoid_def⦎ = get_spec⌜UnivMonoid⌝;
val ⦏univ_monoid_op_def⦎ = get_spec⌜$.⋎M⌝;
val ⦏univ_monoid_unit_def⦎ = get_spec⌜1⋎M⌝;
=TEX
As with semigroups we give a forward proof that the operator of the
universal monoid satisfies the monoid laws.
%%%%
%%%%
=SML

val monoid_thm1 = rewrite_rule[]
	(conv_rule
	(LEFT_C (rewrite_conv[abs_m_def, rep_m_def, abs_ume_def, rep_ume_def]))
	(list_∀_elim[
		⌜Abs⋎M : 'a UME ALGEBRA → 'a UME MONOID⌝,
		⌜Rep⋎M : 'a UME MONOID → 'a UME ALGEBRA⌝] 	(list_∀_elim[
			⌜MonoidLaws⌝,
			⌜Abs⋎UME⌝,
			⌜Rep⋎UME⌝]variety_laws_lemma)));


val monoid_thm2 =
	rewrite_rule[eq_sym_rule univ_monoid_def]
		(once_rewrite_rule[eq_sym_rule (rewrite_rule[abs_m_def] monoid_thm1)]
			monoid_thm1);

val monoid_thm2 = rewrite_rule[eq_sym_rule univ_monoid_def]
	(once_rewrite_rule[eq_sym_rule (rewrite_rule[abs_m_def] monoid_thm1)] monoid_thm1);

val monoid_thm3 = rewrite_rule[monoid_thm1]
	let	val t = hd(snd(strip_app(concl monoid_thm1)));
	in	∀_elim t(∧_right_elim rep_m_def)
	end;

val monoid_thm4 =
	rewrite_conv[
		car_universe_thm,
		monoid_thm3,
		univ_monoid_def
	] ⌜Car (Rep⋎M UnivMonoid)⌝;

val monoid_thm5 =
	(pc_rule1 "sets_ext1" rewrite_rule [
		semigroup_laws_def,
		monoid_laws_def,
		assoc_eq_def,
		unit_eq_def,
		monoid_thm4,
		let_def,
		variety_def] monoid_thm2);

=TEX
The following metalanguage functions let us extract the laws from the
theorem just proved.
=SML

fun ⦏flat_∨⦎ (t : TERM) : TERM list = (
	if	is_∨ t
	then	flat (map flat_∨ (strip_∨ t))
	else	[t]
);

fun ⦏get_laws⦎ (thm : THM) : (TERM * TERM) list = (
	let	val b = snd(strip_∀(concl thm));
		val ant = fst(dest_⇒ b);
		val eqs = flat_∨ ant;
		val rhses = map (snd o dest_eq) eqs;
		val res = map dest_pair rhses;
	in	res
	end
);
=TEX
Using this we specialise the theorem to each law in turn:
=SML
val monoid_thms6 =
	let	val pairs = get_laws monoid_thm5;
	in	map (fn (t1, t2) => rewrite_rule[] (list_∀_elim [t1, t2] monoid_thm5)) pairs
	end;
=TEX
Finally, we specialise to an interpration that interprets
the $v_n$ for small $n$ as distinct variables.
=SML

val monoid_thms7 = map 
	(fn thm => all_∀_intro(rewrite_rule[
		let_def,
		derived_op_def,
		map_def]
		(∀_elim⌜λv⦁
			if	v = 0
			then	x : 'a UME
			else if	v = 1
			then	y
			else	z⌝ thm))) monoid_thms6;


=TEX
We can now use this to show that the operators of the universal monoid
do indeed satisfy the monoid laws: 
=SML

val ⦏univ_monoid_assoc_thm⦎ = save_thm( "univ_monoid_assoc_thm", (
set_goal([], ⌜∀x y z⦁
	(x .⋎M y) .⋎M z = x .⋎M (y .⋎M z)
⌝);
a(REPEAT strip_tac);
a(rewrite_tac(univ_monoid_op_def :: monoid_thms7));
pop_thm()));

=TEX
=SML

val ⦏univ_monoid_unit_thm⦎ = save_thm( "univ_monoid_unit_thm", (
set_goal([], ⌜∀x⦁
	1⋎M .⋎M x = x
∧	x .⋎M 1⋎M = x
⌝);
a(REPEAT strip_tac THEN
	rewrite_tac(univ_monoid_op_def :: univ_monoid_unit_def :: monoid_thms7));
pop_thm()));

=TEX
%%%%
%%%%
\subsection{Double Monoids}
=TEX
We begin by working through the definitions proving
consistency as necessary.
%%%%
%%%%
%%%%
%%%%
=SML
=TEX
=SML
val _ = open_theory "double-monoids";
val _ = set_merge_pcs["basic_hol1", "'sets_alg"];
val ⦏double_monoid_laws_def⦎ = get_spec⌜DoubleMonoidLaws⌝;
val ⦏double_monoid_def⦎ = get_defn "-" "DOUBLE_MONOID";
=TEX
=SML
save_consistency_thm ⌜Abs⋎DM⌝ (
push_consistency_goal ⌜Abs⋎DM⌝;
a (strip_asm_tac (rewrite_rule[](simple_⇒_match_mp_rule type_lemmas_thm double_monoid_def)));
a (∃_tac ⌜(rep, abs)⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
pop_thm());
val ⦏abs_dm_def⦎ = get_spec⌜Abs⋎DM⌝;
val ⦏rep_dm_def⦎ = get_spec⌜Rep⋎DM⌝;
val ⦏udme_def⦎ = get_defn "-" "UDME";
=TEX
=SML
save_consistency_thm ⌜Abs⋎UDME⌝ (
push_consistency_goal ⌜Abs⋎UDME⌝;
a (strip_asm_tac (rewrite_rule[let_def](simple_⇒_match_mp_rule type_lemmas_thm udme_def)));
a (∃_tac ⌜(rep, abs)⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
pop_thm());
val ⦏abs_udme_def⦎ = get_spec⌜Abs⋎UDME⌝;
val ⦏rep_udme_def⦎ = get_spec⌜Rep⋎UDME⌝;
val ⦏univ_double_monoid_def⦎ = get_spec⌜UnivDoubleMonoid⌝;
val ⦏univ_double_monoid_op_0_def⦎ = get_spec⌜$.⋎DM0⌝;
val ⦏univ_double_monoid_op_1_def⦎ = get_spec⌜$.⋎DM0⌝;
val ⦏univ_double_monoid_unit_0_def⦎ = get_spec⌜1⋎DM0⌝;
val ⦏univ_double_monoid_unit_1_def⦎ = get_spec⌜1⋎DM1⌝;

=TEX
%%%%
%%%%
=SML

val double_monoid_thm1 = rewrite_rule[]
	(conv_rule
	(LEFT_C (rewrite_conv[abs_dm_def, rep_dm_def, abs_udme_def, rep_udme_def]))
	(list_∀_elim[
		⌜Abs⋎DM : 'a UDME ALGEBRA → 'a UDME DOUBLE_MONOID⌝,
		⌜Rep⋎DM : 'a UDME DOUBLE_MONOID → 'a UDME ALGEBRA⌝] 	(list_∀_elim[
			⌜DoubleMonoidLaws⌝,
			⌜Abs⋎UDME⌝,
			⌜Rep⋎UDME⌝]variety_laws_lemma)));

val double_monoid_thm2 =
	rewrite_rule[eq_sym_rule univ_double_monoid_def]
		(once_rewrite_rule[eq_sym_rule (rewrite_rule[abs_dm_def] double_monoid_thm1)]
			double_monoid_thm1);

val double_monoid_thm3 = rewrite_rule[double_monoid_thm1]
	let	val t = hd(snd(strip_app(concl double_monoid_thm1)));
	in	∀_elim t(∧_right_elim rep_dm_def)
	end;

val double_monoid_thm4 =
	rewrite_conv[
		car_universe_thm,
		double_monoid_thm3,
		univ_double_monoid_def
	] ⌜Car (Rep⋎DM UnivDoubleMonoid)⌝;
=TEX
The following involves a hack to make the function {\em get\_laws} apply.
=SML
val double_monoid_thm5 =
	pure_rewrite_rule[prove_rule[]⌜∀x y a b⦁x = a ∧ y = b ⇔ (x, y) = (a, b)⌝]
	(merge_pcs_rule1 ["'sets_ext1", "basic_hol1"] rewrite_rule [
		semigroup_laws_def,
		double_monoid_laws_def,
		monoid_laws_def,
		rename_laws_clauses,
		rename_term_def,
		map_def,
		assoc_eq_def,
		unit_eq_def,
		double_monoid_thm4,
		let_def,
		variety_def] double_monoid_thm2);

val double_monoid_thms6 =
	let	val pairs = get_laws double_monoid_thm5;
	in	map (fn (t1, t2) => rewrite_rule[] (list_∀_elim [t1, t2] double_monoid_thm5)) pairs
	end;

=TEX
Finally, we specialise to an interpration that interprets
the $v_n$ for small $n$ as distinct variables.
=SML

val double_monoid_thms7 = map 
	(fn thm => all_∀_intro(rewrite_rule[
		let_def,
		derived_op_def,
		map_def]
		(∀_elim⌜λv⦁
			if	v = 0
			then	x : 'a UDME
			else if	v = 1
			then	y
			else	z⌝ thm))) double_monoid_thms6;


=TEX
Now we can show easily that the operators of the universal double monoid
do indeed satisfy the relevant monoid laws.
=SML

val ⦏univ_double_monoid_assoc__0_thm⦎ = save_thm( "univ_double_monoid_assoc_thm", (
set_goal([], ⌜∀x y z⦁
	(x .⋎DM0 y) .⋎DM0 z = x .⋎DM0 (y .⋎DM0 z)
∧	(x .⋎DM1 y) .⋎DM1 z = x .⋎DM1 (y .⋎DM1 z)
⌝);
a(rewrite_tac(univ_double_monoid_op_0_def ::
	univ_double_monoid_op_1_def :: double_monoid_thms7));
pop_thm()));

=TEX
%%%%
%%%%
=SML

val ⦏univ_double_monoid_unit_thm⦎ = save_thm( "univ_double_monoid_unit_thm", (
set_goal([], ⌜∀x⦁
	1⋎DM0 .⋎DM0 x = x
∧	x .⋎DM1 1⋎DM1 = x
⌝);
a(rewrite_tac(univ_double_monoid_op_0_def ::
		univ_double_monoid_unit_0_def ::
		univ_double_monoid_op_1_def ::
		univ_double_monoid_unit_1_def :: double_monoid_thms7));
pop_thm()));


=TEX
%%%%
%%%%
\subsection{Miscellaneous Examples}
=SML

val _ = open_theory "alg-egs";
val _ = set_merge_pcs["basic_hol1", "'sets_alg"];
val ⦏pos_nat_def⦎ = get_spec⌜PosNat⌝;
val ⦏list_monoid_def⦎ = get_spec⌜ListMonoid⌝;
val ⦏nat_mult_def⦎ = get_spec⌜NatMult⌝;
val ⦏π_u_def⦎ = get_spec ⌜Π⋎U⌝;
val ⦏π_n_def⦎ = get_spec ⌜Π⋎N⌝;
=TEX
%%%%
%%%%
=SML

val ⦏rep_s_pos_nat_def_algebra_thm⦎ = save_thm( "rep_s_pos_nat_def_algebra_thm", (
set_goal([], ⌜Rep⋎S PosNat = DefAlgebra Universe 1 [] [] [(0, (λ m n⦁ m + n + 1))]⌝);
a(rewrite_tac [pos_nat_def, conv_rule (ONCE_MAP_C eq_sym_conv) (∧_right_elim rep_s_def)]);
a(rewrite_tac[def_algebra_def, def_bin_ops_def, def_un_ops_def, def_cons_def,
	let_def, variety_def, car_universe_thm,
	semigroup_laws_def, assoc_eq_def]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1 THEN
	rewrite_tac[derived_op_def, let_def, map_def, length_def]
		THEN PC_T1 "lin_arith" prove_tac[]);
pop_thm()));

=TEX
%%%%
%%%%
=SML

val ⦏pos_nat_variety_thm⦎ = save_thm( "pos_nat_variety_thm", (
set_goal([], ⌜DefAlgebra Universe 1 [] [] [(0, (λ m n⦁ m + n + 1))] ∈ Variety SemigroupLaws⌝);
a(rewrite_tac [conv_rule (ONCE_MAP_C eq_sym_conv) rep_s_pos_nat_def_algebra_thm]);
a(rewrite_tac[rep_s_def, pos_nat_def]);
pop_thm()));


=TEX
%%%%
%%%%
=SML

val ⦏rep_m_list_monoid_def_algebra_thm⦎ = save_thm( "rep_m_list_monoid_def_algebra_thm", (
set_goal([], ⌜Rep⋎M ListMonoid = DefAlgebra Universe [] [(0, [])] [] [(0, $@)]⌝);
a(rewrite_tac [list_monoid_def, conv_rule (ONCE_MAP_C eq_sym_conv) (∧_right_elim rep_m_def)]);
a(rewrite_tac[def_algebra_def, def_bin_ops_def, def_un_ops_def, def_cons_def,
	let_def, variety_def, car_universe_thm,
	monoid_laws_def, semigroup_laws_def, assoc_eq_def, unit_eq_def]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1 THEN
	rewrite_tac[derived_op_def, let_def, map_def, length_def]
	THEN rewrite_tac[ append_assoc_thm, append_empty_thm, append_def]);
pop_thm()));

=TEX
%%%%
%%%%
=SML

val ⦏list_monoid_variety_thm⦎ = save_thm( "list_monoid_variety_thm", (
set_goal([], ⌜DefAlgebra Universe [] [(0, [])] [] [(0, $@)]∈ Variety MonoidLaws⌝);
a(rewrite_tac [conv_rule (ONCE_MAP_C eq_sym_conv) rep_m_list_monoid_def_algebra_thm]);
a(rewrite_tac[rep_m_def, list_monoid_def]);
pop_thm()));


=TEX
%%%%
%%%%
=SML

val ⦏rep_m_nat_mult_def_algebra_thm⦎ = save_thm( "rep_m_nat_mult_def_algebra_thm", (
set_goal([], ⌜Rep⋎M NatMult = DefAlgebra Universe 1 [(0, 1)] [] [(0, $*)]⌝);
a(rewrite_tac [nat_mult_def, conv_rule (ONCE_MAP_C eq_sym_conv) (∧_right_elim rep_m_def)]);
a(rewrite_tac[def_algebra_def, def_bin_ops_def, def_un_ops_def, def_cons_def,
	let_def, variety_def, car_universe_thm,
	monoid_laws_def, semigroup_laws_def, assoc_eq_def, unit_eq_def]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1 THEN
	rewrite_tac[derived_op_def, let_def, map_def, length_def]
	THEN PC_T1 "lin_arith" prove_tac[]);
pop_thm()));

=TEX
%%%%
%%%%
=SML

val ⦏nat_mult_variety_thm⦎ = save_thm( "nat_mult_variety_thm", (
set_goal([], ⌜DefAlgebra Universe 1 [(0, 1)] [] [(0, $*)]∈ Variety MonoidLaws⌝);
a(rewrite_tac [conv_rule (ONCE_MAP_C eq_sym_conv) rep_m_nat_mult_def_algebra_thm]);
a(rewrite_tac[rep_m_def, nat_mult_def]);
pop_thm()));

=TEX
%%%%
%%%%
=SML

val monoid_laws_thm1 =
	pc_rule1 "sets_ext" rewrite_rule[asm_rule ⌜Car K = Universe⌝]
	(undisch_rule(fst(⇔_elim(MERGE_PCS_C1 ["sets_ext"]
	rewrite_conv[monoid_laws_def, unit_eq_def, assoc_eq_def,
		variety_def, monoid_laws_def, semigroup_laws_def, let_def]
			⌜K ∈ Variety MonoidLaws⌝))));

val monoid_laws_thms2 =
	let	val pairs = get_laws monoid_laws_thm1;
	in	map (fn (t1, t2) => rewrite_rule[] (list_∀_elim [t1, t2] monoid_laws_thm1)) pairs
	end;

val monoid_laws_bc_thms = map (fn thm => 
	rewrite_rule[taut_rule⌜∀p q r⦁ (p ⇒ q ⇒ r) ⇔ (p ∧ q ⇒ r)⌝]
	(all_∀_intro (all_disch_rule(rewrite_rule[
		let_def,
		derived_op_def,
		map_def]
		(∀_elim⌜λv⦁
			if	v = 0
			then	x : 'a
			else if	v = 1
			then	y
			else	z⌝ thm))))) monoid_laws_thms2;

val ⦏π_u_homomorphism_thm⦎ = save_thm( "π_u_homomorphism_thm", (
set_goal([], ⌜∀K xs ys⦁
	Car K = Universe
∧	K ∈ Variety MonoidLaws
⇒	Π⋎U 0 0 K (xs ⁀ ys) = Op K 0 [Π⋎U 0 0 K xs; Π⋎U 0 0 K ys]
⌝);
a(REPEAT strip_tac);
a(intro_∀_tac1⌜ys⌝);
a(list_induction_tac⌜xs⌝ THEN rewrite_tac[π_u_def, append_def]
	THEN REPEAT strip_tac
	THEN ALL_FC_T asm_rewrite_tac monoid_laws_bc_thms);
pop_thm()));


=TEX
%%%%
%%%%

Instantiating the above to a specific monoid is most naturally
done as a forward proof.
See the theory listing for the statement. 
=SML
val  ⦏π_n_homomorphism_thm⦎ = save_thm( "π_n_homomorphism_thm", (
	all_∀_intro
	(rewrite_rule[rep_m_nat_mult_def_algebra_thm,
		car_op_def_def_algebra_universe_thm, let_def, def_bin_ops_def,
		length_def]
	(rewrite_rule[conv_rule(ONCE_MAP_C eq_sym_conv) π_n_def]
	(conv_rule (LEFT_C (rewrite_conv[rep_m_nat_mult_def_algebra_thm,
		nat_mult_variety_thm, car_op_def_def_algebra_universe_thm]))
	(all_∀_elim (∀_elim⌜Rep⋎M NatMult⌝ π_u_homomorphism_thm)))))));

=TEX
%%%%
%%%%
A general derived law at the semigroup level (not very interesting).
=SML

val ⦏semigroup_derived_law_eg_thm⦎ = save_thm( "semigroup_derived_law_eg_thm", (
set_goal([], ⌜∀a b c d⦁ (a .⋎S b) .⋎S (c .⋎S d) = a.⋎S b .⋎S c .⋎S d⌝);
a(rewrite_tac [univ_semigroup_assoc_thm]);
pop_thm()));

=TEX
%%%%
%%%%

=SML

val ⦏rep_use_thm1⦎ = all_∀_intro(
	pc_rule1 "predicates" rewrite_rule[rep_use_def]
		(rewrite_rule[let_def, derived_op_def, map_def]
		(list_∀_elim[⌜SemigroupLaws⌝,
		⌜λv⦁  Rep⋎USE (if v = 0 then x else y)⌝,
		⌜let	v i = MkTree(2*i + 1, [])
		 and	x oo y = MkTree(p, [x; y])
		 in	(v 0 oo v 1)⌝] derived_op_safe_thm)));

=TEX
%%%%
%%%%

=SML

val ⦏k_s_safe_thm⦎ = save_thm( "k_s_safe_thm", (
set_goal([], ⌜∀S x⦁ K⋎S S x ∈ Safe SemigroupLaws⌝);
a(REPEAT strip_tac);
a(rewrite_tac[safe_def, k_s_def] THEN strip_tac);
a(cases_tac ⌜K = Rep⋎S S⌝ THEN asm_rewrite_tac[car_def, rep_s_def]
	THEN REPEAT strip_tac);
a(rewrite_tac[v_s_def]);
a(LEMMA_T ⌜Rep⋎USE x ∈ Safe SemigroupLaws⌝ ante_tac
	THEN1 rewrite_tac[rep_use_def]);
a(rewrite_tac[safe_def]);
a(STRIP_T (ante_tac o ∀_elim⌜Rep⋎S S⌝));
a(rewrite_tac[rep_s_def]);
pop_thm()));

val ⦏rep_use_abs_use_k_s_thm⦎ = save_thm ("rep_use_abs_use_k_s_thm",
	pure_rewrite_rule[rep_use_def] k_s_safe_thm);
=TEX
%%%%
%%%%

=SML

val ⦏semigroup_k_lemma⦎ = save_thm( "semigroup_k_lemma", (
set_goal([], ⌜∀S x y⦁ 
	V⋎S S (x .⋎S y) =
	V⋎S S (Abs⋎USE (K⋎S S x) .⋎S Abs⋎USE (K⋎S S y))
⌝);
a(REPEAT strip_tac);
a(rewrite_tac[univ_semigroup_op_def, univ_semigroup_def, semigroup_thm3,
	v_s_def, car_universe_thm, map_def, rep_use_thm1]);
a(conv_tac(LEFT_C (once_rewrite_conv[k_lemma])));
a(rewrite_tac[map_def, rep_use_abs_use_k_s_thm]);
a(rewrite_tac[k_s_def, v_s_def, car_op_def_univ_algebra_thm, univ_op_def, let_def, map_def]);
pop_thm()));

=TEX
%%%%
%%%%
TBD: a conditional derived law about semigroups.
=SML

val ⦏abelian_semigroup_derived_law_eg_thm⦎ = save_thm( "abelian_semigroup_derived_law_eg_thm", (
set_goal([], ⌜∀S x y z⦁ 
	(∀x y⦁ V⋎S S (x .⋎S y) = V⋎S S (y .⋎S x))
⇒	V⋎S S (x .⋎S y .⋎S z) = V⋎S S (z .⋎S y .⋎S x)
⌝);
a(REPEAT strip_tac);
a(TOP_ASM_T (rewrite_thm_tac o ∀_elim⌜x⌝));
a(rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv) univ_semigroup_assoc_thm]);
a(once_rewrite_tac[semigroup_k_lemma]);
a(rewrite_tac[k_s_def]);
a(TOP_ASM_T (rewrite_thm_tac o ∀_elim⌜y⌝));
pop_thm()));

=TEX
%%%%
=TEX
%%%%
%%%%
%%%%
%%%%
=TEX
\subsection{Epilogue}\label{END}
} % matches turning off of HOL index entries.
=TEX
%%%%
%%%%
=SML
open_theory"semigroups";
output_theory{out_file="wrk0811.th.doc", theory="semigroups"};
open_theory"monoids";
output_theory{out_file="wrk0812.th.doc", theory="monoids"};
open_theory"double-monoids";
output_theory{out_file="wrk0813.th.doc", theory="double-monoids"};
open_theory"alg-egs";
output_theory{out_file="wrk0814.th.doc", theory="alg-egs"};
=TEX
\end{document}
=SML

