=IGN
********************************************************************************
wrk067.doc: this file is supplementary material for the ProofPower system

Copyright (c) 2004 Lemma 1 Ltd.

This file is supplied under the GNU General Public Licence (GPL) version 2.

See the file LICENSE supplied with ProofPower source for the terms of the GPL
or visit the OpenSource web site at http://www.opensource.org/

Contact: Rob Arthan < rda@lemma-one.com >
********************************************************************************
$Id: wrk067.doc,v 1.75 2012/06/05 10:24:46 rda Exp rda $
********************************************************************************
pp_make_database -f -p hol topology
docsml wrk066 wrk067
pp -d topology -i wrk066,wrk067 >wrk067.log
doctex wrk067.doc  wrk067[1234].th.doc ; docdvi wrk067
=TEX
\documentclass[11pt,a4paper]{article}
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

\title{Mathematical Case Studies: \\ --- \\ Some Topology\thanks{
First posted 11 April 2004;
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
This {\ProductHOL} document contains definitions and proofs concerning some
basics of abstract topology, metric space theory and algebraic topology (more precisely,
elementary homotopy theory).
It presents the material using the approach taken in  \cite{LEMMA1/HOL/WRK066}: the main body of the document contains the definitions together with a narrative commentary including a discussion of the theorems that have been proved. This is followed by a listing of the theory and an index to the theorems and definitions. The source text of this document also contains the proof scripts, but these are suppressed
from the printed form by default.

The coverage of abstract topology includes the definitions of the following:
topologies; construction of new topologies from old as (binary) product spaces or subspaces;
continuity, Hausdorff spaces; connectedness;  compactness, the interior, boundary and closure operators; a notion of {\em protocomplex} that we later use to define CW complexes. A range of basic theorems are
proved, including: continuity of functional composition and of the structural maps
for products; preservation of compactness and connectedness under continuous maps;
connectedness resp. compactness of products of connected resp. compact spaces.


The coverage of metric spaces is very minimal. The standard arguments in the algebraic
topology we are interested in can be done with almost no metric space ideas. The main idea
that is needed is the notion of the Lebesgue number of a covering (which is needed to
show that if you cover an interval or a square with open sets, then on some suitably fine subdivision of
the interval or square, each subinterval or grid cell is contained in one of the covering sets).
With these applications in view, the metrics for the real line and the plane are defined.
We also define euclidean $n$-space in general using lists of reals for the representation and use these to define cubes, spheres and CW complexes.
(Technical note: we actually use the $L_1$ (Manhattan taxi-cab) metric on product spaces,
not the more usual $L_2$ (Euclidean) metric. The $L_1$ metric gives the same topology
and makes the arithmetic easier in most cases.)

Finally, we deal with some basics of homotopy theory. This material is very far from
complete. Currently we have: the definition of path connectedness and the proof
that path connected spaces are connected; definitions of the notions of homotopy
and of homotopy classes with the proofs that the homotopy relation is an equivalence
relation; definitions of the path space (qua set, not qua space, in fact) together
with the of the operations that induce a groupoid structure on the homotopy
classes in the path space together with the proofs that these operations do indeed
give a groupoid modulo homotopy equivalence; definition of a covering projection and a
proof that covering projections enjoy the unique lifting property and the homotopy
lifting property.

\end{abstract}
\vfill
\begin{centering}

\bf Copyright \copyright\ : Lemma 1 Ltd 2004--\number\year \\
Reference: LEMMA1/HOL/WRK067; Current git revision: \VCVersion


\end{centering}
\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
\tableofcontents
\newpage
%\subsection{Document cross references}

\subsection*{To Do}
This document is a somewhat inchoate state pending some more work on algebra
to inform the work on elementary homotopy theory.

\begin{itemize}
\item
Add some more references.
\item
Some of the results in the theory of the real line and the plane belong logically in the theory of metric spaces. Move them into the right place.
\item
Make the treatment of homotopy classes use the treatment of equivalence relations in \cite{LEMMA1/HOL/WRK068}.
\item
Complete the work on homotopy theory at least to the point where the fundamental group can be defined and said to be a group in the sense of  \cite{LEMMA1/HOL/WRK068} (and calculate some non-trivial fundamental groups, e.g., that of the circle).
\end{itemize}

\subsection*{Acknowledgments}
Thanks to Bill Richter for pointing out that one can define the notion of homotopy lifting property with respect to a given space without falling foul of the restriction on type variables in constant specifications.

\bibliographystyle{fmu}
\bibliography{fmu}

\vfill
\newpage
%%%%
%%%%

%%%%
%%%%

\section{ABSTRACT TOPOLOGY}
%%%%
%%%%

%%%%
%%%%
\subsection{Technical Prelude}
The following ML commands set up a theory ``topology'' to hold the definitions and theorems
and set up a convenient proof context. The parents of the theory are the theory
``bin\_rel'' of binary relations and the theory ``fincomb'' of finite combinatorics.
=SML
force_delete_theory "topology" handle Fail _ => ();
open_theory "bin_rel";
set_merge_pcs["basic_hol1", "'sets_alg"];
new_theory "topology";
new_parent"fincomb";
=TEX
%%%%
%%%%

%%%%
%%%%

=TEX
\subsection{Topologies}

We begin with the definition of a topology. We follow the most common tradition
of defining a topology by specifying its set of open sets. The polymorphic set
{\it Topology} is the set of all sets of sets that we will consider to be topologies.
We do not require a topology to form a topology on the universe of the type of its points.
For example, we wish to consider sets such as the unit interval in the real line to be
topological spaces in their own right. This actually simplifies the definition: we just
require a topology to be a set of sets that is closed under arbitrary unions and
binary intersections. We do not require the carrier set of the topology to
be a non-empty set (as some elementary text books do, unnecessarily).
Nor do we need to make a special case of
the empty set --- it will be shown to be an open set in any topology (as the union
of an empty set of open sets).
%%%%
%%%%

=SML
ⓈHOLCONST
│ ⦏Topology⦎ : 'a SET SET SET
├──────
│ 	Topology =
│	{τ | (∀V⦁ V ⊆ τ ⇒ ⋃ V ∈ τ) ∧ (∀A B⦁A ∈ τ ∧ B ∈ τ ⇒ A ∩ B ∈ τ)}
■
=TEX
We can recover the carrier set of a topology as the union of all its open sets.
It reads quite nicely to call this the {\em space} of the topology.
%%%%
%%%%

=SML
ⓈHOLCONST
│ ⦏Space⋎T⦎ : 'a SET SET → 'a SET
├──────
│ ∀τ⦁ Space⋎T τ = ⋃ τ
■
=TEX
A set is {\em closed} with respect to a topology, $\tau$, if it is
the complement of an open set (i.e., a member of $\tau$) relative to the space of $\tau$.
For this and several other concepts, we use postfix notation to suggest informal
notations like ``$\tau-$closed''.
%%%%
%%%%

=SML
declare_postfix(400, "Closed");
ⓈHOLCONST
│ ⦏$Closed⦎ : 'a SET SET → 'a SET SET
├──────
│ ∀τ⦁ τ Closed = {A | ∃B⦁B ∈ τ ∧ A = Space⋎T τ \ B}
■
=TEX
Note that in the above definition and in those that follow, we do no stipulate that $\tau$ actually be a topology.
We will agree, however, in stating theorems, to make that an assumption whenever necessary (which is nearly always in theorems of any interest).

The theorems begin with some preliminary lemmas about enumerated sets, finite sets and maxima and minima that belong elsewhere eventually.

\ThmsII{%
=GFT
enum_set_⊆_thm
⋃_enum_set_clauses
⋂_enum_set_clauses
=TEX
}{%
=GFT
finite_image_thm
⊆_size_thm
=TEX
}

Now comes a batch of useful basic facts about open and closed sets: the empty set and the space of a topology are both open and both closed; a set is open iff it contains an open neighbourhood of each of its points; a set is closed iff its complement contains an open neighbourhood of each of its points; any member of an open set is a member of the space (a technical convenience in later proofs); binary unions and, more generally, arbitrary unions of open sets are open; binary intersections and, more generally, finite intersections of open sets are open.

\ThmsII{%
=GFT
empty_open_thm
space_t_open_thm
empty_closed_thm
space_t_closed_thm
open_open_neighbourhood_thm
closed_open_neighbourhood_thm
=TEX
}{%
=GFT
∈_space_t_thm
∪_open_thm
⋃_open_thm
∩_open_thm
finite_⋂_open_thm
=TEX
}
\subsection{New Topologies from Old: Subspace and Product Topologies}
=TEX
We borrow the Z symbol for range restriction (decorated with a subscript
to avoid overloading) for the operator that forms the
subspace of a topological space defined by some subset of the universe of its points.
If that subset contains points outside the carrier set of the topological space they
are ignored.
A set is open with respect to the subspace topology defined by a subset $X$ of the space of the topology iff it is the intersection of an open set with $X$.
%%%%
%%%%

=SML
declare_infix(280, "◁⋎T");
ⓈHOLCONST
│ ⦏$◁⋎T⦎ : 'a SET → 'a SET SET → 'a SET SET
├──────
│ ∀X τ⦁ 	(X ◁⋎T τ)
│ =	{A | ∃B⦁ B ∈ τ ∧ A = B ∩ X}
■

We now give basic facts about the subspace topology induced by a subset of the space of a topology: it is a topology; its space is the subset; if the subset is the space of the topology, the subspace topology and the original are the same.

\ThmsIII{%
=GFT
subspace_topology_thm
=TEX
}{%
=GFT
subspace_topology_space_t_thm
=TEX
}{%
=GFT
trivial_subspace_topology_thm
=TEX
}

=TEX
The definition of the (binary) product topology is the usual one (which amounts to saying that the sets of the form $A \times B$ where $A$ and $B$ are open in the factors of the product provide a basis for the product topology).
%%%%
%%%%

=SML
declare_infix(290, "×⋎T");
=TEX
ⓈHOLCONST
│ ⦏$×⋎T⦎ : 'a SET SET → 'b SET SET → ('a × 'b) SET SET
├──────
│ ∀σ τ⦁	(σ ×⋎T τ) = {C | ∀ x y⦁ (x, y) ∈ C
│		⇒ ∃A B⦁ A ∈ σ ∧ B ∈ τ ∧ x ∈ A ∧ y ∈ B ∧ (A × B) ⊆ C}
■

The product topology is indeed a product topology and the space of the product topology is the product of the spaces of the factors:

\ThmsII{%
=GFT
product_topology_thm
=TEX
}{%
=GFT
product_topology_space_t_thm
=TEX
}

The trivial topology on a 1-point type is useful.
ⓈHOLCONST
│ ⦏$1⋎T⦎ : ONE SET SET
├──────
│ 1⋎T = {{}; {One}}
■

\ThmsII{%
=GFT
unit_topology_thm
=TEX
}{%
=GFT
unit_topology_space_t_thm
=TEX
}

Now we define the $n$-th power topology for finite $n$:
if the space of $τ$ is $X$
=INLINEFT
Π⋎T n τ
=TEX
\ is the usual topology on $X^n$.
ⓈHOLCONST
│ ⦏$Π⋎T⦎ : ℕ → 'a SET SET → 'a LIST SET SET 
├──────
│ ∀τ n⦁ 	Π⋎T 0 τ = { {}; {[]} }
│ ∧		(Π⋎T (n+1) τ) = {C | ¬[] ∈ C ∧ ∀ x v⦁ Cons x v ∈ C ⇒
│				∃A B⦁ A ∈ τ ∧ B ∈ Π⋎T n τ ∧ x ∈ A ∧ v ∈ B ∧
│					∀y w⦁y ∈ A ∧ w ∈ B ⇒ Cons y w ∈ C}
■


Apart from the easy lemma
=INLINEFT
=TEX
\ which says that the lists in
=INLINEFT
Π⋎T n τ
=TEX
\ are all of length $n$ and the fact that the power topology is a topology, we defer proofs about the power topology until we have defined homeomorphisms.

\ThmsII{%
=GFT
power_topology_length_thm
=TEX
}{%
=GFT
power_topology_thm
=TEX
}


\subsection{Continuity}

There are some issues about the precise formalisation of continuity.
The interesting part is completely standard: a function is continuous
iff the inverse images of open sets are open sets. Clearly, there are
two topologies here: one for the domain of the function and one for its
range.
It is technically convenient to work with functions that are total on the
universe of the type of the domain. In any case, we want to support
something like the usual way of thinking in the calculus
where one doesn't carefully restrict every function to the domain of interest.
E.g., one says things like ``$1/\mbox{sin}\;x$ is continuous from  $(0, \pi/2)$
to the positive real numbers.``.

The upshot is the following definition of a continuous function from
the topological space $\sigma$ to the topological space $\tau$.
The function is required to map the carrier set of $\sigma$ to that of $\tau$.
It may well also map things outside the carrier set of $\sigma$ into that
of $\tau$, and these need to be filtered out when we are testing whether the
inverse image of an open set is open.
%%%%
%%%%

=SML
declare_postfix(400, "Continuous");
ⓈHOLCONST
│ ⦏$Continuous⦎ : ('a SET SET × 'b SET SET) → ('a → 'b) SET
├──────
│ ∀σ τ⦁	(σ, τ) Continuous =
│	{f
│	|	(∀x⦁ x ∈ Space⋎T σ ⇒ f x ∈ Space⋎T τ)
│	∧	(∀A⦁ A ∈ τ ⇒ {x | x ∈ Space⋎T σ ∧ f x ∈ A} ∈ σ)}
■

We now give some principles for recognising continuous functions.
First of all a function is continuous iff the inverse image of each closed set is closed.
The restriction of a continuous function to a subspace is continuous.
The following are all continuous: constant functions, identity functions, compositions of continuous functions, the projections of a product onto its factors, the pointwise product of two continuous functions with common domain, the natural injections of a factor of a product into the product, the inclusion of the diagonal into the product of a topological space with itself,
a function whose domain or range is the unit topological space,
and, finally, a function defined by cases under suitable hypotheses.
The last-mentioned principle says that, given two continuous functions, $f$ and $g$, on the same topological space and a subset, $X$, of their domain, the function that agrees with $f$ on $X$ and with $g$ elsewhere is continuous provided $f$ and $g$ agree on each point which lies both in the closure of $X$ and in the closure of its complement.

\ThmsII{%
=GFT
continuous_closed_thm
subspace_continuous_thm
const_continuous_thm
id_continuous_thm
comp_continuous_thm
left_proj_continuous_thm
right_proj_continuous_thm
product_continuous_thm
product_continuous_⇔_thm
=TEX
}{%
=GFT
left_product_inj_continuous_thm
right_product_inj_continuous_thm
domain_unit_topology_continuous_thm
range_unit_topology_continuous_thm
diag_inj_continuous_thm
cond_continuous_thm
=TEX
}


=TEX
\subsection{Hausforff Separation Condition}


Now we define the Hausdorff separation condition.
A topology is Hausdorff iff  any two distinct elements possess disjoint open neighbourhoods.
%%%%
%%%%

=SML
ⓈHOLCONST
│ ⦏Hausdorff⦎ : 'a SET SET SET
├──────
│ 	Hausdorff =
│	{τ | ∀x y⦁ x ∈ Space⋎T τ ∧ y ∈ Space⋎T τ ∧ ¬x = y
│	⇒	∃A B⦁A ∈ τ ∧ B ∈ τ ∧ x ∈ A ∧ y ∈ B ∧ A ∩ B = {}}
■

A subspace of a Hausdorff space is Hausdorff as is the product of two Hausdorff spaces:

\ThmsII{%
=GFT
subspace_topology_hausdorff_thm
=TEX
}{%
=GFT
product_topology_hausdorff_thm
=TEX
}

=TEX
\subsection{Compactness}

The definition of compactness is the standard one (a topology is compact iff every open covering has a finite subcovering), together with the explicit
requirement that the compact set be a subset of the space of the topology in question.
%%%%
%%%%

=SML
declare_postfix(400, "Compact");
ⓈHOLCONST
│ ⦏$Compact⦎ : 'a SET SET → 'a SET SET
├──────
│ ∀τ⦁ τ Compact =
│	{A
│	 |	A ⊆ Space⋎T τ
│	∧	∀V⦁ V ⊆ τ ∧ A ⊆ ⋃ V ⇒ ∃W⦁ W ⊆ V ∧ W ∈ Finite ∧ A ⊆ ⋃ W}
■

Compactness is a topological property, i.e., compactness of a set depends only on the topology induced on the set and not on how the set is embedded in the containing topological space;
continuous functions map compact sets to compact sets; the union of two compact sets is again compact; a compact subset of a Hausdorff space is closed.
The final result is preceded by a simple lemma about separating a point from the union of a finite set of sets.

\ThmsII{%
=GFT
compact_topological_thm
image_compact_thm
∪_compact_thm
=TEX
}{%
=GFT
compact_closed_lemma
compact_closed_thm
=TEX
}

Now we show that the product of two compact sets is compact.
This is the finite case of Tychonov's theorem.
The proof in the finite case is much simpler than the general case.
Moreover the general case is probably best stated in terms of a topology on a function space and we do not wish to consider such topologies yet.
We sneak up on the proof in three steps: the first two are of general use: {\em compact\_basis\_thm} says that given a basis for a topology, to check compactness of a set one only needs to consider coverings by basic open sets and {\em compact\_basis\_product\_topology\_thm} is the special case of this where the topology is the product topology and the basis is the basis that defines the product topology.
{\em compact\_product\_lemma} is a somewhat ad hoc lemma that is needed in the proof of the main theorem and might be of use elsewhere.

\ThmsII{%
=GFT
compact_basis_thm
compact_basis_product_topology_thm
=TEX
}{%
=GFT
compact_product_lemma
product_compact_thm
=TEX
}

Finally, for use in producing Lebesgue numbers of coverings of compact subsets of metric spaces, we prove that compact sets are sequentially compact (every countable subset has a limit point).
We precede the proof by a lemma saying that if a (countably infinite) sequence ranges over the union of a finite family of sets, then some member of the family is visited infinitely often.

\ThmsII{%
=GFT
compact_sequentially_compact_lemma
=TEX
}{%
=GFT
compact_sequentially_compact_thm
=TEX
}

\subsection{Connectedness}

=TEX
Similarly, the definition of connectedness is the standard one (a topology is connected if its space cannot be written as the union of two disjoint open sets), again together with the explicit
requirement that the connected set be a subset of the carrier set of the topology in question.
%%%%
%%%%

=SML
declare_postfix(400, "Connected");
ⓈHOLCONST
│ ⦏$Connected⦎ : 'a SET SET → 'a SET SET
├──────
│ ∀τ⦁ τ Connected =
│	{A | A ⊆ Space⋎T τ
│	∧ ∀B C⦁ B ∈ τ ∧ C ∈ τ ∧ A ⊆ B ∪ C ∧ A ∩ B ∩ C = {} ⇒ (A ⊆ B ∨ A ⊆ C)}
■

Connectedness is a topological property\footnote{%
The use of
=INLINEFT
A ∩ B ∩ C = {}
=TEX
\ rather than
=INLINEFT
B ∩ C = {}
=TEX
\ in the definition is perhaps surprising, but connectedness would not be a topological property with the latter formulation.
To see this, consider a space $X$ with three points $x$, $y$ and $z$, topologised so that $O$ is open iff $O = \{\}$ or $z \in O$. Then $x$ and $y$ cannot be separated by disjoint open sets in $X$, but $\{x, y\}$ is not connected under the subspace topology.}%
. a set is connected iff it cannot be separated by two closed sets;
a set is connected iff any two of its points are contained in a connected subset of the set (which doesn't sound very useful, but is, so much so that we present it both as a conditional rewrite rule and in a form suitable for back-chaining);

\ThmsII{%
=GFT
connected_topological_thm
connected_closed_thm
=TEX
}{%
=GFT
connected_pointwise_thm
connected_pointwise_bc_thm
=TEX
}

The empty set is connected as is any singleton set; continuous functions map connected sets to connected sets;
the union of two non-disjoint connected sets is connected as is the product of any two connected sets.
If the union of two non-empty open (or closed) sets is connected the two sets cannot be disjoint.

\ThmsIII{%
=GFT
empty_connected_thm
singleton_connected_thm
image_connected_thm
=TEX
}{%
=GFT
∪_connected_thm
product_connected_thm
=TEX
}{%
=GFT
∪_open_connected_thm
∪_closed_connected_thm
=TEX
}

Results of the following sort capture common ways of thinking about spaces such as geometric simplicial complexes or CW complexes constructed by gluing together connected pieces:

\begin{itemize}
\item
the union of three connected sets is connected if they can be listed, so that each member meets the next member in the list;
\item
if a connected set is covered by a set of connected sets, then the union of the covering sets is itself connected;
\item
if the union of two connected sets is not connected, then the two sets can be separated (by two open sets, which may not be disjoint in general, but are each disjoint from the union);
\item
if a connected set can be separated from each of a finite family of connected sets, then it can be separated from the union of the family;
\item
given a finite family of non-empty connected sets $U$ and a connected set $B$ such that $B$ is connected as is the union of $B$ and the sets in $U$, if $B$ does not contain every set in $U$, then there is some set $A$ in $U$ such that the union of $A$ and $B$ is connected;
\item
given a finite family of non-empty connected sets $U$ and a member $A$ of $U$, one can begin with $A$ and deal out sets from $U$ such that at each stage the union of the sets that have been dealt is connected, such that each set dealt adds to this union whenever that is possible, and such that eventually the union of the sets that have been dealt is equal to the union of all the sets in $U$;
\item
given a finite family of non-empty connected sets $U$ and a member $A$ of $U$, either $A$ contains the union of all the sets in $U$, or there is a $B$ in $U$ not equal to $A$ and such that the union of the sets in $U$ other than $B$ is connected and does not contain $B$.
\end{itemize}


\ThmsII{%
=GFT
∪_∪_connected_thm
cover_connected_thm
separation_thm
finite_separation_thm
=TEX
}{%
=GFT
connected_extension_thm
connected_chain_thm
connected_step_thm
=TEX
}

=TEX
\subsection{Homeomorphisms}

A homeomorphism is a continuous mapping with a continuous two-sided inverse:
%%%%
%%%%

=SML
declare_postfix(400, "Homeomorphism");
=TEX
ⓈHOLCONST
│ ⦏$Homeomorphism⦎ : ('a SET SET × 'b SET SET) → ('a → 'b) SET
├──────
│ ∀σ τ⦁	(σ, τ) Homeomorphism =
│	{f
│	|	f ∈ (σ, τ) Continuous
│	∧	∃g⦁ 	g ∈ (τ, σ) Continuous
│		∧	(∀x⦁x ∈ Space⋎T σ ⇒ g(f x) = x)
│		∧	(∀y⦁y ∈ Space⋎T τ ⇒ f(g y) = y)}
■

The identity function is a homeomorphism as is the composite of two homeomorphisms, the product of a pair of homeomorphisms,
the natural mapping from a space and its product with a one-point space
and the function on product that interchanges the factors;
a homeomorphism is an open mapping (i.e., it sends open sets to open sets) and is also one-to-one; a function is a homeomorphism iff it is a one-to-one, onto, continuous open mapping.
Finally, a useful principle for recognising homeomorphisms obtained by restricting continuous functions defined on compact Hausdorff spaces.

\ThmsII{%
=GFT
id_homeomorphism_thm
comp_homeomorphism_thm
product_homeomorphism_thm
product_unit_homeomorphism_thm
swap_homeomorphism_thm
=TEX
}{%
=GFT
homeomorphism_open_mapping_thm
homeomorphism_one_one_thm
homeomorphism_onto_thm
homeomorphism_one_one_open_mapping_thm
⊆_compact_homeomorphism_thm
=TEX
}

The useful principle is this:
{\em Let $C$ and $X$ be Hausdorff spaces with $C$ compact and
let $f$ be a continuous function from $C$ to $X$.
If $B \subseteq C$
is such that for every $y \in f(B)$ there is a unique $x$ in $C$ such that $f(x) = y$, then $f$ restricts to a homeomorphism between $B$ and $f(B)$.}
To see this, note that it is enough to prove that the restriction of $f$ to $B$ is a closed mapping, since evidently $f$ is one-one and continuous on $B$.
Given a closed subset $A$ of $B$, we have $A = B \cap D$ where $D$ is some closed and hence compact subset of $C$.
By assumption $f(D \backslash B)$ is disjoint from $f(B)$, which implies that
$f(D \cap B) = f(D) \cap f(B)$.
Since $D$ is compact, so also is $f(D)$, whence $f(D)$ is closed.
Thus $f(A) = f(D) \cap f(B)$ is a closed subset of $f(B)$.


\subsection{Interior, Boundary and Closure Operators}
Our definitions of the interior, boundary and Closure operators are standard, but
as we have to be explicit about the ambient topology, we take them to be
infix operators, reflecting usages like ``the $\tau$-interior of $A$'' that one might use when working with several different topologies on the same set.
=SML
declare_infix(400, "Interior");
declare_infix(400, "Boundary");
declare_infix(400, "Closure");
=TEX
The $\tau$-interior of $A$ comprises the points that lie in $\tau$-open subsets of $A$; the $\tau$-boundary comprises the points (of the space) all of whose open neighbourhoods meet both $A$ and its complement; the $\tau$-closure of $A$ is the smallest $\tau$-closed set containing (the points of the space belonging to) $A$.
ⓈHOLCONST
│ ⦏$Interior⦎ ⦏$Boundary⦎ ⦏$Closure⦎: 'a SET SET → 'a SET → 'a SET
├──────
│ ∀τ A⦁
│	τ Interior A = {x | ∃B⦁ B ∈ τ ∧ x ∈ B ∧ B ⊆ A}
│ ∧ 	τ Boundary A =
│	{x | x ∈ Space⋎T τ ∧ ∀B⦁ B ∈ τ ∧ x ∈ B ⇒ ¬B ∩ A = {} ∧ ¬B \ A = {}}
│ ∧ 	τ Closure A = ⋂{B | B ∈ τ Closed ∧ A ∩ Space⋎T τ ⊆ B}
■
The interior and boundary of a set are subsets of the ambient space and the interior is a subset of the set; the boundary of a set is the complement of the union of its interior and the complement of its interior; the interior of the
product of two sets is the product of their interiors; a set is open iff
it is disjoint from its boundary and closed iff it contains its boundary;
the interior of a set is the union of its open subsets; the
closure of a set is the complement of the interior of its complement.

\ThmsII{%
=GFT
interior_boundary_⊆_space_t_thm
interior_⊆_thm
boundary_interior_thm
interior_×_thm
=TEX
}{%
=GFT
open_⇔_disjoint_boundary_thm
closed_⇔_boundary_⊆_thm
interior_⋃_thm
closure_interior_complement_thm
=TEX
}

=TEX
\subsection{The discrete topology}
A topology is discrete if any subset of its space is open.
ⓈHOLCONST
│ ⦏$Discrete⋎T⦎ : 'a SET SET SET
├──────
│ Discrete⋎T = {τ | ∀A⦁ A ⊆ Space⋎T τ ⇒ A ∈ τ}
■
=TEX
We prove that continuity is trivial for mappings on a space with
the discrete topology, that a topology is discrete iff the singletons
are open and that a mapping from a non-empty connected space
to a discrete space has a singleton range.
\ThmsI{%
=GFT
discrete_t_continuous_thm
open_singletons_discrete_thm
connected_continuous_discrete_thm
=TEX
}

\subsection{Covering Projections}

Our definition of covering projection is completely standard: a continuous function is a covering projection if every point in its range has a neighbourhood $C$ whose inverse image is a disjoint union of open sets each of which is mapped homeomorphically onto $C$.

=SML
declare_postfix(400, "CoveringProjection");
=TEX
ⓈHOLCONST
│ ⦏$CoveringProjection⦎ : ('a SET SET × 'b SET SET) → ('a → 'b) SET
├──────
│ ∀σ τ⦁	(σ, τ) CoveringProjection =
│	{p
│	|	p ∈ (σ, τ) Continuous
│	∧	∀y⦁ 	y ∈ Space⋎T τ
│		⇒	∃C⦁	y ∈ C ∧ C ∈ τ ∧
│			∃U⦁	U ⊆ σ
│			∧	(∀x⦁ x ∈ Space⋎T σ ∧ p x ∈ C
│					⇒ ∃A⦁ x ∈ A ∧ A ∈ U)
│			∧	(∀A B⦁ A ∈ U ∧ B ∈ U ∧ ¬A ∩ B = {} ⇒ A = B)
│			∧	(∀A⦁ A ∈ U ⇒ p ∈ (A ◁⋎T σ, C ◁⋎T τ) Homeomorphism)}
■

=TEX
We define the unique lifting property of a function $p$ from a space $\sigma$ to a space $\tau$
for functions from a space $\rho$. 
ⓈHOLCONST
│ ⦏UniqueLiftingProperty⦎ : ('a SET SET × (('b → 'c) × 'b SET SET × 'c SET SET)) SET
├──────
│ ∀ρ σ τ p⦁
│	(ρ, (p, σ, τ)) ∈ UniqueLiftingProperty ⇔
│		∀f g : 'a → 'b; a : 'a⦁
│			f ∈ (ρ, σ) Continuous
│		∧	g ∈ (ρ, σ) Continuous
│		∧	(∀x⦁ x ∈ Space⋎T ρ ⇒ p(f x) = p(g x))
│		∧	a ∈ Space⋎T ρ
│		∧	g a = f a
│		⇒	∀x⦁ x ∈ Space⋎T ρ ⇒ g x = f x
■

We prove two lemmas that fit together to give the unique lifting property for continuous functions from a connected space into the base space of a covering projection.

\ThmsII{%
=GFT
unique_lifting_lemma1
unique_lifting_lemma2
=TEX
}{%
=GFT
unique_lifting_thm
unique_lifting_bc_thm
=TEX
}

\subsection{Protocomplexes}

In a later version of this document we intend to define the notion of a CW complex.
To support this, it is convenient to define some purely topological notions.
A {\em protocomplex} will comprise a set of pairs representing a partial
function from certain closed subsets of a topological space $X$ to the natural
numbers. The sets in the domain of this function will be referred to
as {\em cells} and the natural number associated with a cell will be called
its {\em dimension}. Informally, we call a cell of dimension $m$ an $m$-cell.
The union of all the cells is the {\em space} of the protocomplex:

ⓈHOLCONST
│ ⦏Space⋎K⦎ : ('a SET × ℕ) SET → 'a SET
├──────
│ ∀C⦁ Space⋎K C = ⋃{c | ∃m⦁ (c, m) ∈ C}
■
(We distinguish the name with a subscript $K$ as in the German {\em Komplex}, since we use $C$ elsewhere for the complex numbers.)

We define the $n$-skeleton of $C$ to be the union of all cells of dimension
at most $n$.
=SML
declare_infix(400, "Skeleton");
=TEX

ⓈHOLCONST
│ ⦏$Skeleton⦎ : ℕ → ('a SET × ℕ) SET → 'a SET
├──────
│ ∀n C⦁ n Skeleton C = ⋃{c | ∃m⦁m ≤ n ∧ (c, m) ∈ C}
■

Our requirements on a protocomplex are as follows:
{\em(i)} each cell is a closed set,
{\em(ii)} for every $x$ in $X$ there is a unique $m$-cell $c$
such that $x$ lies in the interior of $c$ with respect to
the relative topology on the $m$-skeleton of $C$,
{\em(iii)} a subset $A$ of $X$ is closed if $A \cap c$ is closed
for every cell $c$,
and {\em(iv)} each $m$-cell meets only finitely many cells of lower dimension.
=TEX
ⓈHOLCONST
│ ⦏Protocomplex⦎ : 'a SET SET → ('a SET × ℕ) SET SET
├──────
│ ∀C τ⦁	C ∈ Protocomplex τ ⇔
│	(∀c m⦁ (c, m) ∈ C ⇒ c ∈ τ Closed)
│ ∧	(∀x⦁ x ∈ Space⋎K C ⇒
│		∃⋎1 (c, m)⦁ (c, m) ∈ C ∧ x ∈ ((m Skeleton C) ◁⋎T τ) Interior c)
│ ∧	(∀A⦁ A ⊆ Space⋎K C ∧ (∀c m⦁ (c, m) ∈ C ⇒ A ∩ c ∈ τ Closed) ⇒ A ∈ τ Closed)
│ ∧	(∀c m⦁ (c, m) ∈ C ⇒ {(d, n) | (d, n) ∈ C ∧ n < m ∧ ¬c ∩ d = {}} ∈ Finite)
■

=TEX
\section{METRIC SPACES --- DEFINITIONS}
In the following, we bring in the theory of analysis from \cite{LEMMA1/HOL/WRK066}, although we could make do just with the real numbers
to start with.
=SML
force_delete_theory "metric_spaces" handle Fail _ => ();
open_theory "topology";
new_theory "metric_spaces";
new_parent"analysis";
new_parent"trees";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=TEX
Our treatment of metric spaces is very minimal.
The main fact we are interested in
will be that coverings of compact subsets of metric spaces have a Lebesgue number.
The definitions involved are the concept of a metric:
%%%%
%%%%
ⓈHOLCONST
│ ⦏Metric⦎ : ('a × 'a → ℝ) SET
├──────
│ 	Metric =
│	{	D
│	|	(∀x y⦁ ℕℝ 0 ≤ D(x, y))
│	∧	(∀x y⦁ D(x, y) = ℕℝ 0 ⇔ x = y)
│	∧	(∀x y⦁ D(x, y) = D (y, x))
│	∧	(∀x y z⦁ D(x, z) ≤ D (x, y) + D(y, z))}
■
=TEX
\ldots and the concept of the metric topology, which we write as a postfix since otherwise the notation for concepts such as ``compact with respect to the metric topology induced by $D$'' look rather strange.
=SML
declare_postfix(400, "MetricTopology");
ⓈHOLCONST
│ ⦏$MetricTopology⦎ : ('a × 'a → ℝ) → 'a SET SET
├──────
│  ∀D⦁ D MetricTopology = {A | ∀x⦁x ∈ A ⇒ ∃e⦁ 0. < e ∧ (∀y⦁D(x, y) < e ⇒ y ∈ A)}
■
We prove some basic facts about the metric topology and about the sum metric on a product of metric spaces.

\ThmsII{%
=GFT
metric_topology_thm
space_t_metric_topology_thm
open_ball_open_thm
open_ball_neighbourhood_thm
=TEX
}{%
=GFT
metric_topology_hausdorff_thm
product_metric_thm
product_metric_topology_thm
=TEX
}

We prove the existence of Lebesgue numbers and that if $X$ is a compact subset of an open space $A$ in
a metric space, then for small $\epsilon >0$, $A$ contains the ball $B(x, \epsilon)$ for every $x \in X$.

\ThmsII{%
=GFT
lebesgue_number_thm
=TEX
}{%
=GFT
collar_thm
=TEX
}

We also define an induced metric on the set of lists of elements of a metric space. We use this, for example, to define $n$-dimensional euclidean space. Getting a good definition
is a little delicate: given a (non-empty) metric space
$A$ with metric $d$, fix an arbitrary element $a \in A$ and let
$A^*$ be the set of countably infinite sequences in $A$ that
take the constant value $a$ for all but finitely many
indices. $A^*$ becomes a metric space under the metric
$d^*$ defined by $d^*(s, t) = \sum_{i}d(s_i, t_i)$.
If we map lists to infinite sequences by padding with $a$,
this induces a pseudo-metric on the space $A^L$ of lists
of elements of $A$.
To get a metric, we take $d^L(v, w) = |\#v - \#w| + d^*(vaaa\ldots, waaa\ldots)$, where $\#v$ is the length of the list $v$.

ⓈHOLCONST
│ ⦏ListMetric⦎ : ('a × 'a → ℝ) → ('a LIST × 'a LIST) → ℝ
├──────
│ ∀D x v y w⦁
│		ListMetric D ([], []) = 0.
│ ∧		ListMetric D (Cons x v, []) = 1. + D(x, Arbitrary) + ListMetric D (v, [])
│ ∧		ListMetric D ([], Cons y w) = 1. + D(Arbitrary, y) + ListMetric D ([], w)
│ ∧		ListMetric D (Cons x v, Cons y w) = D(x, y) + ListMetric D (v, w)
■

\ThmsII{%
=GFT
list_pseudo_metric_lemma1
list_pseudo_metric_lemma2
list_metric_nonneg_thm
=TEX
}{%
=GFT
list_metric_sym_thm
list_metric_metric_thm
=TEX
}

%%%%
%%%%
=TEX
%%%%
%%%%
=TEX
\section{THE REAL LINE AND THE PLANE --- DEFINITIONS }
=SML
force_delete_theory "topology_ℝ" handle Fail _ => ();
open_theory "metric_spaces";
new_theory "topology_ℝ";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=TEX
%%%%
%%%%
We will make much use of the standard topology on the real line and so we define a short alias for it:
=SML
declare_alias("O⋎R", ⌜Open⋎R⌝);
=TEX
%%%%
%%%%

We define the standard metric on the real line:
ⓈHOLCONST
│ ⦏D⋎R⦎ : ℝ × ℝ → ℝ
├──────
│  ∀x y⦁ D⋎R(x, y) = Abs(y - x)
■
In the plane, as we are primarily interested in topological properties
it is simple and convenient to use the $L_1$-norm.
ⓈHOLCONST
│ ⦏D⋎R2⦎ : (ℝ × ℝ) × (ℝ × ℝ) → ℝ
├──────
│  ∀x1 y1 x2 y2⦁ D⋎R2 ((x1, y1), (x2, y2)) = Abs(x2 - x1) + Abs(y2 - y1)
■
=TEX
%%%%
%%%%
%%%%
%%%%
\ThmsII{%
=GFT
d_ℝ_2_def1
open_ℝ_topology_thm
space_t_ℝ_thm
closed_closed_ℝ_thm
compact_compact_ℝ_thm
continuous_cts_at_ℝ_thm
universe_ℝ_connected_thm
closed_interval_connected_thm
subspace_ℝ_thm
connected_ℝ_thm
ℝ_×_ℝ_topology_thm
continuous_ℝ_×_ℝ_ℝ_thm
continuous_ℝ_×_ℝ_ℝ_thm1
continuous_ℝ_×_ℝ_ℝ_thm3
continuous_ℝ_×_ℝ_ℝ_thm4
=TEX
}{%
=GFT
plus_continuous_ℝ_×_ℝ_thm
times_continuous_ℝ_×_ℝ_thm
cond_continuous_ℝ_thm
d_ℝ_metric_thm
d_ℝ_open_ℝ_thm
d_ℝ_2_metric_thm
d_ℝ_2_open_ℝ_×_open_ℝ_thm
open_ℝ_hausdorff_thm
open_ℝ_×_open_ℝ_hausdorff_thm
ℝ_lebesgue_number_thm
closed_interval_lebesgue_number_thm
product_interval_cover_thm
dissect_unit_interval_thm
product_interval_cover_thm
=TEX
}
We honour euclidean $n$-space with the name {\em Space} with no further decoration. For us, this is a family of topologies indexed by the natural
numbers. The underlying spaces of the topologies comprise lists of real numbers.
=SML
declare_postfix(400, "Space");

=TEX
ⓈHOLCONST
│ ⦏$Space⦎ : ℕ → ℝ LIST SET SET
├──────
│  ∀n⦁ n Space = {v | #v = n} ◁⋎T ListMetric D⋎R MetricTopology
■
The $n$-cube is the subpace of $n$-space comprising vectors with coordinates
in the closed interval $[0, 1]$.
=SML
declare_postfix(400, "Cube");

=TEX
ⓈHOLCONST
│ ⦏$Cube⦎ : ℕ → ℝ LIST SET SET
├──────
│  ∀n⦁ n Cube = {v | Elems v ⊆ ClosedInterval 0. 1.} ◁⋎T n Space
■
The open $n$-cube is the subpace of $n$-space comprising vectors with coordinates
in the open interval $(0, 1)$.
=SML
declare_postfix(400, "OpenCube");

=TEX
ⓈHOLCONST
│ ⦏$OpenCube⦎ : ℕ → ℝ LIST SET SET
├──────
│  ∀n⦁ n OpenCube = {v | Elems v ⊆ OpenInterval 0. 1.} ◁⋎T n Space
■
The (topological) $n$-sphere is the subpace of the $n$-cube comprising
vectors with at least one coordinate
in the set $\{0, 1\}$.
=SML
declare_postfix(400, "Sphere");

=TEX
ⓈHOLCONST
│ ⦏$Sphere⦎ : ℕ → ℝ LIST SET SET
├──────
│  ∀n⦁ n Sphere = {v | ¬Elems v ∩ {0.; 1.} = {}} ◁⋎T n Cube
■

=TEX

\section{PATHS AND HOMOTOPY--- DEFINITIONS}
=SML
force_delete_theory "homotopy" handle Fail _ => ();
open_theory "topology_ℝ";
new_theory "homotopy";
new_parent "groups";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=TEX
For convenience, we represent paths in a space as continuous
functions on the whole real line.
For the time being we do not define a topology on the path space (this was historically a slightly thorny topic in the literature and the ``modern'' solution via $k$-ification seems out of place at this stage).
%%%%
%%%%

=SML
ⓈHOLCONST
│ ⦏Paths⦎ : 'a SET SET → (ℝ → 'a) SET
├──────
│ ∀τ⦁	Paths τ =
│	{	f
│	|	f ∈ (O⋎R, τ) Continuous
│	∧	(∀x⦁ x ≤ 0. ⇒ f x = f 0.)
│	∧	(∀x⦁ 1. ≤ x ⇒ f x = f 1.)}
■

=TEX
We now consider
path connectedness. Here is the definition of a path connected set.
%%%%
%%%%

=SML
declare_postfix(400, "PathConnected");
ⓈHOLCONST
│ ⦏$PathConnected⦎ : 'a SET SET → 'a SET SET
├──────
│ ∀τ⦁ τ PathConnected =
│	{	A
│	|	A ⊆ Space⋎T τ
│	∧	∀x y⦁ x ∈ A ∧ y ∈ A
│	⇒	∃f⦁ 	f ∈ Paths τ
│		∧	(∀ t⦁ f t ∈ A)
│		∧	f 0. = x
│		∧	f 1. = y}
■
=SML
ⓈHOLCONST
│ ⦏LocallyPathConnected⦎ : 'a SET SET SET
├──────
│ ∀τ⦁	τ ∈ LocallyPathConnected
│ ⇔	∀x A⦁x ∈ A ∧ A ∈ τ ⇒ ∃B⦁B ∈ τ ∧ x ∈ B ∧ B ⊆ A ∧ B ∈ τ PathConnected
■
=TEX
=TEX
%%%%
%%%%
%%%%
%%%%
=TEX
Continuing along the way towards the elements of algebraic topology, we now consider
the notion of a homotopy. Here and elsewhere it is convenient to model functions
continuous on the unit interval by functions continuous on the whole line.
This is not problematic since any function continuous on the unit interval
can be extended to be continuous everywhere.

Our homotopies are relative to a set $X$.
%%%%
%%%%

=SML
declare_postfix(400, "Homotopy");
ⓈHOLCONST
│ ⦏$Homotopy⦎ : 'a SET SET × 'a SET × 'b SET SET → ('a × ℝ → 'b) SET
├──────
│ ∀σ X τ⦁ (σ, X, τ) Homotopy =
│	{H | H ∈ ((σ ×⋎T O⋎R), τ) Continuous ∧ ∀x s t⦁x ∈ X ⇒ H(x, s) = H(x, t)}
■

%%%%
%%%%

=SML
declare_postfix(400, "Homotopic");
ⓈHOLCONST
│ ⦏$Homotopic⦎ : 'a SET SET × 'a SET × 'b SET SET → ('a → 'b) → ('a → 'b) → BOOL
├──────
│ ∀σ X τ f g⦁
│	((σ, X, τ) Homotopic) f g ⇔
│		∃H⦁ H ∈ (σ, X, τ) Homotopy
│	∧	(∀x⦁ H(x, 0.) = f x) ∧ (∀x⦁ H(x, 1.) = g x)
■
=TEX
\subsection{The Path Groupoid}
=TEX
Now we define addition of paths:
=SML
declare_infix(300, "+⋎P");
ⓈHOLCONST
│ ⦏$+⋎P⦎ : (ℝ → 'a) → (ℝ → 'a) → (ℝ → 'a)
├──────
│ ∀f g⦁ f +⋎P g = (λt⦁if t ≤ 1/2 then f (2. *t) else g (2. *(t - 1/2)))
■
The identity elements of the path space may be taken to be the constant paths of zero length:
ⓈHOLCONST
│ ⦏0⋎P⦎ : 'a → (ℝ → 'a)
├──────
│ ∀x⦁ 0⋎P x = (λt⦁ x)
■
=TEX
Now we define the inverse of a path:
=SML
ⓈHOLCONST
│ ⦏$~⋎P⦎ : (ℝ → 'a) → (ℝ → 'a)
├──────
│ ∀f⦁ ~⋎P f = (λt⦁ f(1. -  t))
■
It is convenient in later definitions and theorems to have a name for the homotopy relation for paths (namely homotopy with respect to the standard topology on the real line relative to the endpoints
of the unit interval).
ⓈHOLCONST
│ ⦏PathHomotopic⦎ : 'a SET SET → (ℝ → 'a) → (ℝ → 'a) → BOOL
├──────
│ ∀τ⦁ PathHomotopic τ = (O⋎R, {0.; 1.}, τ) Homotopic
■

We prove some basic facts about homotopies and paths.

\ThmsII{%
=GFT
path_connected_connected_thm
product_path_connected_thm
homotopic_refl_thm
homotopic_sym_thm
homotopic_trans_thm
homotopic_equiv_thm
homotopy_⊆_thm
homotopic_⊆_thm
homotopic_comp_left_thm
homotopic_comp_right_thm
homotopic_ℝ_thm
paths_continuous_thm
path_0_path_thm
=TEX
}{%
=GFT
path_plus_path_path_thm
minus_path_path_thm
path_plus_assoc_thm
path_plus_0_thm
path_0_plus_thm
path_plus_minus_thm
path_minus_minus_thm
path_minus_plus_thm
paths_space_t_thm
path_comp_continuous_path_thm
path_from_arc_thm
loop_from_arc_thm
=TEX
}

We prove some facts about path connectedness and local path connectedness.

\ThmsII{%
=GFT
open_connected_path_connected_thm
open_interval_path_connected_thm
=TEX
}{%
=GFT
ℝ_locally_path_connected_thm
product_locally_path_connected_thm
=TEX
}

We define a standard retraction of the real line onto the unit interval.
This is useful for constructing paths (following our conventions) from
arbitrary continuous functions on the real line.

ⓈHOLCONST
│ ⦏IotaI⦎ : ℝ → ℝ
├──────
│ IotaI = (λx⦁ if x ≤ 0. then 0. else if x ≤ 1. then x else 1.)
■

We define the path lifting property for a continuous function $p$ from a space $\sigma$ to a space $\tau$:

ⓈHOLCONST
│ ⦏PathLiftingProperty⦎ :
│	(('a → 'b ) × 'a SET SET × 'b SET SET) SET
├──────
│ ∀ σ τ p⦁
│	(p, σ, τ) ∈ PathLiftingProperty
│ ⇔		∀f y⦁
│			f ∈ Paths τ
│		∧	y ∈ Space⋎T σ
│		∧	p y = f 0.
│		⇒	(∃g⦁
│				g ∈ Paths σ
│			∧ 	g 0. = y
│			∧ 	(∀s⦁ p(g s) = f s))
■

We define the notion of homotopy lifting property for a pair comprising a topological space $\rho$ and a continuous mapping 
$p$ from a topological $\sigma$ to a topological space $\tau$
as follows:

ⓈHOLCONST
│ ⦏HomotopyLiftingProperty⦎ :
│	('a SET SET × ('b → 'c ) × 'b SET SET × 'c SET SET) SET
├──────
│ ∀ρ σ τ p⦁
│	(ρ, (p, σ, τ)) ∈ HomotopyLiftingProperty
│ ⇔		∀f H⦁
│			f ∈ (ρ, σ) Continuous
│		∧	H ∈ (ρ ×⋎T O⋎R, τ) Continuous
│		∧	(∀ x⦁ x ∈ Space⋎T ρ ⇒ H(x, 0.) = p(f x))
│		⇒	(∃L⦁
│				L ∈ (ρ ×⋎T O⋎R, σ) Continuous
│			∧ 	(∀ x⦁ x ∈ Space⋎T ρ ⇒ L(x, 0.) = f x)
│			∧	(∀ x s⦁
│					x ∈ Space⋎T ρ
│				∧	s ∈ ClosedInterval 0. 1.
│				⇒	p(L(x, s)) = H(x, s)))
■


We prove that a covering project has the homotopy lifting property with respect to any space(i.e., it is a fibration) and hence also has the path lifting property.

\ThmsII{%
=GFT
covering_projection_fibration_thm
=TEX
}{%
=GFT
covering_projection_path_lifting_thm
=TEX
}

=TEX
\subsection{The Fundamental Group}
We define a loop in a space $\tau$ with basepoint $x$ to be a path that takes the value $x$ everywhere outside the open interval $(0, 1)$.
ⓈHOLCONST
│ ⦏Loops⦎ : 'a SET SET × 'a → (ℝ → 'a) SET
├──────
│ ∀τ x⦁	Loops (τ, x) = Paths τ ∩ {f | ∀t⦁ t ≤ 0. ∨ 1. ≤ t ⇒ f t = x}
■

The following function maps a representative of an element of the fundamental group to the element
it represents: 

ⓈHOLCONST
│ ⦏FunGrpClass⦎ : 'a SET SET × 'a → (ℝ → 'a) → (ℝ → 'a) SET
├──────
│ ∀τ x f⦁
│	FunGrpClass(τ, x) f = EquivClass (Loops(τ, x), PathHomotopic τ) f
■

The group multiplication in the fundamental group is defined by taking the
path sum of representatives.
ⓈHOLCONST
│ ⦏FunGrpTimes⦎ : 'a SET SET × 'a → (ℝ → 'a) SET → (ℝ → 'a) SET → (ℝ → 'a) SET
├──────
│ ∀τ x p q f g⦁
│	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
│	p ∈ Loops (τ, x) / PathHomotopic τ ∧  q ∈ Loops (τ, x) / PathHomotopic τ ∧
│	f ∈ p ∧ g ∈ q ⇒
│	FunGrpTimes(τ, x) p q = FunGrpClass(τ, x) (f +⋎P g)
■

The unit element in the fundamental group is the constant loop at the basepoint.
ⓈHOLCONST
│ ⦏FunGrpUnit⦎ : 'a SET SET × 'a → (ℝ → 'a) SET 
├──────
│ ∀τ x⦁
│	FunGrpUnit(τ, x) = FunGrpClass(τ, x) (0⋎P x)
■
Then group inverse operation in the fundamental group is defined by taking
the path negative of a representative.
ⓈHOLCONST
│ ⦏FunGrpInverse⦎ : 'a SET SET × 'a → (ℝ → 'a) SET → (ℝ → 'a) SET
├──────
│ ∀τ x p f⦁
│	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧ p ∈ Loops (τ, x) / PathHomotopic τ ∧ f ∈ p ⇒
│	FunGrpInverse(τ, x) p = FunGrpClass(τ, x) (~⋎P f)
■
Putting the four components together gives us the fundamental group.\
ⓈHOLCONST
│ ⦏FunGrp⦎ : 'a SET SET × 'a → (ℝ → 'a) SET GROUP
├──────
│ ∀τ x⦁
│	FunGrp(τ, x) =
│	MkGROUP
│		(Loops (τ, x) / PathHomotopic τ)
│		(FunGrpTimes(τ, x))
│		(FunGrpUnit(τ, x))
│		(FunGrpInverse(τ, x))
■


=TEX
\appendix
{%\HOLindexOff
\include{wrk0671.th}}
{%\HOLindexOff
\include{wrk0672.th}}
{%\HOLindexOff
\include{wrk0673.th}}
{%\HOLindexOff
\include{wrk0674.th}}
=TEX
%%%%
%%%%
\twocolumn[\section*{INDEX}\label{INDEX}]
\addcontentsline{toc}{section}{INDEX}
{\small\printindex}

\end{document}
\onecolumn

\section{ABSTRACT TOPOLOGY --- THEOREMS}
=TEX
%%%%
%%%%
=SML
open_theory "topology";
set_merge_pcs["basic_hol1", "'sets_alg"];
=TEX
\subsection{Lemmas About Finite Sets}
=TEX
%%%%
%%%%

=SML

val ⦏enum_set_⊆_thm⦎ = save_thm ( "enum_set_⊆_thm", (
set_goal([], ⌜
	∀ A B C⦁  (Insert A B) ⊆ C ⇔ A ∈ C ∧ B ⊆ C
⌝);
a(PC_T1 "sets_ext1" rewrite_tac[insert_def]);
a(prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⋃_enum_set_clauses⦎ = save_thm ( "⋃_enum_set_clauses", (
set_goal([], ⌜
	⋃{} = {}
∧	∀ A B⦁  ⋃(Insert A B) = A ∪ (⋃B)
⌝);
a(REPEAT strip_tac THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(PC_T "sets_ext1" strip_tac);
a(rewrite_tac[⋃_def, insert_def, ∪_def]);
a(prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⋂_enum_set_clauses⦎ = save_thm ( "⋂_enum_set_clauses", (
set_goal([], ⌜
	⋂{} = Universe
∧	∀ A B⦁  ⋂(Insert A B) = A ∩ (⋂B)
⌝);
a(REPEAT strip_tac THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(PC_T "sets_ext1" strip_tac);
a(rewrite_tac[⋂_def, insert_def, ∩_def]);
a(prove_tac[]);
pop_thm()
));
val ⦏enum_set_clauses⦎ = list_∧_intro
	[enum_set_⊆_thm,  ⋃_enum_set_clauses, ⋂_enum_set_clauses];


=TEX
%%%%
%%%%

=SML

val ⦏finite_image_thm⦎ = save_thm ( "finite_image_thm", (
set_goal([], ⌜∀ f : 'a → 'b; A : 'a SET⦁
	 A ∈ Finite ⇒ {y | ∃x⦁x ∈ A ∧ y = f x} ∈ Finite
⌝);
a(REPEAT strip_tac);
a(finite_induction_tac ⌜A⌝ THEN1 rewrite_tac[]);
(* *** Goal "1" *** *)
a(LEMMA_T⌜{y:'b|F} = {}⌝ (fn th => rewrite_tac[th, empty_finite_thm])
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜{y|∃ x'⦁ x' ∈ {x} ∪ A ∧ y = f x'} = {f x} ∪ {y|∃ x'⦁ x' ∈ A ∧ y = f x'}⌝
	rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(bc_thm_tac singleton_∪_finite_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊆_size_thm⦎ = save_thm ( "⊆_size_thm", (
set_goal([], ⌜∀a b⦁ a ∈ Finite ∧ b ⊆ a ⇒ #b ≤ #a⌝);
a(REPEAT strip_tac);
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

val ⦏⊆_size_thm1⦎ = save_thm ( "⊆_size_thm1", (
set_goal([],⌜∀a b⦁ a ∈ Finite ∧ b ⊆ a ∧ ¬b = a ⇒ #b < #a⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜a \ b ⊆ a ∧ ¬a \ b = {}⌝ THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(REPEAT strip_tac THEN all_fc_tac[⊆_finite_thm]);
a(LEMMA_T ⌜# (b ∪ (a \ b)) + # (b ∩ (a \ b)) = # b + # (a \ b)⌝ ante_tac THEN1
	(bc_thm_tac size_∪_thm THEN REPEAT strip_tac));
a(LEMMA_T ⌜b ∪ (a \ b) = a ∧ b ∩ (a \ b) = {}⌝ rewrite_thm_tac THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(rewrite_tac[size_empty_thm]);
a(STRIP_T rewrite_thm_tac);
a(lemma_tac ⌜¬ #(a \ b) = 0⌝ THEN_LIST
	[id_tac, PC_T1 "lin_arith" asm_prove_tac[]]);
a(ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[size_0_thm]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏finite_⊆_well_founded_thm⦎ = save_thm ( "finite_⊆_well_founded_thm", (
set_goal([],⌜∀p a⦁
	a ∈ Finite
∧	p a
⇒	∃b⦁
	b ⊆ a
∧	p b
∧	∀c⦁c ⊆ b ∧ p c ⇒ c = b⌝);
a(REPEAT strip_tac);
a(PC_T1 "predicates" lemma_tac ⌜#a ∈ {n | ∃t⦁ t ⊆ a ∧ p t ∧ n = #t}⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(∃_tac⌜a⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(all_fc_tac[min_∈_thm]);
a(∃_tac⌜t⌝ THEN REPEAT strip_tac);
a(contr_tac THEN all_fc_tac[⊆_finite_thm]);
a(all_fc_tac[⊆_size_thm1]);
a(DROP_NTH_ASM_T 9 discard_tac);
a(PC_T1 "predicates" lemma_tac ⌜#c ∈ {n | ∃t⦁ t ⊆ a ∧ p t ∧ n = #t}⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac);
a(∃_tac⌜c⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(all_fc_tac[min_≤_thm]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

\subsection{The Definitions}
=SML
val ⦏topology_def⦎ = get_spec⌜$Topology⌝;
val ⦏space_t_def⦎ = get_spec⌜Space⋎T⌝;
val ⦏closed_def⦎ = get_spec⌜$Closed⌝;
val ⦏continuous_def⦎ = get_spec⌜$Continuous⌝;
val ⦏connected_def⦎ = get_spec⌜$Connected⌝;
val ⦏compact_def⦎ = get_spec⌜$Compact⌝;
val ⦏subspace_topology_def⦎ = get_spec⌜$◁⋎T⌝;
val ⦏product_topology_def⦎ = get_spec⌜$×⋎T⌝;
val ⦏unit_topology_def⦎ = get_spec⌜1⋎T⌝;
val ⦏power_topology_def⦎ = get_spec⌜Π⋎T⌝;
val ⦏hausdorff_def⦎ = get_spec⌜Hausdorff⌝;
val ⦏homeomorphism_def⦎ = get_spec⌜$Homeomorphism⌝;
local
	val thm1 = all_∀_elim (get_spec⌜$Interior⌝);
	val [i_def, b_def, c_def] = strip_∧_rule thm1;
in
	val ⦏interior_def⦎ = all_∀_intro i_def;
	val ⦏boundary_def⦎ = all_∀_intro b_def;
	val ⦏closure_def⦎ = all_∀_intro c_def;
end;
val ⦏discrete_t_def⦎ = get_spec⌜Discrete⋎T⌝;
val ⦏covering_projection_def⦎ = get_spec⌜$CoveringProjection⌝;
val ⦏unique_lifting_property_def⦎ = get_spec⌜UniqueLiftingProperty⌝;
val ⦏space_k_def⦎ = get_spec⌜Space⋎K⌝;
val ⦏skeleton_def⦎ = get_spec⌜$Skeleton⌝;
val ⦏protocomplex_def⦎ = get_spec⌜Protocomplex⌝;
=TEX
\subsection{Elementary Properties of Open and Closed Sets}
%%%%
%%%%

=SML

val ⦏empty_open_thm⦎ = save_thm ( "empty_open_thm", (
set_goal([], ⌜∀τ : 'a SET SET ⦁ τ ∈ Topology ⇒ {} ∈ τ⌝);
a(rewrite_tac[topology_def] THEN REPEAT strip_tac);
a(SPEC_NTH_ASM_T 2 ⌜{}: 'a SET SET⌝ ante_tac);
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜⋃{} = {}⌝]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏space_t_open_thm⦎ = save_thm ( "space_t_open_thm", (
set_goal([], ⌜∀τ : 'a SET SET ⦁ τ ∈ Topology ⇒ Space⋎T τ ∈ τ⌝);
a(rewrite_tac[topology_def, space_t_def] THEN REPEAT strip_tac);
a(SPEC_NTH_ASM_T 2 ⌜τ: 'a SET SET⌝ ante_tac);
a(rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏empty_closed_thm⦎ = save_thm ( "empty_closed_thm", (
set_goal([], ⌜∀τ : 'a SET SET ⦁ τ ∈ Topology ⇒ {} ∈ τ Closed⌝);
a(rewrite_tac[closed_def] THEN REPEAT strip_tac);
a(all_fc_tac[space_t_open_thm]);
a(∃_tac⌜Space⋎T τ⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏space_t_closed_thm⦎ = save_thm ( "space_t_closed_thm", (
set_goal([], ⌜∀τ : 'a SET SET ⦁ τ ∈ Topology ⇒ Space⋎T τ ∈ τ Closed⌝);
a(rewrite_tac[closed_def] THEN REPEAT strip_tac);
a(all_fc_tac[empty_open_thm]);
a(∃_tac⌜{} : 'a SET⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏open_open_neighbourhood_thm⦎ = save_thm ( "open_open_neighbourhood_thm", (
set_goal([], ⌜∀τ A ⦁
	τ ∈ Topology ⇒
	(A ∈ τ ⇔ ∀x⦁x ∈ A ⇒ ∃B⦁ B ∈ τ ∧ x ∈ B ∧ B ⊆ A)⌝);
a(rewrite_tac[topology_def, space_t_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜A⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜A = ⋃{B | B ∈ τ ∧ B ⊆ A}⌝);
(* *** Goal "2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN
	contr_tac THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a(POP_ASM_T once_rewrite_thm_tac THEN DROP_NTH_ASM_T 3 bc_thm_tac);
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏closed_open_neighbourhood_thm⦎ = save_thm ( "closed_open_neighbourhood_thm", (
set_goal([], ⌜∀τ A ⦁
	τ ∈ Topology ⇒
	(	A ∈ τ Closed
	⇔ 	A ⊆ Space⋎T τ
	∧	∀x⦁x ∈ Space⋎T τ  ∧ ¬x ∈ A ⇒ ∃B⦁ B ∈ τ ∧ x ∈ B ∧ B ∩ A = {})⌝);
a(rewrite_tac[closed_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜x ∈ B⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[open_open_neighbourhood_thm]);
a(∃_tac⌜B'⌝ THEN PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(FC_T1 fc_⇔_canon once_rewrite_tac [open_open_neighbourhood_thm]);
a(∃_tac⌜Space⋎T τ \ A⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(all_asm_fc_tac[]);
a(∃_tac⌜B⌝ THEN PC_T1 "sets_ext1" asm_rewrite_tac[]);
a(rewrite_tac[space_t_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "3.1.1" *** *)
a(contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "3.1.2" *** *)
a(REPEAT_N 2 (POP_ASM_T ante_tac) THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "3.2" *** *)
a(LIST_GET_NTH_ASM_T [1, 3] (MAP_EVERY ante_tac)  THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏∈_space_t_thm⦎ = save_thm ( "∈_space_t_thm", (
set_goal([], ⌜∀τ x A ⦁
	x ∈ A ∧ A ∈ τ ⇒ x ∈ Space⋎T τ
⌝);
a(rewrite_tac[space_t_def] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏∈_closed_∈_space_t_thm⦎ = save_thm ( "∈_closed_∈_space_t_thm", (
set_goal([], ⌜∀τ x A ⦁
	x ∈ A ∧ A ∈ τ Closed ⇒ x ∈ Space⋎T τ
⌝);
a(rewrite_tac[space_t_def, closed_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_asm_fc_tac[] THEN contr_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏closed_open_complement_thm⦎ = save_thm ( "closed_open_complement_thm", (
set_goal([], ⌜∀τ A ⦁
	τ ∈ Topology ⇒
	(	A ∈ τ Closed
	⇔ 	A ⊆ Space⋎T τ
	∧	Space⋎T τ \ A ∈ τ)⌝);
a(rewrite_tac[closed_def] THEN REPEAT strip_tac THEN_TRY all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜B ⊆ Space⋎T τ⌝ THEN1
	(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_fc_tac[∈_space_t_thm]));
a(LEMMA_T ⌜Space⋎T τ \ (Space⋎T τ \ B) = B⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜Space⋎T τ \ A⌝ THEN PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏∪_open_thm⦎ = save_thm ( "∪_open_thm", (
set_goal([], ⌜∀τ A B ⦁
	τ ∈ Topology ∧ A ∈ τ ∧ B ∈ τ ⇒ A ∪ B ∈ τ
⌝);
a(rewrite_tac[topology_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(SPEC_NTH_ASM_T 4 ⌜{A; B}⌝ (strip_asm_tac o rewrite_rule[enum_set_clauses]));
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⋃_open_thm⦎ = save_thm ( "⋃_open_thm", (
set_goal([], ⌜∀ τ V⦁
	τ ∈ Topology
∧	V ⊆ τ
⇒	⋃V ∈ τ⌝);
a(rewrite_tac[topology_def] THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏∩_open_thm⦎ = save_thm ( "∩_open_thm", (
set_goal([], ⌜∀τ A B ⦁
	τ ∈ Topology ∧ A ∈ τ ∧ B ∈ τ ⇒ A ∩ B ∈ τ
⌝);
a(rewrite_tac[topology_def] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⋂_open_thm⦎ = save_thm ( "⋂_open_thm", (
set_goal([], ⌜∀ τ V⦁
	τ ∈ Topology
∧	¬V = {}
∧	V ∈ Finite
∧	V ⊆ τ
⇒	⋂V ∈ τ⌝);
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [1, 3, 4] (MAP_EVERY ante_tac));
a(intro_∀_tac1 ⌜τ⌝ THEN1 finite_induction_tac⌜V⌝
	THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[
	pc_rule1"sets_ext1" prove_rule[]
		⌜(∀x a⦁ {x} ⊆ a ⇔ x ∈ a)
	∧	∀a b c⦁a ∪ b ⊆ c ⇔ a ⊆ c ∧ b ⊆ c⌝]));
a(cases_tac⌜V = {}⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(LEMMA_T⌜∀x⦁ ⋂({x} ∪ {}) = x⌝ asm_rewrite_thm_tac);
a(DROP_ASMS_T discard_tac);
a(rewrite_tac[] THEN PC_T1 "sets_ext1" rewrite_tac[]
	THEN prove_tac[]);
a(POP_ASM_T bc_thm_tac THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(lemma_tac⌜x ∩ ⋂V ∈ τ⌝ THEN1 all_fc_tac[∩_open_thm]);
a(LEMMA_T⌜∀x b⦁ ⋂({x} ∪ b) = x ∩ ⋂b⌝ asm_rewrite_thm_tac);
a(DROP_ASMS_T discard_tac);
a(PC_T1 "sets_ext1" rewrite_tac[]
	THEN prove_tac[]);
a(POP_ASM_T bc_thm_tac THEN rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏∩_closed_thm⦎ = save_thm ( "∩_closed_thm", (
set_goal([], ⌜∀τ A B ⦁
	τ ∈ Topology ∧ A ∈ τ Closed ∧ B ∈ τ Closed ⇒ A ∩ B ∈ τ Closed
⌝);
a(REPEAT strip_tac THEN REPEAT_N 2 (POP_ASM_T ante_tac));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[closed_open_complement_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b s⦁a ⊆ s ∧ b ⊆ s ⇒ a ∩ b ⊆ s⌝]);
(* *** Goal "2" *** *)
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀s a b⦁ s \ a ∩ b = (s \ a) ∪ (s \ b)⌝]);
a(all_fc_tac [∪_open_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⋂_closed_thm⦎ = save_thm ( "⋂_closed_thm", (
set_goal([], ⌜∀ τ V⦁
	τ ∈ Topology
∧	¬V = {}
∧	V ⊆ τ Closed
⇒	⋂V ∈ τ Closed
⌝);
a(REPEAT strip_tac THEN POP_ASM_T (ante_tac o pc_rule1"sets_ext1"rewrite_rule[]));
a(PC_T1 "sets_ext1" POP_ASM_T strip_asm_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[closed_open_complement_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜∀t v⦁ t \ ⋂v  = ⋃{a|∃b⦁b ∈ v ∧ a = t \ b}⌝ rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(DROP_ASMS_T discard_tac);
a(PC_T "sets_ext1" contr_tac THEN_TRY all_asm_fc_tac[]);
a(spec_nth_asm_tac 1 ⌜t \ s⌝);
a(spec_nth_asm_tac 1 ⌜s⌝);
(* *** Goal "2.2" *** *)
a(bc_thm_tac ⋃_open_thm THEN REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏∪_closed_thm⦎ = save_thm ( "∪_closed_thm", (
set_goal([], ⌜∀τ A B ⦁
	τ ∈ Topology ∧ A ∈ τ Closed ∧ B ∈ τ Closed ⇒ A ∪ B ∈ τ Closed
⌝);
a(REPEAT strip_tac THEN REPEAT_N 2 (POP_ASM_T ante_tac));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[closed_open_complement_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b s⦁a ⊆ s ∧ b ⊆ s ⇒ a ∪ b ⊆ s⌝]);
(* *** Goal "2" *** *)
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀s a b⦁ s \ (a ∪ b) = (s \ a) ∩ (s \ b)⌝]);
a(all_fc_tac [∩_open_thm]);
pop_thm()
));
=TEX
%%%%
%%%%

=SML

val ⦏⋃_closed_thm⦎ = save_thm ( "⋃_closed_thm", (
set_goal([], ⌜∀ τ V⦁
	τ ∈ Topology
∧	¬V = {}
∧	V ∈ Finite
∧	V ⊆ τ Closed
⇒	⋃V ∈ τ Closed⌝);
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [1, 3, 4] (MAP_EVERY ante_tac));
a(intro_∀_tac1 ⌜τ⌝ THEN1 finite_induction_tac⌜V⌝
	THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[
	pc_rule1"sets_ext1" prove_rule[]
		⌜(∀x a⦁ {x} ⊆ a ⇔ x ∈ a)
	∧	∀a b c⦁a ∪ b ⊆ c ⇔ a ⊆ c ∧ b ⊆ c⌝]));
a(cases_tac⌜V = {}⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(LEMMA_T⌜∀x⦁ ⋃({x} ∪ {}) = x⌝ asm_rewrite_thm_tac);
a(DROP_ASMS_T discard_tac);
a(rewrite_tac[] THEN PC_T1 "sets_ext1" rewrite_tac[]
	THEN prove_tac[]);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(lemma_tac⌜x ∪ ⋃V ∈ τ Closed⌝ THEN1 all_fc_tac[∪_closed_thm]);
a(LEMMA_T⌜∀x b⦁ ⋃({x} ∪ b) = x ∪ ⋃b⌝ asm_rewrite_thm_tac);
a(DROP_ASMS_T discard_tac);
a(PC_T1 "sets_ext1" rewrite_tac[]
	THEN prove_tac[]);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
pop_thm()
));




=TEX
%%%%
%%%%

=SML

val ⦏finite_⋂_open_thm⦎ = save_thm ( "finite_⋂_open_thm", (
set_goal([], ⌜∀τ V⦁
	τ ∈ Topology ∧ V ⊆ τ ∧ ¬V = {} ∧ V ∈ Finite
⇒	⋂V ∈ τ⌝);
a(rewrite_tac[topology_def] THEN REPEAT strip_tac);
a(POP_ASM_T (fn th => POP_ASM_T ante_tac THEN POP_ASM_T ante_tac THEN asm_tac th));
a(finite_induction_tac⌜V⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x y⦁{x} ⊆ y ⇔ x ∈ y⌝]);
a(LEMMA_T⌜⋂{x} = x⌝ (fn th => rewrite_tac [th] THEN taut_tac));
(* *** Goal "3" *** *)
a(PC_T"sets_ext1" strip_tac THEN rewrite_tac[⋂_def] THEN prove_tac[]);
(* *** Goal "4" *** *)
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x y z⦁{x} ∪ z ⊆ y ⇔ x ∈ y ∧ z ⊆ y⌝]);
a(LEMMA_T⌜⋂({x} ∪ V) = x ∩ ⋂V⌝ rewrite_thm_tac);
(* *** Goal "4.1" *** *)
a(PC_T"sets_ext1" strip_tac THEN rewrite_tac[⋂_def, ∩_def, ∪_def] THEN prove_tac[]);
(* *** Goal "4.2" *** *)
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
\subsection{Constructing New Topologies from Old}
%%%%
%%%%

=SML

val ⦏subspace_topology_thm⦎ = save_thm ( "subspace_topology_thm", (
set_goal([], ⌜∀τ X⦁
	τ ∈ Topology
⇒	(X ◁⋎T τ) ∈ Topology⌝);
a(rewrite_tac[topology_def, subspace_topology_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_ante_tac THEN1 PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac ⌜⋃{C| C ∈ τ ∧ C ∩ X ∈ V}⌝  THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "1.1" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.2" *** *)
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.2.1" *** *)
a(all_asm_fc_tac[] THEN all_var_elim_asm_tac1);
a(∃_tac ⌜B⌝  THEN REPEAT strip_tac);
(* *** Goal "1.2.2" *** *)
a(all_asm_fc_tac[] THEN all_var_elim_asm_tac1);
(* *** Goal "1.2.3" *** *)
a(∃_tac ⌜s ∩ X⌝  THEN PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(∃_tac ⌜B' ∩ B''⌝   THEN PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏subspace_topology_space_t_thm⦎ = save_thm ( "subspace_topology_space_t_thm", (
set_goal([], ⌜∀τ A⦁
	τ ∈ Topology
⇒	Space⋎T (A ◁⋎T τ) = A ∩ Space⋎T τ⌝);
a(rewrite_tac[topology_def, space_t_def, subspace_topology_def] THEN
	PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(∃_tac ⌜B⌝  THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(∃_tac ⌜s ∩ A⌝  THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(∃_tac ⌜s ⌝  THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏subspace_topology_space_t_thm1⦎ = save_thm ( "subspace_topology_space_t_thm1", (
set_goal([], ⌜∀τ A⦁
	τ ∈ Topology
∧	A ⊆ Space⋎T τ
⇒	Space⋎T (A ◁⋎T τ) = A⌝);
a(REPEAT strip_tac THEN ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b⦁a ⊆ b = a ∩ b = a⌝]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏universe_subspace_topology_thm⦎ = save_thm ( "universe_subspace_topology_thm", (
set_goal([], ⌜∀τ⦁ (Universe ◁⋎T τ) = τ⌝);
a(REPEAT strip_tac THEN rewrite_tac[subspace_topology_def]);
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀t⦁ {a | ∃b⦁ b ∈ t ∧ a = b} = t⌝]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏open_⊆_space_t_thm⦎ = save_thm ( "open_⊆_space_t_thm", (
set_goal([], ⌜∀τ A⦁
	τ ∈ Topology
∧	A ∈ τ
⇒	A ⊆ Space⋎T τ⌝);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_fc_tac[∈_space_t_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏subspace_topology_space_t_thm2⦎ = save_thm ( "subspace_topology_space_t_thm2", (
set_goal([], ⌜∀τ A⦁
	τ ∈ Topology
∧	A ∈ τ
⇒	Space⋎T (A ◁⋎T τ) = A⌝);
a(REPEAT strip_tac THEN bc_tac[
	subspace_topology_space_t_thm1,
	open_⊆_space_t_thm] THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏subspace_topology_space_t_thm3⦎ = save_thm ( "subspace_topology_space_t_thm3", (
set_goal([], ⌜∀τ A⦁
	τ ∈ Topology
∧	A ∈ τ Closed
⇒	Space⋎T (A ◁⋎T τ) = A⌝);
a(REPEAT strip_tac THEN bc_thm_tac subspace_topology_space_t_thm1);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_fc_tac[∈_closed_∈_space_t_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏subspace_topology_closed_thm⦎ = save_thm ( "subspace_topology_closed_thm", (
set_goal([], ⌜∀X τ⦁
	τ ∈ Topology
⇒	(X ◁⋎T τ) Closed = {A | ∃B⦁ B ∈ τ Closed ∧ A = B ∩ X}
⌝);
a(REPEAT strip_tac THEN PC_T "sets_ext1" strip_tac);
a(lemma_tac⌜X ◁⋎T τ ∈ Topology⌝ THEN1 ALL_FC_T rewrite_tac [subspace_topology_thm]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[closed_open_complement_thm,
	subspace_topology_space_t_thm]
	THEN rewrite_tac[subspace_topology_def]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(∃_tac⌜ Space⋎T τ \ B ⌝);
a(lemma_tac⌜B ⊆ Space⋎T τ⌝ THEN1
	(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_fc_tac[∈_space_t_thm]));
a(ALL_FC_T asm_rewrite_tac[pc_rule1"sets_ext1"prove_rule[]
	⌜∀b s⦁b ⊆ s ⇒ s \ b ⊆ s ∧ s \ (s \ b) = b⌝]);
a(asm_rewrite_tac[pc_rule1"sets_ext1"prove_rule[]
	⌜∀b s x⦁ (s \ b) ∩ x = (x ∩ s) \ (b ∩ x)⌝]);
a(lemma_tac⌜B ∩ X ⊆ X ∩ Space⋎T τ⌝ THEN1
	(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(all_fc_tac[pc_rule1"sets_ext1"prove_rule[]
	⌜∀a b c⦁ a ⊆ c ∧ b ⊆ c ∧ c \ a = b ⇒ a = c \ b⌝]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[pc_rule1"sets_ext1"prove_rule[]
	⌜∀b s x⦁ b ⊆ s ⇒ b ∩ x ⊆ x ∩ s⌝]);
(* *** Goal "3" *** *)
a(∃_tac⌜ Space⋎T τ \ B ⌝ THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1"sets_ext1"prove_rule[]
	⌜∀b s x⦁ (s \ b) ∩ x = (x ∩ s) \ (b ∩ x)⌝]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏trivial_subspace_topology_thm⦎ = save_thm ( "trivial_subspace_topology_thm", (
set_goal([], ⌜∀τ⦁
	τ ∈ Topology
⇒	(Space⋎T τ ◁⋎T τ)  = τ⌝);
a(rewrite_tac[subspace_topology_def] THEN  REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1 THEN all_fc_tac[space_t_open_thm]);
a(all_fc_tac[∩_open_thm]);
(* *** Goal "2" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_fc_tac[∈_space_t_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏⊆_subspace_topology_thm⦎ = save_thm ( "⊆_subspace_topology_thm", (
set_goal([], ⌜∀τ A B⦁
	A ⊆ B
⇒	(A ◁⋎T (B ◁⋎T τ))  = (A ◁⋎T τ)⌝);
a(rewrite_tac[subspace_topology_def] THEN REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(∃_tac⌜B''⌝ THEN asm_rewrite_tac[]);
a(POP_ASM_T discard_tac THEN PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜B' ∩ B⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(∃_tac⌜B'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(POP_ASM_T discard_tac THEN PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏product_topology_thm⦎ = save_thm ( "product_topology_thm", (
set_goal([], ⌜∀σ : 'a SET SET; τ : 'b SET SET⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	(σ ×⋎T τ) ∈ Topology⌝);
a(rewrite_tac[topology_def, product_topology_def]
	THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T  [3] all_fc_tac);
a(∃_tac⌜A⌝  THEN ∃_tac ⌜B⌝ THEN REPEAT strip_tac);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x y z⦁x ⊆ y ∧ y ∈ z ⇒ x ⊆ ⋃ z⌝]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T  [3, 4] all_fc_tac);
a(∃_tac⌜A' ∩ A''⌝  THEN ∃_tac ⌜B' ∩ B''⌝ THEN REPEAT strip_tac
	THEN_TRY SOLVED_T (all_asm_fc_tac[]));
a(MERGE_PCS_T1["'bin_rel", "sets_ext1"] asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏product_topology_space_t_thm⦎ = save_thm ( "product_topology_space_t_thm", (
set_goal([], ⌜∀σ : 'a SET SET; τ : 'b SET SET⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	Space⋎T  (σ ×⋎T τ)  = (Space⋎T σ × Space⋎T τ)⌝);
a(rewrite_tac[product_topology_def, space_t_def]);
a(MERGE_PCS_T1["'bin_rel", "sets_ext1"] REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[] THEN contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[] THEN contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜s × s'⌝ THEN MERGE_PCS_T1["'bin_rel", "sets_ext1"] REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN ∃_tac⌜s'⌝ THEN MERGE_PCS_T1["'bin_rel", "sets_ext1"] REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%

=SML
val ⦏unit_topology_thm⦎ = save_thm ( "unit_topology_thm", (
set_goal([], ⌜ 1⋎T ∈ Topology ⌝);
a(rewrite_tac[topology_def, unit_topology_def]
	THEN MERGE_PCS_T1 ["'one", "sets_ext1"] rewrite_tac[]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
a(asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏space_t_unit_topology_thm⦎ = save_thm ( "space_t_unit_topology_thm", (
set_goal([], ⌜ Space⋎T 1⋎T = Universe ⌝);
a(rewrite_tac[space_t_def, unit_topology_def]
	THEN MERGE_PCS_T1 ["'one", "sets_ext1"] rewrite_tac[]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
a(∃_tac ⌜Universe⌝ THEN asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏power_topology_length_thm⦎ = save_thm ( "power_topology_length_thm", (
set_goal([], ⌜∀τ n v⦁ v ∈ Space⋎T (Π⋎T n τ) ⇒ Length v = n⌝);
a(REPEAT_N 2 strip_tac THEN induction_tac⌜n:ℕ⌝
	THEN rewrite_tac[power_topology_def, space_t_def]
	THEN REPEAT strip_tac THEN_TRY all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[length_def]);
(* *** Goal "2" *** *)
a(strip_asm_tac(∀_elim⌜v⌝ list_cases_thm) THEN all_var_elim_asm_tac1
	THEN all_asm_fc_tac[]);
a(all_fc_tac[∈_space_t_thm]);
a(all_asm_fc_tac[] THEN asm_rewrite_tac[length_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏power_topology_thm⦎ = save_thm ( "power_topology_thm", (
set_goal([], ⌜∀τ n⦁ τ ∈ Topology ⇒ Π⋎T n τ ∈ Topology⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝
	THEN rewrite_tac[power_topology_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" prove_tac[topology_def]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext1" rewrite_tac[topology_def] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜A⌝ THEN ∃_tac⌜B⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.3" *** *)
a(LIST_DROP_NTH_ASM_T  [3, 5] all_fc_tac);
a(∃_tac⌜A' ∩ A''⌝  THEN ∃_tac ⌜B' ∩ B''⌝ THEN REPEAT strip_tac
	THEN all_asm_fc_tac[∩_open_thm]);
pop_thm()
));


=TEX
\subsection{Continuity}
=TEX
%%%%
%%%%

=SML

val ⦏continuous_∈_space_t_thm⦎ = save_thm ( "continuous_∈_space_t_thm", (
set_goal([], ⌜∀ σ; τ; f : 'a → 'b; x⦁
	f ∈ (σ, τ) Continuous ∧ x ∈ Space⋎T σ ⇒ f x ∈ Space⋎T τ
⌝);
a(rewrite_tac[continuous_def] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏continuous_open_thm⦎ = save_thm ( "continuous_open_thm", (
set_goal([], ⌜∀ σ; τ; f : 'a → 'b; A⦁
	f ∈ (σ, τ) Continuous ∧ A ∈ τ ⇒ {x|x ∈ Space⋎T σ ∧ f x ∈ A} ∈ σ
⌝);
a(rewrite_tac[continuous_def] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏continuous_closed_thm⦎ = save_thm ( "continuous_closed_thm", (
set_goal([], ⌜∀ σ : 'a SET SET; τ : 'b SET SET⦁
	(σ, τ) Continuous =
	{f
	|	(∀x⦁ x ∈ Space⋎T σ ⇒ f x ∈ Space⋎T τ)
	∧	(∀A⦁ A ∈ τ Closed ⇒ {x | x ∈ Space⋎T σ ∧ f x ∈ A} ∈ σ Closed)}
⌝);
a(REPEAT ∀_tac THEN  rewrite_tac[continuous_def]);
a(PC_T1 "sets_ext1" once_rewrite_tac[] THEN strip_tac);
a(rename_tac[(⌜x⌝, "f")] THEN rewrite_tac[
		taut_rule ⌜∀p q r⦁ (r ∧ p ⇔ r ∧ q) ⇔ (r ⇒ (p ⇔ q)) ⌝,
		closed_def]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
a(∃_tac⌜{x|x ∈ Space⋎T σ ∧ f x ∈ B} ⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 2 (ante_tac o ∀_elim⌜Space⋎T τ \ A⌝));
a(LEMMA_T ⌜∃ B⦁ B ∈ τ ∧ Space⋎T τ \ A = Space⋎T τ \ B⌝ rewrite_thm_tac
	THEN1 asm_prove_tac[]);
a(REPEAT strip_tac);
a(LEMMA_T ⌜{x|x ∈ Space⋎T σ ∧ f x ∈ A} = B⌝ asm_rewrite_thm_tac);
a(lemma_tac⌜B ⊆ Space⋎T σ⌝ THEN1
	(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_fc_tac[∈_space_t_thm]));
a(lemma_tac⌜{x|x ∈ Space⋎T σ ∧ f x ∈ A} ⊆ Space⋎T σ⌝ THEN1
	(PC_T1 "sets_ext1" prove_tac[]));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜ ∀a b c⦁ a ⊆ c ∧ b ⊆ c ⇒ (a = b ⇔ c \ a = c \ b)⌝]);
a(DROP_NTH_ASM_T 3 (rewrite_thm_tac o eq_sym_rule));
a(PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏subspace_continuous_thm⦎ = save_thm ( "subspace_continuous_thm", (
set_goal([], ⌜∀σ τ A B f⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	f ∈ (σ, τ) Continuous
∧	(∀x⦁ x ∈ A ⇒ f x ∈ B)
⇒	f ∈ (A ◁⋎T σ, B ◁⋎T τ) Continuous
⌝);
a(REPEAT strip_tac THEN rewrite_tac[continuous_def]);
a(ALL_FC_T asm_rewrite_tac[subspace_topology_space_t_thm]);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[continuous_def]));
a(rewrite_tac[subspace_topology_def]THEN REPEAT strip_tac
	THEN (all_var_elim_asm_tac1
		ORELSE all_asm_fc_tac[]));
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜{x|x ∈ Space⋎T σ ∧ f x ∈ B'}⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏subspace_domain_continuous_thm⦎ = save_thm ( "subspace_domain_continuous_thm", (
set_goal([], ⌜∀σ τ A B f⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	f ∈ (σ, τ) Continuous
⇒	f ∈ (A ◁⋎T σ, τ) Continuous
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜τ = Universe ◁⋎T τ⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[universe_subspace_topology_thm]);
a(bc_thm_tac subspace_continuous_thm THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏empty_continuous_thm⦎ = save_thm ( "empty_continuous_thm", (
set_goal([], ⌜∀σ τ f⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	f ∈ ({} ◁⋎T σ, τ) Continuous
⌝);
a(REPEAT strip_tac);
a(asm_rewrite_tac[continuous_def]);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]);
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜{x|F} = {}⌝]);
a(REPEAT strip_tac THEN rewrite_tac[subspace_topology_def]);
a(∃_tac⌜{}⌝ THEN ALL_FC_T rewrite_tac[empty_open_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏subspace_range_continuous_thm⦎ = save_thm ( "subspace_range_continuous_thm", (
set_goal([], ⌜∀σ τ f B⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	f ∈ (σ, B ◁⋎T τ) Continuous
⇒	f ∈ (σ, τ) Continuous
⌝);
a(rewrite_tac[continuous_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[] THEN POP_ASM_T ante_tac);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜∀x⦁ x ∈ Space⋎T σ ∧ f x ∈ A ⇔
	x ∈ Space⋎T σ ∧ f x ∈ A ∩ B⌝
	rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 3 ante_tac);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 2 bc_thm_tac);
a(rewrite_tac[subspace_topology_def]
	THEN asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏subspace_range_continuous_⇔_thm⦎ = save_thm ( "subspace_range_continuous_⇔_thm", (
set_goal([], ⌜∀σ; τ; f : 'a → 'b; B⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	B ⊆ Space⋎T τ
⇒	(f ∈ (σ, B ◁⋎T τ) Continuous ⇔
	 f ∈ (σ, τ) Continuous ∧ ∀x⦁ x ∈ Space⋎T σ ⇒ f x ∈ B)
⌝);
a(REPEAT strip_tac THEN1 all_fc_tac[subspace_range_continuous_thm]);
(* *** Goal "1" *** *)
a(all_fc_tac[continuous_∈_space_t_thm]);
a(POP_ASM_T ante_tac THEN ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]);
a(REPEAT strip_tac);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[continuous_def] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]);
a(all_asm_fc_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[subspace_topology_def] THEN strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(LEMMA_T ⌜∀x⦁ x ∈ Space⋎T σ ∧ f x ∈ A ⇔ x ∈ Space⋎T σ ∧ f x ∈ B'⌝
	asm_rewrite_thm_tac);
a(all_var_elim_asm_tac1 THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏subspace_range_continuous_bc_thm⦎ = save_thm ( "subspace_range_continuous_bc_thm", (
set_goal([], ⌜∀σ; τ; f : 'a → 'b; B⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	B ⊆ Space⋎T τ
∧	(∀x⦁ x ∈ Space⋎T σ ⇒ f x ∈ B)
∧	f ∈ (σ, τ) Continuous
⇒	f ∈ (σ, B ◁⋎T τ) Continuous
⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[subspace_range_continuous_⇔_thm]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏const_continuous_thm⦎ = save_thm ( "const_continuous_thm", (
set_goal([], ⌜∀σ τ c⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	c ∈ Space⋎T τ
⇒	(λx⦁ c) ∈ (σ, τ) Continuous
⌝);
a(REPEAT strip_tac);
a(rewrite_tac[continuous_def, topology_def] THEN
	PC_T1 "sets_ext1" REPEAT strip_tac);
a(cases_tac⌜c ∈ A⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(rewrite_tac[pc_rule1"sets_ext" prove_rule[]⌜{x | x ∈ Space⋎T σ} = Space⋎T σ⌝]);
a(all_asm_fc_tac[space_t_open_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[pc_rule1"sets_ext" prove_rule[]⌜{x | F} = {}⌝]);
a(all_asm_fc_tac[empty_open_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏id_continuous_thm⦎ = save_thm ( "id_continuous_thm", (
set_goal([], ⌜∀τ⦁
	τ ∈ Topology
⇒	(λx⦁ x) ∈ (τ, τ) Continuous
⌝);
a(rewrite_tac[continuous_def, topology_def, space_t_def] THEN
	PC_T1 "sets_ext1" REPEAT strip_tac);
a(LEMMA_T ⌜ {x|x ∈ ⋃ τ ∧ x ∈ A} = A⌝  asm_rewrite_thm_tac);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1"  prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏comp_continuous_thm⦎ = save_thm ( "comp_continuous_thm", (
set_goal([], ⌜∀f g ρ σ τ⦁
	f ∈ (ρ, σ) Continuous
∧	g ∈ (σ, τ) Continuous
∧	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	(λx⦁ g(f x)) ∈ (ρ, τ) Continuous
⌝);
a(rewrite_tac[continuous_def] THEN REPEAT strip_tac THEN
	(all_asm_fc_tac[] THEN all_asm_fc_tac[]));
a( LEMMA_T ⌜{x|x ∈ Space⋎T ρ ∧ g (f x) ∈ A} ={x|x ∈ Space⋎T ρ ∧ f x ∈ {x|x ∈ Space⋎T σ ∧ g x ∈ A}}⌝
	once_rewrite_thm_tac THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" prove_tac[] THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏left_proj_continuous_thm⦎ = save_thm ( "left_proj_continuous_thm", (
set_goal([], ⌜∀σ : 'a SET SET; τ : 'b SET SET⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	(λ(x, y)⦁ x) ∈ ((σ ×⋎T τ), σ) Continuous
⌝);
a(REPEAT strip_tac THEN rewrite_tac[continuous_def]);
a(all_fc_tac[product_topology_thm]);
a(ALL_FC_T rewrite_tac [product_topology_space_t_thm]);
a(rewrite_tac[product_topology_def, ×_def] THEN REPEAT strip_tac);
a(∃_tac⌜A⌝ THEN ∃_tac⌜Space⋎T τ⌝ THEN
	ALL_FC_T asm_rewrite_tac[space_t_open_thm]);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a(all_fc_tac[∈_space_t_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏fst_continuous_thm⦎ = save_thm ( "fst_continuous_thm", (
set_goal([], ⌜∀σ : 'a SET SET; τ : 'b SET SET⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	Fst ∈ ((σ ×⋎T τ), σ) Continuous
⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜Fst = λ(x:'a, y:'b)⦁x⌝ rewrite_thm_tac THEN1 prove_tac[]);
a(all_fc_tac[left_proj_continuous_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏right_proj_continuous_thm⦎ = save_thm ( "right_proj_continuous_thm", (
set_goal([], ⌜∀σ : 'a SET SET; τ : 'b SET SET⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	(λ(x, y)⦁ y) ∈ ((σ ×⋎T τ), τ) Continuous
⌝);
a(REPEAT strip_tac THEN rewrite_tac[continuous_def]);
a(all_fc_tac[product_topology_thm]);
a(ALL_FC_T rewrite_tac [product_topology_space_t_thm]);
a(rewrite_tac[product_topology_def, ×_def] THEN REPEAT strip_tac);
a(∃_tac⌜Space⋎T σ⌝ THEN ∃_tac⌜A⌝ THEN
	ALL_FC_T asm_rewrite_tac[space_t_open_thm]);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a(all_fc_tac[∈_space_t_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏snd_continuous_thm⦎ = save_thm ( "snd_continuous_thm", (
set_goal([], ⌜∀σ : 'a SET SET; τ : 'b SET SET⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	Snd ∈ ((σ ×⋎T τ), τ) Continuous
⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜Snd = λ(x:'a, y:'b)⦁y⌝ rewrite_thm_tac THEN1 prove_tac[]);
a(all_fc_tac[right_proj_continuous_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏product_continuous_thm⦎ = save_thm ( "product_continuous_thm", (
set_goal([], ⌜∀ f : 'a → 'b; g : 'a → 'c; ρ : 'a SET SET; σ : 'b SET SET; τ : 'c SET SET⦁
	f ∈ (ρ, σ) Continuous
∧	g ∈ (ρ, τ) Continuous
∧	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	(λz⦁(f z, g z)) ∈ (ρ, (σ ×⋎T τ)) Continuous
⌝);
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4, 5] (MAP_EVERY ante_tac));
a(rewrite_tac[continuous_def]);
a(all_fc_tac[product_topology_thm]);
a(ALL_FC_T rewrite_tac [product_topology_space_t_thm]);
a(rewrite_tac[product_topology_def, ×_def] THEN REPEAT strip_tac
	THEN_TRY (SOLVED_T (all_asm_fc_tac[])));
a(LIST_DROP_NTH_ASM_T (interval 6 16) discard_tac
	THEN ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]);
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
a(LIST_DROP_NTH_ASM_T [11, 13] all_fc_tac);
a(∃_tac⌜{x|x ∈ Space⋎T ρ ∧ g x ∈ B} ∩ {x|x ∈ Space⋎T ρ ∧ f x ∈ A'}⌝);
a(ALL_FC_T rewrite_tac[∩_open_thm]);
a(REPEAT strip_tac THEN PC_T1"sets_ext1" REPEAT strip_tac);
a(bc_thm_tac (pc_rule1"sets_ext" prove_rule[]⌜∀a xy⦁xy ∈ a ∧ a ⊆ A ⇒ xy ∈ A⌝));
a(∃_tac⌜{(v, w)|v ∈ A' ∧ w ∈ B}⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

set_goal([], ⌜∀ f : 'a → 'b; g : 'a → 'c; ρ : 'a SET SET; σ : 'b SET SET; τ : 'c SET SET⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	((λz⦁(f z, g z)) ∈ (ρ, (σ ×⋎T τ)) Continuous
	⇔	f ∈ (ρ, σ) Continuous
	∧	g ∈ (ρ, τ) Continuous)

⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac⌜(σ ×⋎T τ) ∈ Topology⌝ THEN1 all_fc_tac[product_topology_thm]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T⌜(λz⦁ (λ(x, y)⦁ x) ((λz⦁(f z, g z)) z))  ∈ (ρ, σ) Continuous⌝
	(fn th => ante_tac th THEN rewrite_tac[η_axiom]));
a(bc_thm_tac comp_continuous_thm);
a(∃_tac⌜σ ×⋎T τ⌝ THEN REPEAT strip_tac);
a(bc_thm_tac left_proj_continuous_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LEMMA_T⌜(λz⦁ (λ(x, y)⦁ y) ((λz⦁(f z, g z)) z))  ∈ (ρ, τ) Continuous⌝
	(fn th => ante_tac th THEN rewrite_tac[η_axiom]));
a(bc_thm_tac comp_continuous_thm);
a(∃_tac⌜σ ×⋎T τ⌝ THEN REPEAT strip_tac);
a(bc_thm_tac right_proj_continuous_thm THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(all_fc_tac[product_continuous_thm]);
val ⦏product_continuous_⇔_thm⦎ = save_pop_thm "product_continuous_⇔_thm";


=TEX
%%%%
%%%%

=SML

val ⦏left_product_inj_continuous_thm⦎ = save_thm ( "left_product_inj_continuous_thm", (
set_goal([], ⌜∀σ : 'a SET SET; τ : 'b SET SET; y : 'b⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	y ∈ Space⋎T τ
⇒	(λx⦁ (x, y)) ∈ (σ, σ ×⋎T τ) Continuous
⌝);
a(REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜λx:'a⦁ x⌝, ⌜λx:'a⦁y⌝, ⌜σ⌝, ⌜σ⌝, ⌜τ⌝] product_continuous_thm));
a(ALL_FC_T asm_rewrite_tac[id_continuous_thm, const_continuous_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏right_product_inj_continuous_thm⦎ = save_thm ( "right_product_inj_continuous_thm", (
set_goal([], ⌜∀σ: 'a SET SET; τ : 'b SET SET; x : 'a⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	x ∈ Space⋎T σ
⇒	(λy⦁ (x, y)) ∈ (τ, σ ×⋎T τ) Continuous
⌝);
a(REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜λy:'b⦁ x⌝, ⌜λy:'b⦁y⌝, ⌜τ⌝, ⌜σ⌝, ⌜τ⌝] product_continuous_thm));
a(ALL_FC_T asm_rewrite_tac[id_continuous_thm, const_continuous_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏range_unit_topology_continuous_thm⦎ = save_thm ( "range_unit_topology_continuous_thm", (
set_goal([], ⌜∀τ: 'a SET SET; f : 'a → ONE⦁
	τ ∈ Topology
⇒	f ∈ (τ, 1⋎T) Continuous
⌝);
a(rewrite_tac[continuous_def,
		unit_topology_def, space_t_unit_topology_thm] THEN
	REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" rewrite_tac[pc_rule1"sets_ext1" prove_rule[] ⌜{x|F} = {}⌝]);
a(all_fc_tac[empty_open_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[one_def, pc_rule1"sets_ext1" prove_rule[] ⌜∀a⦁{x|x ∈ a} = a⌝]);
a(all_fc_tac[space_t_open_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏domain_unit_topology_continuous_thm⦎ = save_thm ( "domain_unit_topology_continuous_thm", (
set_goal([], ⌜∀τ: 'a SET SET; f : ONE → 'a⦁
	τ ∈ Topology
∧	f One ∈ Space⋎T τ
⇒	f ∈ (1⋎T, τ) Continuous
⌝);
a(rewrite_tac[continuous_def,
		unit_topology_def, space_t_unit_topology_thm] THEN
	REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[one_def]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN POP_ASM_T ante_tac);
a(PC_T1 "sets_ext1" rewrite_tac[one_def]);
pop_thm()
));

=TEX

We instantiate the morphism-proving tools to prove continuity of functions between topological spaces.

=TEX
Next we give the backchaining theorems.
=SML
val ⦏pair_continuous_thm⦎ = snd ( "pair_continuous_thm", (
set_goal([], ⌜∀ ρ σ τ f g⦁
	ρ ∈ Topology ∧ σ ∈ Topology ∧ τ ∈ Topology ∧
	f ∈ (ρ, σ) Continuous ∧ g ∈ (ρ, τ) Continuous ⇒
	Pair (f, g) ∈ (ρ, σ ×⋎T τ) Continuous
⌝);
a(REPEAT strip_tac THEN rewrite_tac[pair_def]
	THEN ALL_FC_T rewrite_tac[product_continuous_thm]);
pop_thm()
));

=TEX
=SML
val ⦏o_continuous_thm⦎ = snd ( "o_continuous_thm", (
set_goal([], ⌜∀ ρ σ τ f g⦁
	ρ ∈ Topology ∧ σ ∈ Topology ∧ τ ∈ Topology ∧
	f ∈ (ρ, σ) Continuous ∧ g ∈ (σ, τ) Continuous ⇒
	g o f ∈ (ρ, τ) Continuous
⌝);
a(REPEAT strip_tac THEN rewrite_tac[
		prove_rule[o_def] ⌜∀f g⦁ g o f = λx⦁ g(f x)⌝]
	THEN ALL_FC_T rewrite_tac[comp_continuous_thm]);
pop_thm()
));

=TEX
=SML
val ⦏i_continuous_thm⦎ = snd ( "i_continuous_thm", (
set_goal([], ⌜∀τ⦁ τ ∈ Topology ⇒ CombI ∈ (τ, τ) Continuous⌝);
a(REPEAT strip_tac THEN rewrite_tac[
		prove_rule[get_spec⌜CombI⌝] ⌜CombI = λx⦁ x⌝]
	THEN ALL_FC_T rewrite_tac[id_continuous_thm]);
pop_thm()
));

=TEX
=SML
val ⦏k_continuous_thm⦎ = snd ( "k_continuous_thm", (
set_goal([], ⌜∀ σ τ c⦁
	σ ∈ Topology ∧ τ ∈ Topology ∧ c ∈ Space⋎T τ ⇒
	CombK c ∈ (σ, τ) Continuous⌝);
a(REPEAT strip_tac THEN rewrite_tac[
		prove_rule[get_spec⌜CombK⌝] ⌜∀c⦁CombK c = λx⦁ c⌝]
	THEN ALL_FC_T rewrite_tac[const_continuous_thm]);
pop_thm()
));

=TEX
=SML

val ⦏∈_space_t_product_thm⦎ = snd ( "∈_space_t_product_thm", (
set_goal([], ⌜∀σ τ x⦁
	σ ∈ Topology ∧ τ ∈ Topology ∧ Fst x ∈ Space⋎T σ ∧ Snd x ∈ Space⋎T τ ⇒
	x ∈ Space⋎T(σ ×⋎T τ)⌝);
a(REPEAT strip_tac THEN ALL_FC_T rewrite_tac[product_topology_space_t_thm]);
a(asm_rewrite_tac[×_def]);
pop_thm()
));


=TEX
Now we define the basic continuity-proving tactic. It will be parametrized by a list of theorems from which it extracts information about known topological spaces and known continuous functions.

=SML

local

(*
=TEX
We bring together the basic facts about product topologies and constructing new continuous functions from old.
=SML
*)

val ⦏continuity_fact_thms⦎ : THM list = [
	product_topology_thm,
	∈_space_t_product_thm,
	fst_continuous_thm,
	snd_continuous_thm,
	i_continuous_thm,
	k_continuous_thm,
	pair_continuous_thm,
	o_continuous_thm];

(*
=TEX
We analyse the input theorems by matching their conclusions with template terms as follows. (Here in each pair, the first element is the variable that matches the continuous function or topological space and the second is the template term).
=SML
*)

(*
=TEX
Now we pull the above pieces together into a function that constructs the parameters needed by the basic morphismhood prover from a list of theorems.
=SML
*)
val ⦏continuity_pats⦎ = {
	object_pat = ⌜(α, α ∈ Topology)⌝,
	unary_pat = ⌜(x, x ∈ (α, β) Continuous)⌝,
	binary_pat = ⌜(x, Uncurry x ∈ (α, β) Continuous)⌝,
	parametrized_pat = ⌜(h, (λ x⦁ h x p) ∈ (α, β) Continuous)⌝};

val ⦏fst_snd⦎ : TERM list = [⌜Fst⌝,  ⌜Snd⌝];

val ⦏product_t_const⦎ : TERM = ⌜$×⋎T⌝;

val ⦏continuity_params⦎ = morphism_params
		continuity_pats
		fst_snd
		[([], product_t_const)]
		∃_object_by_type_tac
		continuity_fact_thms;
in
(*
=TEX
This gives us our basic continuity prover.
=SML
*)
fun ⦏basic_continuity_tac⦎ (thms : THM list): TACTIC = (fn gl as (asms, _) =>
	basic_morphism_tac (continuity_params (thms @ map asm_rule asms)) [] gl
);
end (* local ... in ... end *);
=TEX

A tactic to prove objecthood in the category of topological spaces is also useful. The following will do this given a list of theorems that either
assert that particular sets are topologies or are Horn clauses with
conclusions making such an assertion.
=SML
local
	val ∈_topology_pattern = ⌜α ∈ Topology⌝;
in
fun ⦏basic_topology_tac⦎ (thms : THM list) : TACTIC = (fn gl as (asms, _) =>
	let
		val all_thms = map asm_rule asms @ thms;
		fun is_∈_topology tm = (
			(term_match tm ∈_topology_pattern; true)
			handle Fail _ => false
		);
		fun is_rule thm = (
			let	val tm = (snd o strip_∀ o concl) thm;
			in
			is_⇒ tm andalso (is_∈_topology o snd o dest_⇒) tm
			end
		);
		val is_axiom = is_∈_topology o snd o strip_∀ o concl;
		val rule_thms = product_topology_thm ::
					subspace_topology_thm ::
					all_thms drop (not o is_rule);
		val basic_thms = unit_topology_thm ::
					all_thms drop (not o is_axiom);
	in	(REPEAT o CHANGED_T o FIRST)
			[rewrite_tac basic_thms, bc_tac rule_thms]
	end	gl
);
end;

=TEX
%%%%
%%%%

=SML

val ⦏diag_inj_continuous_thm⦎ = save_thm ( "diag_inj_continuous_thm", (
set_goal([], ⌜∀ τ : 'a SET SET⦁
	τ ∈ Topology
⇒	(λx⦁ (x, x)) ∈ (τ, τ ×⋎T τ) Continuous
⌝);
a(REPEAT strip_tac);
a(basic_continuity_tac[]);
pop_thm()
));

=TEX
The following theorem about the continuity of a function defined by cases is not
the most general of its type, but it should be suffficient for the intended applications
in, for example, showing the continuity of a piecewise linear function.
The condition on $f$ and $g$ is that they agree on every point $x$ that is
in the interesection of the closure of $X$ and the closure of its complement.
%%%%
%%%%

=SML

val ⦏cond_continuous_thm⦎ = save_thm ( "cond_continuous_thm", (
set_goal([], ⌜∀f g X σ τ⦁
	f ∈ (σ, τ) Continuous
∧	g ∈ (σ, τ) Continuous
∧	(∀x⦁x ∈ Space⋎T σ ∧  (∀A⦁x ∈ A ∧ A ∈ σ ⇒ ∃y z⦁y ∈ A ∧ z ∈ A ∧ y ∈ X ∧ ¬z ∈ X)
		⇒ f x = g x)
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	(λx⦁ if x ∈ X then f x else g x) ∈ (σ, τ) Continuous
⌝);
a(rewrite_tac[continuous_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(cases_tac⌜x ∈ X⌝ THEN asm_rewrite_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]);
a(strip_tac THEN rewrite_tac[]);
a(cases_tac⌜x ∈ X⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(cases_tac⌜¬ ∀ A⦁ x ∈ A ∧ A ∈ σ ⇒ (∃ y z⦁ y ∈ A ∧ z ∈ A ∧ y ∈ X ∧ ¬ z ∈ X)⌝);
(* *** Goal "2.1.1" *** *)
a(LIST_DROP_NTH_ASM_T [13] all_fc_tac);
a(∃_tac⌜{x|x ∈ Space⋎T σ ∧ f x ∈ A} ∩ A'⌝);
a(REPEAT strip_tac);
(* *** Goal "2.1.1.1" *** *)
a(bc_thm_tac ∩_open_thm THEN REPEAT strip_tac);
(* *** Goal "2.1.1.2" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(spec_nth_asm_tac 5 ⌜x⌝);
a(spec_nth_asm_tac 1 ⌜x'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a(LIST_DROP_NTH_ASM_T [9, 11] all_fc_tac);
a(∃_tac⌜{x|x ∈ Space⋎T σ ∧ f x ∈ A} ∩ {x | x ∈ Space⋎T σ ∧ g x ∈ A}⌝);
a(REPEAT strip_tac);
(* *** Goal "2.1.2.1" *** *)
a(bc_thm_tac ∩_open_thm THEN REPEAT strip_tac);
(* *** Goal "2.1.2.2" *** *)
a(LEMMA_T⌜f x = g x⌝ (asm_rewrite_thm_tac o eq_sym_rule));
a(all_asm_fc_tac[]);
(* *** Goal "2.1.2.3" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(cases_tac ⌜x' ∈ X⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(cases_tac⌜¬ ∀ A⦁ x ∈ A ∧ A ∈ σ ⇒ (∃ y z⦁ y ∈ A ∧ z ∈ A ∧ y ∈ X ∧ ¬ z ∈ X)⌝);
(* *** Goal "2.2.1" *** *)
a(LIST_DROP_NTH_ASM_T [11] all_fc_tac);
a(∃_tac⌜{x|x ∈ Space⋎T σ ∧ g x ∈ A} ∩ A'⌝);
a(REPEAT strip_tac);
(* *** Goal "2.2.1.1" *** *)
a(bc_thm_tac ∩_open_thm THEN REPEAT strip_tac);
(* *** Goal "2.2.1.2" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(spec_nth_asm_tac 5 ⌜x'⌝);
a(spec_nth_asm_tac 1 ⌜x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [9, 11] all_fc_tac);
a(∃_tac⌜{x|x ∈ Space⋎T σ ∧ f x ∈ A} ∩ {x | x ∈ Space⋎T σ ∧ g x ∈ A}⌝);
a(REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a(bc_thm_tac ∩_open_thm THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2" *** *)
a(LEMMA_T⌜f x = g x⌝ asm_rewrite_thm_tac);
a(all_asm_fc_tac[]);
(* *** Goal "2.2.2.3" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(cases_tac ⌜x' ∈ X⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏closed_∪_closed_continuous_thm⦎ = save_thm ( "closed_∪_closed_continuous_thm", (
set_goal([], ⌜∀σ τ A B f g⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	A ∈ σ Closed
∧	B ∈ σ Closed
∧	f ∈ (A ◁⋎T σ, τ) Continuous
∧	g ∈ (B ◁⋎T σ, τ) Continuous
∧	(∀x⦁x ∈ A ∩ B ⇒ f x = g x)
⇒	(λx⦁ if x ∈ A then f x else g x) ∈ ((A ∪ B) ◁⋎T σ, τ) Continuous
⌝);
a(rewrite_tac[continuous_closed_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T (interval 1 6) (MAP_EVERY ante_tac));
a(lemma_tac ⌜A ∪ B ∈ σ Closed⌝ THEN1 all_fc_tac[∪_closed_thm]);
a(ALL_FC_T rewrite_tac[subspace_topology_closed_thm,
	subspace_topology_space_t_thm3]);
a(PC_T1 "predicates" REPEAT strip_tac
	THEN cases_tac⌜x ∈ A⌝);
(* *** Goal "1.1" *** *)
a(LIST_DROP_NTH_ASM_T [7] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 2 strip_asm_tac);
a(LIST_DROP_NTH_ASM_T [5] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T (interval 1 6) (MAP_EVERY ante_tac));
a(lemma_tac ⌜A ∪ B ∈ σ Closed⌝ THEN1 all_fc_tac[∪_closed_thm]);
a(ALL_FC_T rewrite_tac[subspace_topology_closed_thm,
	subspace_topology_space_t_thm3]
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3, 5] all_fc_tac);
a(∃_tac⌜(B'' ∩ A) ∪ (B' ∩ B)⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_tac[∩_closed_thm, ∪_closed_thm] THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(LIST_DROP_NTH_ASM_T [1, 3] (rewrite_tac o map eq_sym_rule));
a(DROP_NTH_ASM_T 4 ante_tac THEN DROP_ASMS_T discard_tac);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN strip_tac THEN ∀_tac);
a(cases_tac⌜x ∈ A⌝ THEN asm_rewrite_tac[]
	THEN asm_prove_tac[]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
pop_thm()
));


=TEX

%%%%
%%%%
=SML

val ⦏open_∪_open_continuous_thm⦎ = save_thm ( "open_∪_open_continuous_thm", (
set_goal([], ⌜∀σ τ A B f g⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	A ∈ σ
∧	B ∈ σ
∧	f ∈ (A ◁⋎T σ, τ) Continuous
∧	g ∈ (B ◁⋎T σ, τ) Continuous
∧	(∀x⦁x ∈ A ∩ B ⇒ f x = g x)
⇒	(λx⦁ if x ∈ A then f x else g x) ∈ ((A ∪ B) ◁⋎T σ, τ) Continuous
⌝);
a(rewrite_tac[continuous_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T (interval 1 6) (MAP_EVERY ante_tac));
a(lemma_tac ⌜A ∪ B ∈ σ⌝ THEN1 all_fc_tac[∪_open_thm]);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm2]);
a(rewrite_tac[subspace_topology_def]);
a(PC_T1 "predicates" REPEAT strip_tac
	THEN cases_tac⌜x ∈ A⌝);
(* *** Goal "1.1" *** *)
a(LIST_DROP_NTH_ASM_T [7] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 2 strip_asm_tac);
a(LIST_DROP_NTH_ASM_T [5] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T (interval 1 6) (MAP_EVERY ante_tac));
a(lemma_tac ⌜A ∪ B ∈ σ⌝ THEN1 all_fc_tac[∪_open_thm]);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm2]);
a(rewrite_tac[subspace_topology_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3, 5] all_fc_tac);
a(∃_tac⌜(B'' ∩ A) ∪ (B' ∩ B)⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_tac[∩_open_thm, ∪_open_thm] THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(LIST_DROP_NTH_ASM_T [1, 3] (rewrite_tac o map eq_sym_rule));
a(DROP_NTH_ASM_T 4 ante_tac THEN DROP_ASMS_T discard_tac);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN strip_tac THEN ∀_tac);
a(cases_tac⌜x ∈ A⌝ THEN asm_rewrite_tac[]
	THEN asm_prove_tac[]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏compatible_family_continuous_thm⦎ = save_thm ( "compatible_family_continuous_thm", (
set_goal([], ⌜∀σ τ X U G⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	(∀x⦁ x ∈ X ⇒ U x ⊆ X)
∧	(∀x⦁ x ∈ X ⇒ x ∈ U x)
∧	(∀x⦁ x ∈ X ⇒ U x ∈ X ◁⋎T σ)
∧	(∀x⦁ x ∈ X ⇒ G x ∈ (U x ◁⋎T σ, τ) Continuous)
∧	(∀x y⦁ x ∈ X ∧ y ∈ U x ⇒ G y y = G x y)
⇒	(λx⦁ G x x) ∈ (X ◁⋎T σ, τ) Continuous
⌝);
a(rewrite_tac[continuous_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac THEN ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]
	THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [4] (FC_T bc_tac));
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]
	THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜X ⊆ Space⋎T σ⌝);
(* *** Goal "2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(lemma_tac ⌜X ◁⋎T σ ∈ Topology⌝ THEN1 
	(bc_thm_tac subspace_topology_thm THEN REPEAT strip_tac));
a(LEMMA_T ⌜x ∈ Space⋎T (X ◁⋎T σ)⌝ ante_tac THEN1 all_fc_tac[∈_space_t_thm]);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm1]);
a(lemma_tac⌜X ◁⋎T σ ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]
	THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(LIST_DROP_NTH_ASM_T [3, 4](MAP_EVERY ante_tac));
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm1]);
a(rewrite_tac[subspace_topology_def] THEN REPEAT strip_tac);
a(lemma_tac⌜x ∈ B ∩ U x⌝
	THEN1 (DROP_NTH_ASM_T 3 (rewrite_thm_tac o eq_sym_rule)
		THEN asm_rewrite_tac[]));
a(∃_tac⌜B ∩ U x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(∃_tac⌜B ∩ B'⌝ THEN REPEAT strip_tac THEN1 all_fc_tac[∩_open_thm]);
a(asm_rewrite_tac[] THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(DROP_NTH_ASM_T 4 (rewrite_thm_tac o eq_sym_rule));
a(PC_T1 "sets_ext1" REPEAT strip_tac
	THEN1 PC_T1 "sets_ext" all_asm_fc_tac[]);
a(LIST_DROP_NTH_ASM_T [15] (ALL_FC_T asm_rewrite_tac));
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏compatible_family_continuous_thm1⦎ = save_thm ( "compatible_family_continuous_thm1", (
set_goal([], ⌜∀σ : ('a × 'b) SET SET; τ : 'c SET SET; X U G⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	(∀v r⦁ (v, r) ∈ X ⇒ U (v, r) ⊆ X)
∧	(∀v r⦁ (v, r) ∈ X ⇒ (v, r) ∈ U (v, r))
∧	(∀v r⦁ (v, r) ∈ X ⇒ U (v, r) ∈ X ◁⋎T σ)
∧	(∀v r⦁ (v, r) ∈ X ⇒ G (v, r) ∈ (U (v, r) ◁⋎T σ, τ) Continuous)
∧	(∀v r w s⦁ (v, r) ∈ X ∧ (w, s) ∈ U (v, r) ⇒ G (w, s) (w, s) = G (v, r) (w, s))
⇒	(λ(v, r)⦁ G (v, r) (v, r)) ∈ (X ◁⋎T σ, τ) Continuous
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜(λ(v, r)⦁ G (v, r) (v, r)) = (λx⦁G x x)⌝ rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac compatible_family_continuous_thm);
a(∃_tac⌜U⌝ THEN REPEAT strip_tac
	THEN pair_tac⌜x = (a : 'a, b : 'b)⌝
	THEN_TRY pair_tac⌜y = (c : 'a, d : 'b)⌝
	THEN asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏same_on_space_continuous_thm⦎ = save_thm ( "same_on_space_continuous_thm", (
set_goal([], ⌜∀σ τ f g⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	g ∈ (σ, τ) Continuous
∧	(∀x⦁x ∈ Space⋎T σ ⇒ f x = g x)
⇒	f ∈ (σ, τ) Continuous
⌝);
a(rewrite_tac[continuous_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[]);
a(LEMMA_T ⌜∀x⦁ x ∈ Space⋎T σ ∧ f x ∈ A ⇔ x ∈ Space⋎T σ ∧ g x ∈ A⌝
	asm_rewrite_thm_tac);
a(rewrite_tac[taut_rule ⌜∀p q r⦁ (p ∧ q ⇔ p ∧ r) ⇔ (p ⇒ (q ⇔ r))⌝]);
a(∀_tac THEN ⇒_tac THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));


=TEX

%%%%
%%%%
=SML

val ⦏same_on_space_continuous_thm1⦎ = save_thm ( "same_on_space_continuous_thm1", (
set_goal([], ⌜∀σ τ f g⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	(∀x⦁x ∈ Space⋎T σ ⇒ f x = g x)
⇒	(f ∈ (σ, τ) Continuous ⇔ g ∈ (σ, τ) Continuous)
⌝);
a(REPEAT strip_tac THEN all_fc_tac[same_on_space_continuous_thm]);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(all_fc_tac[same_on_space_continuous_thm]);
pop_thm()
));


=TEX

%%%%
%%%%
=SML

val ⦏subspace_product_continuous_thm⦎ = save_thm ( "subspace_product_continuous_thm", (
set_goal([], ⌜∀ρ σ τ f A B⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	¬(A × B) = {}
∧	A ⊆ Space⋎T ρ
∧	B ⊆ Space⋎T σ
⇒	(f ∈ ((A × B) ◁⋎T (ρ ×⋎T σ), τ) Continuous ⇔
	(∀a b⦁ a ∈ A ∧ b ∈ B ⇒ f(a, b) ∈ Space⋎T τ) ∧
	(∀a b E⦁ a ∈ A ∧ b ∈ B ∧ f(a, b) ∈ E ∧ E ∈ τ
		⇒	∃C D⦁ a ∈ C ∧ C ∈ ρ ∧ b ∈ D ∧ D ∈ σ ∧ ∀x y⦁
				x ∈ A ∩ C ∧ y ∈ B ∩ D ⇒ f(x, y) ∈ E))
⌝);
a(REPEAT_UNTIL is_⇔ strip_tac);
a(lemma_tac⌜ρ ×⋎T σ ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(rewrite_tac[continuous_def]);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm,
		product_topology_space_t_thm]);
a(PC_T1 "sets_ext1" rewrite_tac[×_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [1, 2, 5, 6] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(POP_ASM_T ante_tac);
a(lemma_tac⌜{(v, w)|v ∈ A ∧ w ∈ B} ◁⋎T ρ ×⋎T σ ∈ Topology⌝
	THEN1 (bc_thm_tac subspace_topology_thm THEN REPEAT strip_tac));
a(LIST_GET_NTH_ASM_T [8, 9] (PC_T1 "sets_ext1" all_fc_tac));
a(PC_T1 "sets_ext1" rewrite_tac[product_topology_def, subspace_topology_def, ×_def] THEN REPEAT strip_tac);
a(TOP_ASM_T (ante_tac o list_∀_elim[⌜a⌝, ⌜b⌝])
	THEN rewrite_tac[] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜A'⌝ THEN ∃_tac⌜B''⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 11 (ante_tac o list_∀_elim[⌜x⌝, ⌜y⌝])
	THEN rewrite_tac[] THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(DROP_NTH_ASM_T 6 (ante_tac o list_∀_elim[⌜Fst x⌝, ⌜Snd x⌝])
	THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a(rename_tac[(⌜A'⌝, "E")]
	THEN LEMMA_T ⌜
	{x |((Fst x ∈ A ∧ Snd x ∈ B) ∧ Fst x ∈ Space⋎T ρ ∧ Snd x ∈ Space⋎T σ) ∧ f x ∈ E} =
	{(c, d) | (c ∈ A ∧ c ∈ Space⋎T ρ) ∧ (d ∈ B ∧ d ∈  Space⋎T σ) ∧ f(c, d) ∈ E}⌝ rewrite_thm_tac
	THEN1 MERGE_PCS_T1 ["'pair", "sets_ext1"] prove_tac[]);
a(LEMMA_T⌜∀x⦁ x ∈ A ∧ x ∈ Space⋎T ρ ⇔ x ∈ A⌝ rewrite_thm_tac
	THEN1 (GET_NTH_ASM_T 6 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜∀x⦁ x ∈ B ∧ x ∈ Space⋎T σ ⇔ x ∈ B⌝ rewrite_thm_tac
	THEN1 (GET_NTH_ASM_T 5 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(lemma_tac⌜{(v, w)|v ∈ A ∧ w ∈ B} ◁⋎T ρ ×⋎T σ ∈ Topology⌝
	THEN1 (bc_thm_tac subspace_topology_thm THEN REPEAT strip_tac));
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[
	open_open_neighbourhood_thm]);
a(REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [6] all_fc_tac);
a(∃_tac⌜(A ∩ C) × (B ∩ D)⌝
	THEN once_rewrite_tac[taut_rule⌜∀p q⦁p ∧ q ⇔ q ∧ p⌝]
	THEN REPEAT strip_tac);
(* *** Goal "4.1" *** *)
a(MERGE_PCS_T1 ["'pair", "sets_ext1"] asm_rewrite_tac[×_def]);
(* *** Goal "4.2" *** *)
a(MERGE_PCS_T1 ["'pair", "sets_ext1"] rewrite_tac[×_def]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
(* *** Goal "4.3" *** *)
a(rewrite_tac[subspace_topology_def]);
a(∃_tac⌜C × D⌝
	THEN once_rewrite_tac[taut_rule⌜∀p q⦁p ∧ q ⇔ q ∧ p⌝]
	THEN REPEAT strip_tac);
(* *** Goal "4.3.1" *** *)
a(MERGE_PCS_T1 ["'pair", "sets_ext1"] asm_rewrite_tac[×_def]);
a(taut_tac);
(* *** Goal "4.3.2" *** *)
a(rewrite_tac[product_topology_def, ×_def]
	THEN REPEAT strip_tac);
a(∃_tac⌜C⌝ THEN ∃_tac⌜D⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
\subsection{Hausdorff Property}
=TEX
Any subspace of a Hausdorff space is Hausdorff:
%%%%
%%%%

=SML

val ⦏subspace_topology_hausdorff_thm⦎ = save_thm ( "subspace_topology_hausdorff_thm", (
set_goal([], ⌜∀τ X⦁
	τ ∈ Topology
∧	τ ∈ Hausdorff
⇒	(X ◁⋎T τ) ∈ Hausdorff
⌝);
a(rewrite_tac [hausdorff_def]);
a(REPEAT ∀_tac THEN ⇒_tac);
a(ALL_FC_T rewrite_tac [subspace_topology_space_t_thm]);
a(rewrite_tac[subspace_topology_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(∃_tac⌜A ∩ X⌝ THEN ∃_tac ⌜B ∩ X⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜A⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(∃_tac⌜B⌝ THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
A product Hausdorff spaces is Hausdorff:
%%%%
%%%%

=SML

val ⦏product_topology_hausdorff_thm⦎ = save_thm ( "product_topology_hausdorff_thm", (
set_goal([], ⌜∀σ τ⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	σ ∈ Hausdorff
∧	τ ∈ Hausdorff
⇒	(σ ×⋎T τ) ∈ Hausdorff
⌝);
a(rewrite_tac [hausdorff_def]);
a(REPEAT ∀_tac THEN ⇒_tac);
a(ALL_FC_T rewrite_tac [product_topology_space_t_thm]);
a(rewrite_tac[product_topology_def,
	pc_rule1"prop_eq_pair" prove_rule[]
		⌜∀p q⦁¬p = q ⇔ ¬Fst p = Fst q ∨ ¬Snd p = Snd q⌝,
	merge_pcs_rule1["'bin_rel", "sets_ext1"] prove_rule[]
		⌜∀p a b⦁p ∈ (a × b) ⇔ Fst p ∈ a ∧ Snd p ∈ b⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
a(∃_tac⌜A × Space⋎T τ⌝ THEN ∃_tac ⌜B × Space⋎T τ⌝);
a(rewrite_tac[merge_pcs_rule1["'bin_rel", "sets_ext1"] prove_rule[]
		⌜∀p a b⦁p ∈ (a × b) ⇔ Fst p ∈ a ∧ Snd p ∈ b⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(∃_tac⌜A⌝ THEN ∃_tac ⌜Space⋎T τ⌝ THEN ALL_FC_T asm_rewrite_tac[space_t_open_thm]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜B⌝ THEN ∃_tac ⌜Space⋎T τ⌝ THEN ALL_FC_T asm_rewrite_tac[space_t_open_thm]);
a(asm_rewrite_tac[merge_pcs_rule1["'bin_rel", "sets_ext1"] prove_rule[]
		⌜∀a b c d⦁ (a × b) ∩ (c × d) = ((a ∩ c) × (b ∩ d))  ∧ ({} × a) = {}⌝]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[]);
a(∃_tac⌜Space⋎T σ × A⌝ THEN ∃_tac ⌜Space⋎T σ × B⌝);
a(rewrite_tac[merge_pcs_rule1["'bin_rel", "sets_ext1"] prove_rule[]
		⌜∀p a b⦁p ∈ (a × b) ⇔ Fst p ∈ a ∧ Snd p ∈ b⌝]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(∃_tac⌜Space⋎T σ⌝ THEN ∃_tac ⌜A⌝ THEN ALL_FC_T asm_rewrite_tac[space_t_open_thm]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜Space⋎T σ⌝ THEN ∃_tac ⌜B⌝ THEN ALL_FC_T asm_rewrite_tac[space_t_open_thm]);
a(asm_rewrite_tac[merge_pcs_rule1["'bin_rel", "sets_ext1"] prove_rule[]
		⌜∀a b c d⦁ (a × b) ∩ (c × d) = ((a ∩ c) × (b ∩ d))  ∧ (a × {}) = {}⌝]);
pop_thm()
));

=TEX
Puncturing a Hausdorff space at a single point leaves an open set:
%%%%
%%%%

=SML

val ⦏punctured_hausdorff_thm⦎ = save_thm ( "punctured_hausdorff_thm", (
set_goal([], ⌜∀τ X x⦁
	τ ∈ Topology
∧	τ ∈ Hausdorff
∧	X ⊆ Space⋎T τ
∧	x ∈ Space⋎T τ
⇒	(X \ {x}) ∈ (X ◁⋎T τ)
⌝);
a(rewrite_tac [hausdorff_def] THEN REPEAT strip_tac);
a(lemma_tac ⌜ (X ◁⋎T τ) ∈ Topology ⌝
	THEN1 ALL_FC_T rewrite_tac[subspace_topology_thm]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[
	open_open_neighbourhood_thm]);
a(rewrite_tac[subspace_topology_def]
	THEN REPEAT strip_tac);
a(all_asm_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀x X S⦁x ∈ X ∧ X ⊆ S ⇒ x ∈ S⌝]);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(∃_tac⌜A ∩ X⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN POP_ASM_T ante_tac
	THEN DROP_ASMS_T discard_tac);
a(PC_T "sets_ext1" contr_tac
	THEN all_var_elim_asm_tac1
	THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
\subsection{Compactness}
%%%%
%%%%

%%%%
%%%%

=SML

val ⦏compact_topological_thm⦎ = save_thm ( "compact_topological_thm", (
set_goal([], ⌜∀τ X⦁
	τ ∈ Topology
⇒	(X ∈ τ Compact ⇔ X ∈ (X ◁⋎T τ) Compact)⌝);
a(rewrite_tac[compact_def] THEN PC_T1 "sets_ext1" REPEAT ∀_tac THEN ⇒_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[subspace_topology_space_t_thm]);
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b⦁a ⊆ a ∩ b ⇔ a ⊆ b⌝]);
a(rewrite_tac[subspace_topology_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜X ⊆ ⋃{B | B ∈ τ ∧ B ∩ X ∈ V} ⌝ THEN1 PC_T1 "sets_ext" REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(LIST_GET_NTH_ASM_T [1, 2, 3] (PC_T1 "sets_ext1" (MAP_EVERY strip_asm_tac)));
a(all_asm_fc_tac[]);
a(LIST_GET_NTH_ASM_T [3] all_fc_tac THEN all_var_elim_asm_tac1);
a(∃_tac⌜B⌝ THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜{B | B ∈ τ ∧ B ∩ X ∈ V} ⊆ τ⌝ THEN1 PC_T1 "sets_ext" prove_tac[]);
a(all_asm_fc_tac[]);
a(ante_tac(list_∀_elim[⌜λB⦁B ∩ X⌝, ⌜W⌝]finite_image_thm));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac ⌜{C|∃ B⦁ B ∈ W ∧ C = B ∩ X}⌝ THEN REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(PC_T "sets_ext1"  strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(LIST_GET_NTH_ASM_T [5] (PC_T1 "sets_ext1" all_fc_tac));
(* *** Goal "1.2.2" *** *)
a(PC_T "sets_ext1"  strip_tac THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [3] (PC_T1 "sets_ext1" all_fc_tac));
a(∃_tac⌜s ∩ X⌝ THEN REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(lemma_tac⌜X ⊆ ⋃{C | ∃B⦁ B ∈ V ∧ C = B ∩ X} ⌝ THEN1 PC_T1 "sets_ext" REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LIST_GET_NTH_ASM_T [2] (PC_T1 "sets_ext1" all_fc_tac));
a(∃_tac⌜s ∩ X⌝ THEN REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜{C | ∃B⦁ B ∈ V ∧ C = B ∩ X} ⊆ {A|∃ B⦁ B ∈ τ ∧ A = B ∩ X}⌝
	THEN1 (PC_T "sets_ext" strip_tac THEN REPEAT strip_tac));
(* *** Goal "2.2.1" *** *)
a(all_var_elim_asm_tac1 THEN ∃_tac ⌜B⌝ THEN
	REPEAT strip_tac THEN PC_T1 "sets_ext1" all_asm_fc_tac[]);
(* *** Goal "2.2.2" *** *)
a(all_asm_fc_tac[]);
a(lemma_tac⌜∃f⦁∀C⦁ C ∈ W ⇒ f C ∈ V ∧ C = f C ∩ X⌝ THEN1 prove_∃_tac);
(* *** Goal "2.2.2.1" *** *)
a(REPEAT strip_tac);
a(cases_tac⌜¬C' ∈ W⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 (PC_T1 "sets_ext1" strip_asm_tac));
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(all_var_elim_asm_tac1 THEN ∃_tac⌜B⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2" *** *)
a(strip_asm_tac(list_∀_elim[⌜f⌝, ⌜W⌝]finite_image_thm));
a(∃_tac⌜{y|∃ x⦁ x ∈ W ∧ y = f x}⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(PC_T "sets_ext1"  strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "2.2.2.2.2" *** *)
a(PC_T "sets_ext1"  strip_tac THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (PC_T1 "sets_ext1" strip_asm_tac));
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(∃_tac⌜f s⌝ THEN asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(DROP_NTH_ASM_T 4 ante_tac);
a(POP_ASM_T (fn th => conv_tac(LEFT_C(once_rewrite_conv[th]))));
a(REPEAT strip_tac THEN rename_tac[]);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏image_compact_thm⦎ = save_thm ( "image_compact_thm", (
set_goal([], ⌜∀f C σ τ⦁
	f ∈ (σ, τ) Continuous
∧	C ∈ σ Compact
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	{y | ∃x⦁ x ∈ C ∧ y = f x} ∈ τ Compact
⌝);
a(rewrite_tac[compact_def, continuous_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac );
a(all_var_elim_asm_tac1 THEN PC_T1 "sets_ext1" all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜{A | ∃B⦁ B ∈ V ∧ A = {x|x ∈ Space⋎T σ ∧ f x ∈ B}} ⊆ σ⌝);
(* *** Goal "2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN GET_NTH_ASM_T 8 bc_thm_tac);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜C ⊆ ⋃{A | ∃B⦁ B ∈ V ∧ A = {x|x ∈ Space⋎T σ ∧ f x ∈ B}}⌝);
(* *** Goal "2.2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(LEMMA_T⌜f x ∈ {y|∃ x⦁ x ∈ C ∧ y = f x}⌝  asm_tac THEN1
	(REPEAT strip_tac THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac));
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(∃_tac⌜{x|x ∈ Space⋎T σ ∧ f x ∈ s}⌝ THEN REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a(all_asm_fc_tac[]);
a(lemma_tac⌜∃h⦁∀A⦁ A ∈ W ⇒ h A ∈ V ∧ A = {x | x ∈ Space⋎T σ ∧ f x ∈ h A}⌝
	THEN1 prove_∃_tac THEN REPEAT strip_tac);
 (* *** Goal "2.2.2.1" *** *)
a(cases_tac ⌜A' ∈ W⌝  THEN asm_rewrite_tac[]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(∃_tac⌜B⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2" *** *)
a(strip_asm_tac (list_∀_elim[⌜h⌝, ⌜W⌝] finite_image_thm));
a(∃_tac⌜{y|∃ x⦁ x ∈ W ∧ y = h x}⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "2.2.2.2.2" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 7 discard_tac);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀b⦁x' ∈ C ∧ C ⊆ b ⇒ x' ∈ b⌝]);
a(∃_tac⌜h s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.2.1" *** *)
a(all_asm_fc_tac[]);
a(POP_ASM_T (fn th => DROP_NTH_ASM_T 5 (ante_tac o once_rewrite_rule[th])));
a(REPEAT strip_tac);
(* *** Goal "2.2.2.2.2.2" *** *)
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏∪_compact_thm⦎ = save_thm ( "∪_compact_thm", (
set_goal([], ⌜∀C D σ⦁
	C ∈ σ Compact
∧	D ∈ σ Compact
∧	σ ∈ Topology
⇒	C ∪ D ∈ σ Compact
⌝);
a(rewrite_tac[compact_def] THEN REPEAT strip_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ∪ b ⊆ c ⇒ a ⊆ c ∧ b ⊆ c⌝]);
a(all_asm_fc_tac[]);
a(∃_tac ⌜W ∪ W'⌝ THEN
	rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b⦁⋃(a ∪ b) = ⋃a ∪ ⋃b⌝]
	THEN ALL_FC_T rewrite_tac[
	pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ c ∧ b ⊆ c ⇒ a ∪ b ⊆ c⌝,
	pc_rule1"sets_ext1" prove_rule[]⌜∀a b c d⦁a ⊆ c ∧ b ⊆ d ⇒ a ∪ b ⊆ d ∪ c⌝,
	conv_rule(ONCE_MAP_C eq_sym_conv) ∪_finite_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏compact_closed_lemma⦎ = (* not saved *) snd ( "compact_closed_lemma", (
set_goal([], ⌜∀τ V p⦁
	τ ∈ Topology
∧	V ⊆ τ
∧	V ∈ Finite
∧	p ∈ Space⋎T τ
∧	(∀A⦁ A ∈ V ⇒ ∃B⦁ B ∈ τ ∧ p ∈ B ∧ A ∩ B = {})
⇒	∃B⦁ B ∈ τ ∧ p ∈ B ∧ B ∩ ⋃V = {}⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜
	∃b⦁∀A⦁A ∈ V ⇒ b A ∈ τ ∧ p ∈ b A ∧ A ∩ b A = {}
⌝ THEN1 prove_∃_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(cases_tac⌜¬A' ∈ V⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(cases_tac⌜⋃V = {}⌝);
(* *** Goal "2.1" *** *)
a(∃_tac ⌜Space⋎T τ⌝ THEN ALL_FC_T asm_rewrite_tac[space_t_open_thm]);
(* *** Goal "2.2" *** *)
a(lemma_tac ⌜⋂{y|∃ x⦁ x ∈ V ∧ y = b x} ∈ τ⌝ THEN1 bc_thm_tac finite_⋂_open_thm);
(* *** Goal "2.2.1" *** *)
a(asm_rewrite_tac[] THEN ALL_FC_T rewrite_tac[finite_image_thm]);
a(REPEAT strip_tac THEN PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "2.2.1.1" *** *)
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "2.2.1.2" *** *)
a(rewrite_tac[]);
a(cases_tac⌜V = {}⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(POP_ASM_T (PC_T1 "sets_ext1" strip_asm_tac));
a(∃_tac⌜b x⌝ THEN ∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(∃_tac⌜⋂{y|∃ x⦁ x ∈ V ∧ y = b x}⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(PC_T "sets_ext1" strip_tac THEN rewrite_tac[∩_def, ⋂_def, ⋃_def]);
a(REPEAT strip_tac);
a(∃_tac⌜b s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(∃_tac⌜ s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.2" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏compact_closed_thm⦎ = save_thm ( "compact_closed_thm", (
set_goal([], ⌜∀τ C⦁
	τ ∈ Topology
∧	τ ∈ Hausdorff
∧	C ∈ τ Compact
⇒	C ∈ τ Closed⌝);
a(REPEAT strip_tac);
a(ALL_FC_T1 fc_⇔_canon  rewrite_tac[closed_open_neighbourhood_thm]);
a(once_rewrite_tac[prove_rule[]⌜∀p1 p2⦁ p1 ∧ p2 ⇔ p1 ∧ (p1 ⇒ p2)⌝]);
a(REPEAT strip_tac THEN1
	(POP_ASM_T ante_tac THEN prove_tac[compact_def]));
a(lemma_tac⌜C ⊆ ⋃ {A | A ∈ τ ∧ ∃B⦁B ∈ τ ∧ x ∈ B ∧ A ∩ B = {}}⌝);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[hausdorff_def]));
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(lemma_tac⌜x' ∈ Space⋎T τ⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜¬x' = x⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac1));
a(all_asm_fc_tac[]);
a(∃_tac⌜A⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[compact_def]));
a(lemma_tac⌜{A | A ∈ τ ∧ ∃B⦁B ∈ τ ∧ x ∈ B ∧ A ∩ B = {}} ⊆ τ⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(all_asm_fc_tac[]);
a(lemma_tac⌜W ⊆ τ⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜∀ A⦁ A ∈ W ⇒ (∃ B⦁ B ∈ τ ∧ x ∈ B ∧ A ∩ B = {})⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac);
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
a(∃_tac⌜B⌝ THEN PC_T1 "sets_ext1" asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(all_fc_tac[compact_closed_lemma]);
a(∃_tac⌜B⌝ THEN  asm_rewrite_tac[]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[] ⌜∀X⦁ C ⊆ X ∧ B ∩ X = {} ⇒ B ∩ C = {}⌝]);
pop_thm()
));

=TEX
%%%%
%%%%
A closed subset of a compact set is closed:
=SML

val ⦏closed_⊆_compact_thm⦎ = save_thm ( "closed_⊆_compact_thm", (
set_goal([], ⌜∀τ B C⦁
	τ ∈ Topology
∧	τ ∈ Hausdorff
∧	C ∈ τ Compact
∧	B ∈ τ Closed
∧	B ⊆ C
⇒	B ∈ τ Compact⌝);
a(REPEAT strip_tac THEN GET_NTH_ASM_T 3 ante_tac);
a(rewrite_tac[compact_def] THEN REPEAT strip_tac
	THEN all_fc_tac[closed_open_complement_thm]);
a(all_fc_tac[compact_closed_thm]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀t a x⦁a ⊆ t ∧ x ∈ t ⇒ a ∪ {x} ⊆ t⌝]);
a(LEMMA_T⌜∀c b s v⦁ c ⊆ s ∧ b ⊆ ⋃v ⇒ c ⊆ ⋃(v ∪ {s \ b})⌝
	(fn th => all_fc_tac[∀_elim⌜C⌝ th]));
(* *** Goal "1" *** *)
a(DROP_ASMS_T discard_tac THEN PC_T1 "sets_ext1" prove_tac[]);
a(cases_tac⌜x ∈ b⌝ THEN all_asm_fc_tac[]);
(* *** Goal "1.1" *** *)
a(contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜s \ b⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [8] all_fc_tac);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀w v x⦁ w ⊆ v ∪ {x} ⇒ w \ {x} ⊆ v ∧ w \ {x} ⊆ w⌝]);
a(all_fc_tac[⊆_finite_thm]);
a(∃_tac⌜W \ {Space⋎T τ \ B}⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜∀c w s b⦁ b ⊆ c ∧ c ⊆ ⋃w ⇒ b ⊆ ⋃(w \ {s \ b})⌝
	(fn th => bc_thm_tac (∀_elim⌜C⌝th)
		THEN contr_tac THEN all_asm_fc_tac[]));
a(DROP_ASMS_T discard_tac THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜s'⌝ THEN contr_tac THEN all_var_elim_asm_tac1);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏compact_basis_thm⦎ = save_thm ( "compact_basis_thm", (
set_goal([], ⌜∀U τ X⦁
	τ ∈ Topology
∧	U ⊆ τ
∧	(∀A⦁∀x⦁ x ∈ A ∧ A ∈ τ ⇒ ∃B⦁ x ∈ B ∧ B ⊆ A ∧ B ∈ U)
∧	X ⊆ Space⋎T τ
∧	(∀V⦁ V ⊆ U ∧ X ⊆ ⋃ V ⇒ ∃ W⦁ W ⊆ V ∧ W ∈ Finite ∧ X ⊆ ⋃ W)
⇒	X ∈ τ Compact
⌝);
a(rewrite_tac[compact_def] THEN REPEAT strip_tac);
a(lemma_tac⌜{B | B ∈ U ∧ ∃ A⦁ A ∈ V ∧ B ⊆ A} ⊆ U⌝ THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(lemma_tac⌜X ⊆ ⋃{B | B ∈ U ∧ ∃ A⦁ A ∈ V ∧ B ⊆ A}⌝
	THEN1 PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 3 (fn th => PC_T1 "sets_ext1" all_fc_tac[th]));
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x a⦁x ∈ a ∧ a ⊆ τ ⇒ x ∈ τ⌝]);
a(DROP_NTH_ASM_T 9 (fn th => all_fc_tac[th]));
a(∃_tac⌜B⌝ THEN REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 5 (fn th => all_fc_tac[th]));
a(lemma_tac⌜∃f⦁∀B⦁B ∈ W ⇒ f B ∈ V ∧ B ⊆ f B⌝ THEN1 prove_∃_tac);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac THEN cases_tac⌜B' ∈ W⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 (fn th => all_fc_tac[pc_rule1 "sets_ext1" once_rewrite_rule[] th]));
a(∃_tac ⌜A⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(ante_tac(list_∀_elim[⌜f⌝, ⌜W⌝] finite_image_thm) THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
a(∃_tac ⌜{y|∃ x⦁ x ∈ W ∧ y = f x}⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "2.2.2" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (fn th => all_fc_tac[pc_rule1 "sets_ext1" once_rewrite_rule[] th]));
a(∃_tac ⌜f s⌝ THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a(PC_T1 "sets_ext" asm_prove_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(∃_tac ⌜s⌝ THEN asm_rewrite_tac[] );
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏compact_basis_product_topology_thm⦎ = save_thm ( "compact_basis_product_topology_thm", (
set_goal([], ⌜∀σ τ X⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	X ⊆ Space⋎T (σ ×⋎T τ)
∧	(∀V⦁ 	V ⊆ (σ ×⋎T τ)
	∧	(∀D⦁ D ∈ V ⇒ ∃B C⦁ B ∈ σ ∧ C ∈ τ ∧ D = (B × C))
	∧	X ⊆ ⋃ V
	⇒	∃ W⦁ W ⊆ V ∧ W ∈ Finite ∧ X ⊆ ⋃ W)
⇒	X ∈ (σ ×⋎T τ) Compact
⌝);
a(REPEAT strip_tac THEN bc_thm_tac compact_basis_thm);
a(ALL_FC_T asm_rewrite_tac[product_topology_thm]);
a(∃_tac⌜{D | ∃B C⦁ B ∈ σ ∧ C ∈ τ ∧ D = (B × C)}⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[product_topology_def] THEN PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(∃_tac⌜B⌝ THEN ∃_tac⌜C⌝ THEN asm_rewrite_tac[]);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[×_def]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[product_topology_def] THEN REPEAT strip_tac);
a(POP_ASM_T (ante_tac o list_∀_elim[⌜Fst x⌝, ⌜Snd x⌝]));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜A' × B⌝ THEN REPEAT strip_tac THEN1 asm_rewrite_tac[×_def]);
a(∃_tac⌜A'⌝ THEN ∃_tac⌜B⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 2 (fn th => ante_tac(pc_rule1 "sets_ext1" once_rewrite_rule[] th)));
a(rewrite_tac[taut_rule⌜∀p1 p2⦁(p1 ⇒ p2 ∧ p1) ⇔ p1 ⇒ p2⌝]);
a(REPEAT strip_tac THEN PC_T "sets_ext" strip_tac THEN REPEAT strip_tac);
a(all_asm_fc_tac[] THEN all_var_elim_asm_tac1);
a(rewrite_tac[product_topology_def] THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[×_def]));
a(∃_tac⌜B⌝ THEN ∃_tac⌜C⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏compact_product_lemma⦎ = (* not saved *) snd ( "compact_product_lemma", (
set_goal([], ⌜∀σ τ W x⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	x ∈ Space⋎T σ
∧	W ∈ Finite
∧	(∀D⦁D ∈ W ⇒ ∃B C⦁ x ∈ B ∧ B ∈ σ ∧ C ∈ τ ∧ D = (B × C))
⇒	∃A⦁ x ∈ A ∧ A ∈ σ ∧ ∀t y⦁(x, y) ∈ ⋃W ∧ t ∈ A ⇒ (t, y) ∈ ⋃W⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀V⦁ V ∈ Finite ∧ V ⊆ W ⇒
	∃A⦁ x ∈ A ∧ A ∈ σ ∧ ∀t y⦁(x, y) ∈ ⋃V ∧ t ∈ A ⇒ (t, y) ∈ ⋃V⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(finite_induction_tac ⌜V⌝);
(* *** Goal "1.1" *** *)
a(rewrite_tac[enum_set_clauses]);
a(all_fc_tac[space_t_open_thm] THEN contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a(LEMMA_T ⌜¬{x'} ∪ V ⊆ W⌝ rewrite_thm_tac);
a(GET_NTH_ASM_T 2 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.3" *** *)
a(REPEAT strip_tac);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[] ⌜∀x a b⦁ {x} ∪ a ⊆ b ⇒ x ∈ b⌝]);
a(LIST_DROP_NTH_ASM_T [8] all_fc_tac);
a(all_var_elim_asm_tac1 THEN rewrite_tac[enum_set_clauses,
	pc_rule1"sets_ext1" prove_rule[]⌜∀a v⦁⋃(a ∪ v) = ⋃a ∪ ⋃v⌝]);
a(∃_tac ⌜B ∩ A⌝ THEN REPEAT strip_tac);
(* *** Goal "1.3.1" *** *)
a(bc_thm_tac ∩_open_thm THEN REPEAT strip_tac);
(* *** Goal "1.3.2" *** *)
a(swap_nth_asm_concl_tac 1 THEN LIST_DROP_NTH_ASM_T [3, 4] (MAP_EVERY ante_tac));
a(rewrite_tac[×_def] THEN prove_tac[]);
(* *** Goal "1.3.3" *** *)
a(LEMMA_T ⌜(x, y) ∈ ⋃V⌝ asm_tac THEN1
	(LIST_DROP_NTH_ASM_T [5, 4] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext" prove_tac[]));
a(LIST_DROP_NTH_ASM_T [13] all_fc_tac);
a(contr_tac THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏product_compact_thm⦎ = save_thm ( "product_compact_thm", (
set_goal([], ⌜∀X : 'a SET; Y : 'b SET; σ τ ⦁
	X ∈ σ Compact
∧	Y ∈ τ Compact
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	(X × Y) ∈ (σ ×⋎T τ) Compact⌝);
a(REPEAT strip_tac THEN bc_thm_tac compact_basis_product_topology_thm);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[product_topology_space_t_thm]);
a(all_asm_ante_tac THEN rewrite_tac[compact_def] THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [4, 6] (MAP_EVERY ante_tac) THEN
	MERGE_PCS_T1 ["'bin_rel", "sets_ext1"] prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac ⌜∃W⦁∀x⦁ x ∈ X ⇒
	W x ⊆ V ∧ W x ∈ Finite ∧ (∀y⦁y ∈ Y ⇒ (x, y) ∈ ⋃(W x)) ∧
	∀D⦁ D ∈ W x ⇒ (∃ B C⦁ x ∈ B ∧ B ∈ σ ∧ C ∈ τ ∧ D = (B × C))⌝
	THEN1 prove_∃_tac THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(cases_tac ⌜x' ∈ X⌝ THEN asm_rewrite_tac[]);
a(lemma_tac ⌜x' ∈ Space⋎T σ⌝ THEN1
	(LIST_DROP_NTH_ASM_T [1, 8] (MAP_EVERY ante_tac) THEN
	rewrite_tac[compact_def] THEN PC_T1 "sets_ext1" prove_tac[]));
a(strip_asm_tac (list_∀_elim[⌜σ⌝, ⌜τ⌝, ⌜x'⌝] right_product_inj_continuous_thm));
a(lemma_tac ⌜(σ ×⋎T τ) ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(ante_tac (list_∀_elim[⌜λy:'b⦁(x', y)⌝, ⌜Y⌝, ⌜τ⌝, ⌜σ ×⋎T τ⌝] image_compact_thm));
a(asm_rewrite_tac[compact_def] THEN REPEAT strip_tac);
a(lemma_tac⌜x' ∈ X ⇒ {y|∃ x⦁ x ∈ Y ∧ Fst y = x' ∧ Snd y = x} ⊆ (X × Y)⌝
	THEN1 (MERGE_PCS_T1 ["'bin_rel", "sets_ext" ] prove_tac[]
		THEN all_var_elim_asm_tac1));
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(POP_ASM_T (PC_T1 "sets_ext1" strip_asm_tac));
a(∃_tac ⌜{A | A ∈ W ∧ ∃y⦁(x', y) ∈ A}⌝ THEN PC_T1 "basic_hol" REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(DROP_NTH_ASM_T 3 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac ⌜W⌝ THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.3" *** *)
a(lemma_tac⌜(x', y) ∈ ⋃W⌝);
(* *** Goal "2.1.3.1" *** *)
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
a(∃_tac⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.3.2" *** *)
a(REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN asm_rewrite_tac[]);
a(∃_tac⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.4" *** *)
a(lemma_tac⌜D ∈ V⌝ THEN1 (
	LIST_DROP_NTH_ASM_T [1, 4] (MAP_EVERY ante_tac)
		THEN PC_T1 "sets_ext" prove_tac[]));
a(LIST_DROP_NTH_ASM_T [14] all_fc_tac);
a(∃_tac⌜B⌝ THEN ∃_tac⌜C⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 ante_tac THEN all_var_elim_asm_tac1);
a(prove_tac[×_def]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜X ⊆ ⋃{A | A ∈ σ ∧∃x⦁x ∈ X ∧  x ∈ A ∧ ∀t y⦁t ∈ A ∧ y ∈ Y ⇒ (t, y) ∈ ⋃(W x)}⌝
	THEN1 PC_T1 "sets_ext" REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(lemma_tac ⌜x ∈ Space⋎T σ⌝ THEN1
	(LIST_DROP_NTH_ASM_T [1, 9] (MAP_EVERY ante_tac) THEN
	rewrite_tac[compact_def] THEN PC_T1 "sets_ext1" prove_tac[]));
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜x⌝));
a(all_fc_tac[compact_product_lemma]);
a(∃_tac⌜A⌝ THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN PC_T1 "basic_hol" REPEAT strip_tac);
a(PC_T1 "basic_hol" (LIST_DROP_NTH_ASM_T [7])  all_fc_tac);
a(PC_T1 "basic_hol" (LIST_DROP_NTH_ASM_T [4])  all_fc_tac);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜{A | A ∈ σ ∧∃x⦁x ∈ X ∧  x ∈ A ∧ ∀t y⦁t ∈ A ∧ y ∈ Y ⇒ (t, y) ∈ ⋃(W x)} ⊆ σ⌝
	THEN1 PC_T1 "sets_ext" prove_tac[]);
a(GET_NTH_ASM_T 10 (fn th => all_fc_tac[rewrite_rule[compact_def] th]));
a(LIST_DROP_NTH_ASM_T [4, 5, 7, 8] discard_tac);
a(lemma_tac⌜∃U⦁∀A⦁A ∈ W' ⇒ (∀ t y⦁ t ∈ A ∧ y ∈ Y ⇒ (t, y) ∈ ⋃ (U A)) ∧ U A ⊆ V ∧ U A ∈ Finite⌝
	THEN1 prove_∃_tac);
(* *** Goal "2.2.2.1" *** *)
a(REPEAT strip_tac);
a(cases_tac⌜A' ∈ W'⌝ THEN asm_rewrite_tac[]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(∃_tac⌜W x⌝ THEN  POP_ASM_T ante_tac THEN ALL_ASM_FC_T rewrite_tac[] THEN taut_tac);
(* *** Goal "2.2.2.2" *** *)
a(∃_tac⌜⋃{y|∃ x⦁ x ∈ W' ∧ y = U x}⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [3] all_asm_fc_tac);
a(LIST_DROP_NTH_ASM_T [2, 4] (MAP_EVERY ante_tac) THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.2.2.2" *** *)
a(ante_tac (list_∀_elim[⌜U⌝, ⌜W'⌝] finite_image_thm) THEN asm_rewrite_tac[] THEN strip_tac);
a(bc_thm_tac ⋃_finite_thm THEN REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(all_asm_fc_tac[]);
(* *** Goal "2.2.2.2.3" *** *)
a(MERGE_PCS_T1 ["'bin_rel", "sets_ext1"] REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] (PC_T1"sets_ext1" all_fc_tac));
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(∃_tac⌜s'⌝ THEN REPEAT strip_tac);
a(∃_tac⌜U s⌝ THEN REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
We now look at sequential compactness. To show that compact spaces are sequentially compact
we use the following purely combinatorial lemma:
%%%%
%%%%

=SML

val ⦏compact_sequentially_compact_lemma⦎ = (* not saved *) snd ( "compact_sequentially_compact_lemma", (
set_goal([], ⌜∀W s⦁
	W ∈ Finite
∧	(∀m:ℕ⦁s m ∈ ⋃W)
⇒	∃A⦁A ∈ W ∧ ∀m⦁∃n⦁m ≤ n ∧ s n ∈ A
⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜∀V s⦁
	V ∈ Finite
∧	(∀m:ℕ⦁s m ∈ ⋃V)
∧	V ⊆ W
⇒	∃A⦁A ∈ W ∧ ∀m⦁∃n⦁m ≤ n ∧ s n ∈ A
⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN POP_ASM_T ante_tac THEN POP_ASM_T ante_tac);
a(intro_∀_tac(⌜s'⌝, ⌜s'⌝));
a(finite_induction_tac⌜V⌝ THEN
	rewrite_tac[⋃_enum_set_clauses,
		pc_rule1"sets_ext1" prove_rule[]⌜∀u v⦁⋃(u ∪ v) = ⋃u ∪ ⋃v⌝]);
a(REPEAT strip_tac);
a(cases_tac⌜∀ m⦁ ∃ n⦁ m ≤ n ∧ s' n ∈ x⌝);
(* *** Goal "1.1" *** *)
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 2 ante_tac THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 5 (ante_tac o ∀_elim⌜λn⦁s'(m + n)⌝));
a(ALL_FC_T rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ∪ b ⊆ c ⇒ b ⊆ c⌝]);
a(LEMMA_T ⌜∀ m'⦁ s' (m + m') ∈ ⋃ V⌝ rewrite_thm_tac THEN1 ∀_tac);
(* *** Goal "1.2.1" *** *)
a(bc_thm_tac (pc_rule1"sets_ext1" prove_rule[]⌜∀a b y⦁¬y ∈ a ∧ y ∈ a ∪ b ⇒ y ∈ b⌝));
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
a(spec_nth_asm_tac 1 ⌜m + m'⌝);
(* *** Goal "1.2.2" *** *)
a(REPEAT strip_tac THEN ∃_tac⌜A⌝ THEN REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜m'⌝);
a(∃_tac⌜m + n⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 1 (ante_tac o ∀_elim⌜W⌝) THEN rewrite_tac[] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(∃_tac⌜A⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
We can now show that compact spaces are sequentially compact. This is useful
in proving the existence of Lebesgue numbers for coverings of compact subspaces
of the real line or the plane.

%%%%
%%%%

=SML

val ⦏compact_sequentially_compact_thm⦎ = save_thm ( "compact_sequentially_compact_thm", (
set_goal([], ⌜∀τ X s⦁
	τ ∈ Topology
∧	X ∈ τ Compact
∧	(∀m:ℕ⦁s m ∈ X)
⇒	∃x⦁x ∈ X ∧ (∀A⦁A ∈ τ ∧ x ∈ A ⇒ ∀m⦁∃n⦁m ≤ n ∧ s n ∈ A)
⌝);
a(rewrite_tac[compact_def] THEN contr_tac);
a(lemma_tac⌜X ⊆ ⋃{A | A ∈ τ ∧ ∃x⦁x ∈ A ∧ x ∈ X ∧ ∃m⦁∀n⦁m ≤ n ⇒ ¬s n ∈ A}⌝);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜x⌝);
a(∃_tac⌜A⌝ THEN asm_rewrite_tac[]);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
a(∃_tac⌜m⌝ THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜n⌝);
(* *** Goal "2" *** *)
a(lemma_tac⌜{A | A ∈ τ ∧ ∃x⦁x ∈ A ∧ x ∈ X ∧ ∃m⦁∀n⦁m ≤ n ⇒ ¬s n ∈ A} ⊆ τ⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(lemma_tac⌜∀m⦁s m ∈ ⋃W⌝ THEN1
	all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b⦁a ⊆ b ∧ (∀ m⦁ s m ∈ a) ⇒ (∀ m⦁ s m ∈ b)⌝]);
a(all_fc_tac[compact_sequentially_compact_lemma]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀y a b⦁y ∈ a ∧ a ⊆ b ⇒ y ∈ b⌝]);
a(spec_nth_asm_tac 5 ⌜m⌝);
a(LIST_DROP_NTH_ASM_T [3] all_asm_fc_tac);
pop_thm()
));

=TEX
\subsection{Connectedness}
%%%%
%%%%

=SML

val ⦏connected_topological_thm⦎ = save_thm ( "connected_topological_thm", (
set_goal([], ⌜∀τ X⦁
	τ ∈ Topology
⇒	(X ∈ τ Connected ⇔ X ∈ (X ◁⋎T τ) Connected)⌝);
a(rewrite_tac[connected_def] THEN PC_T1 "sets_ext1" REPEAT ∀_tac THEN ⇒_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[subspace_topology_space_t_thm]);
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b⦁a ⊆ a ∩ b ⇔ a ⊆ b⌝]);
a(rewrite_tac[subspace_topology_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1);
a(lemma_tac⌜X ⊆ B'  ∪ B''⌝ THEN1
	(GET_NTH_ASM_T 3 ante_tac THEN  PC_T1 "sets_ext" prove_tac[]));
a(DROP_NTH_ASM_T 3 ante_tac THEN
	rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ∩ (b ∩ a) ∩ c ∩ a = a ∩ b ∩ c⌝]);
a(REPEAT strip_tac);
a(lemma_tac⌜¬X ⊆ B' ⌝ THEN1
	(GET_NTH_ASM_T 3 ante_tac THEN  PC_T1 "sets_ext" prove_tac[]));
a(all_asm_fc_tac[]);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "2" *** *)
a(list_spec_nth_asm_tac 6 [⌜B ∩ X⌝, ⌜C ∩ X⌝]);
(* *** Goal "2.1" *** *)
a(list_spec_nth_asm_tac 1 [⌜B⌝]);
(* *** Goal "2.2" *** *)
a(list_spec_nth_asm_tac 1 [⌜C⌝]);
(* *** Goal "2.3" *** *)
a(i_contr_tac THEN LIST_DROP_NTH_ASM_T [1, 4] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.4" *** *)
a(i_contr_tac THEN LIST_DROP_NTH_ASM_T [1, 3] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.5" *** *)
a(i_contr_tac THEN LIST_DROP_NTH_ASM_T [1, 2] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.6" *** *)
a(LIST_DROP_NTH_ASM_T [1] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏connected_closed_thm⦎ = save_thm ( "connected_closed_thm", (
set_goal([], ⌜∀τ X⦁
	τ Connected =
	{A |A ⊆ Space⋎T τ ∧ ∀ B C ⦁ B ∈ τ Closed ∧ C ∈ τ Closed ∧ A ⊆ B ∪ C ∧ A ∩ B ∩ C = {} ⇒ A ⊆ B ∨ A ⊆ C}⌝);
a(REPEAT strip_tac THEN rewrite_tac[connected_def, closed_def]);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1 THEN rename_tac[(⌜B'⌝, "c"), (⌜B''⌝, "b")]);
a(DROP_NTH_ASM_T 2 ante_tac);
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule [] ⌜∀A B C⦁ (A \ B) ∩ (A \ C) = A \ (B ∪ C)⌝]
	THEN strip_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule [] ⌜∀S U X⦁ X ⊆ S ∧ X ∩ (S \ U) = {} ⇒ X ⊆ U⌝]);
a(DROP_NTH_ASM_T 4 ante_tac);
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule [] ⌜∀A B C⦁ (A \ B) ∪ (A \ C) = A \ (B ∩ C)⌝]
	THEN strip_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule [] ⌜∀S I X⦁ X ⊆ S \ I  ⇒ X ∩ I = {}⌝]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule [] ⌜∀S X⦁ X ⊆ S \ (c ∩ b) ∧ ¬X ⊆ S \ c ⇒ ¬X ⊆ b⌝]);
a(list_spec_nth_asm_tac 9 [⌜c⌝, ⌜b⌝]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule [] ⌜∀S X⦁ X ⊆ S \ (c ∩ b) ∧ X ⊆  c ⇒ X ⊆ S \ b⌝]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜x ⊆ Space⋎T τ \ (B ∩ C)⌝ ante_tac THEN1
	(LIST_GET_NTH_ASM_T [2, 7] (MAP_EVERY ante_tac)
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule [] ⌜∀A B C⦁A \ (B ∩ C) =  (A \ B) ∪ (A \ C) ⌝]
	THEN strip_tac);
a(LEMMA_T⌜x ∩ (Space⋎T τ \ (B ∪ C)) = {}⌝ ante_tac THEN1
	(LIST_GET_NTH_ASM_T [4, 8] (MAP_EVERY ante_tac)
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule [] ⌜∀A B C⦁A \ (B ∪ C) =  (A \ B) ∩ (A \ C) ⌝]
	THEN strip_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule []
	⌜∀S⦁ x ⊆ S ∧ ¬x ⊆ B ∧ x ⊆ B ∪ C ⇒ ¬x ⊆ S \ C⌝]);
a(contr_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule []
	⌜∀S⦁ x ⊆ S ∧ ¬x ⊆ C ∧ x ⊆ B ∪ C ⇒ ¬x ⊆ S \ B⌝]);
a(lemma_tac⌜x ⊆ Space⋎T τ \ B ∨ x ⊆ Space⋎T τ \ C⌝);
a(DROP_NTH_ASM_T 16 bc_thm_tac);
a(asm_rewrite_tac[]);
a(strip_tac THEN_LIST[∃_tac⌜B⌝, ∃_tac⌜C⌝] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏connected_pointwise_thm⦎ = save_thm ( "connected_pointwise_thm", (
set_goal([], ⌜∀τ X⦁
	τ ∈ Topology
⇒	(	X ∈ τ Connected
	 ⇔ 	∀x y⦁ x ∈ X ∧ y ∈ X ⇒ ∃Y⦁ Y ⊆ X ∧ x ∈ Y ∧ y ∈ Y ∧ Y ∈ τ Connected)⌝);
a(REPEAT strip_tac THEN1 (∃_tac⌜X⌝ THEN PC_T1 "sets_ext1" asm_prove_tac[]));
a(POP_ASM_T ante_tac THEN rewrite_tac[connected_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_asm_fc_tac[]);
a(LIST_GET_NTH_ASM_T [2, 3, 4] (MAP_EVERY ante_tac) THEN PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN PC_T "sets_ext1" contr_tac);
a(list_spec_nth_asm_tac 9 [⌜x⌝, ⌜x'⌝]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ b ∧ b ∩ c = {} ⇒ a ∩ c = {}⌝]);
a(list_spec_nth_asm_tac 3 [⌜B⌝, ⌜C⌝]);
(* *** Goal "2.1" *** *)
a(LIST_GET_NTH_ASM_T [1, 7, 11] (MAP_EVERY ante_tac) THEN PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "2.2" *** *)
a(LIST_GET_NTH_ASM_T [1, 6, 9] (MAP_EVERY ante_tac) THEN PC_T1 "sets_ext" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏connected_pointwise_bc_thm⦎ = save_thm ( "connected_pointwise_bc_thm", (
set_goal([], ⌜∀τ X⦁
	τ ∈ Topology
∧ 	(∀x y⦁ x ∈ X ∧ y ∈ X ⇒ ∃Y⦁ Y ⊆ X ∧ x ∈ Y ∧ y ∈ Y ∧ Y ∈ τ Connected)
⇒	X ∈ τ Connected⌝);
a(REPEAT strip_tac THEN ALL_FC_T1 fc_⇔_canon once_rewrite_tac[connected_pointwise_thm]);
a(POP_ASM_T ante_tac THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏empty_connected_thm⦎ = save_thm ( "empty_connected_thm", (
set_goal([], ⌜∀τ⦁ τ ∈ Topology ⇒ {} ∈ τ Connected⌝);
a(REPEAT strip_tac THEN bc_thm_tac connected_pointwise_bc_thm);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏singleton_connected_thm⦎ = save_thm ( "singleton_connected_thm", (
set_goal([], ⌜∀τ x⦁ τ ∈ Topology ∧ x ∈ Space⋎T τ ⇒ {x} ∈ τ Connected⌝);
a(REPEAT strip_tac THEN rewrite_tac[connected_def, enum_set_clauses]);
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏image_connected_thm⦎ = save_thm ( "image_connected_thm", (
set_goal([], ⌜∀f X σ τ⦁
	f ∈ (σ, τ) Continuous
∧	X ∈ σ Connected
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	{y | ∃x⦁ x ∈ X ∧ y = f x} ∈ τ Connected
⌝);
a(rewrite_tac[connected_def, continuous_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac );
a(all_var_elim_asm_tac1 THEN PC_T1 "sets_ext1" all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(contr_tac);
a(LIST_DROP_NTH_ASM_T [11] all_fc_tac);
a(GET_NTH_ASM_T 12 (PC_T1 "sets_ext1" strip_asm_tac));
a(lemma_tac⌜
	X ⊆ {x|x ∈ Space⋎T σ ∧ f x ∈ B} ∪ {x|x ∈ Space⋎T σ ∧ f x ∈ C}
⌝ THEN1 (PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
		THEN_TRY SOLVED_T (all_asm_fc_tac[])));
(* *** Goal "2.1" *** *)
a(swap_nth_asm_concl_tac 9 THEN PC_T "sets_ext1" strip_tac);
a(REPEAT strip_tac THEN ∃_tac⌜f x⌝ THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜
	X ∩ {x|x ∈ Space⋎T σ ∧ f x ∈ B} ∩ {x|x ∈ Space⋎T σ ∧ f x ∈ C} = {}
⌝ THEN1 (PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac));
(* *** Goal "2.2.1" *** *)
a(swap_nth_asm_concl_tac 11 THEN PC_T "sets_ext1" strip_tac);
a(REPEAT strip_tac THEN ∃_tac⌜f x⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a(LEMMA_T ⌜X ⊆ {x|x ∈ Space⋎T σ ∧ f x ∈ B} ∨ X ⊆ {x|x ∈ Space⋎T σ ∧ f x ∈ C}⌝ ante_tac);
(* *** Goal "2.2.2.1" *** *)
a(DROP_NTH_ASM_T 14 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(swap_nth_asm_concl_tac 8);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "2.2.2.2.2" *** *)
a(swap_nth_asm_concl_tac 7);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏∪_connected_thm⦎ = save_thm ( "∪_connected_thm", (
set_goal([], ⌜∀C D σ⦁
	σ ∈ Topology
∧	C ∈ σ Connected
∧	D ∈ σ Connected
∧	¬C ∩ D = {}
⇒	C ∪ D ∈ σ Connected
⌝);
a(rewrite_tac[connected_def] THEN REPEAT strip_tac
	THEN1 all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ c ∧ b ⊆ c ⇒ a ∪ b ⊆ c⌝]);
a(DROP_NTH_ASM_T 6 (PC_T1 "sets_ext1" strip_asm_tac) THEN contr_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a b c⦁a ∪ b ⊆ c ⇒ a ⊆ c ∧ b ⊆ c⌝]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a b c⦁(a ∪ b) ∩ c = {} ⇒ a ∩ c = {} ∧ b ∩ c = {}⌝]);
a(list_spec_nth_asm_tac 15 [⌜B⌝, ⌜C'⌝] THEN list_spec_nth_asm_tac 14 [⌜B⌝, ⌜C'⌝]);
(* *** Goal "1" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ c ∧ b ⊆ c ⇒ a ∪ b ⊆ c⌝]);
(* *** Goal "2" *** *)
a(ante_tac(pc_rule1 "sets_ext1" prove_rule[]
	⌜x ∈ C ∧ x ∈ D  ∧ C ⊆ B ∧ D ⊆ C' ⇒ x ∈ C ∩ B ∩ C'⌝));
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(ante_tac(pc_rule1 "sets_ext1" prove_rule[]
	⌜x ∈ C ∧ x ∈ D  ∧ C ⊆ C' ∧ D ⊆ B ⇒ x ∈ C ∩ B ∩ C'⌝));
a(asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ c ∧ b ⊆ c ⇒ a ∪ b ⊆ c⌝]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏product_connected_thm⦎ = save_thm ( "product_connected_thm", (
set_goal([], ⌜∀X : 'a SET; Y : 'b SET; σ τ ⦁
	X ∈ σ Connected
∧	Y ∈ τ Connected
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	(X × Y) ∈ (σ ×⋎T τ) Connected⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜(σ ×⋎T τ) ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[connected_pointwise_thm]);
a(REPEAT strip_tac);
a(lemma_tac⌜
	(∃H⦁ H ∈ (σ ×⋎T τ) Connected ∧ x ∈ H ∧ (Fst y, Snd x) ∈ H ∧ H ⊆ (X × Y))
∧	(∃V⦁ V ∈ (σ ×⋎T τ) Connected ∧ y ∈ V ∧ (Fst y, Snd x) ∈ V ∧ V ⊆ (X × Y))⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜{ab | ∃a⦁ a ∈ X ∧ ab = (λa⦁(a, Snd x)) a}⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(bc_thm_tac image_connected_thm);
a(∃_tac⌜σ⌝ THEN REPEAT strip_tac);
a(bc_thm_tac left_product_inj_continuous_thm THEN REPEAT strip_tac);
a(POP_ASM_T discard_tac THEN POP_ASM_T (ante_tac o rewrite_rule[×_def]));
a(DROP_NTH_ASM_T 4 (strip_asm_tac o rewrite_rule[connected_def]));
a(POP_ASM_T discard_tac THEN POP_ASM_T ante_tac
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac ⌜Fst x⌝ THEN rewrite_tac[]);
a(POP_ASM_T discard_tac THEN POP_ASM_T (strip_asm_tac o rewrite_rule[×_def]));
(* *** Goal "1.3" *** *)
a(∃_tac ⌜Fst y⌝ THEN rewrite_tac[]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[×_def]));
(* *** Goal "1.4" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN rewrite_tac[×_def] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o rewrite_rule[×_def]) THEN taut_tac);
(* *** Goal "2" *** *)
a(∃_tac⌜{ab | ∃b⦁ b ∈ Y ∧ ab = (λb⦁(Fst y, b)) b}⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac image_connected_thm);
a(∃_tac⌜τ⌝ THEN REPEAT strip_tac);
a(bc_thm_tac right_product_inj_continuous_thm THEN REPEAT strip_tac);
a(POP_ASM_T (ante_tac o rewrite_rule[×_def]));
a(DROP_NTH_ASM_T 6 (strip_asm_tac o rewrite_rule[connected_def]));
a(POP_ASM_T discard_tac THEN POP_ASM_T ante_tac
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac ⌜Snd y⌝ THEN rewrite_tac[]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[×_def]));
(* *** Goal "2.3" *** *)
a(∃_tac ⌜Snd x⌝ THEN rewrite_tac[]);
a(POP_ASM_T discard_tac THEN POP_ASM_T (strip_asm_tac o rewrite_rule[×_def]));
(* *** Goal "2.4" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN rewrite_tac[×_def] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[×_def]) THEN taut_tac);
(* *** Goal "3" *** *)
a(lemma_tac ⌜H ∪ V ⊆ (X × Y)⌝ THEN1
	all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ c ∧ b ⊆ c ⇒ a ∪ b ⊆ c⌝]);
a(∃_tac⌜H ∪ V⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ∪_connected_thm);
a(REPEAT strip_tac THEN PC_T "sets_ext1" contr_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏∪_open_connected_thm⦎ = save_thm ( "∪_open_connected_thm", (
set_goal([], ⌜∀A B σ⦁
	A ∈ σ
∧	¬A = {}
∧	B ∈ σ
∧	¬B = {}
∧	A ∪ B ∈ σ Connected
⇒	¬A ∩ B = {}
⌝);
a(rewrite_tac[connected_def] THEN contr_tac);
a(DROP_NTH_ASM_T 2 (ante_tac o list_∀_elim[⌜A⌝, ⌜B⌝]));
a(asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [2, 4, 6] discard_tac THEN PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏∪_closed_connected_thm⦎ = save_thm ( "∪_closed_connected_thm", (
set_goal([], ⌜∀A B σ⦁
	A ∈ σ Closed
∧	¬A = {}
∧	B ∈ σ Closed
∧	¬B = {}
∧	A ∪ B ∈ σ Connected
⇒	¬A ∩ B = {}
⌝);
a(rewrite_tac[connected_closed_thm] THEN contr_tac);
a(DROP_NTH_ASM_T 2 (ante_tac o list_∀_elim[⌜A⌝, ⌜B⌝]));
a(asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [2, 4, 6] discard_tac THEN PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
The previous result is the first in a sequence of results saying that if one has a chain of connected sets each of which meets its successor, then the union of the sequence is connected.
The case when the chain has length three is often useful to have:

=SML

val ⦏∪_∪_connected_thm⦎ = save_thm ( "∪_∪_connected_thm", (
set_goal([], ⌜∀C D E σ⦁
	σ ∈ Topology
∧	C ∈ σ Connected
∧	D ∈ σ Connected
∧	E ∈ σ Connected
∧	¬C ∩ D = {}
∧	¬D ∩ E = {}
⇒	C ∪ D ∪ E ∈ σ Connected
⌝);
a(REPEAT strip_tac THEN REPEAT (bc_thm_tac ∪_connected_thm THEN REPEAT strip_tac));
a(PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏cover_connected_thm⦎ = save_thm ( "cover_connected_thm", (
set_goal([], ⌜∀C U σ⦁
	σ ∈ Topology
∧	C ∈ σ Connected
∧	U ⊆ σ Connected
∧	C ⊆ ⋃U
⇒	⋃{D | D ∈ U ∧ ¬C ∩ D = {}} ∈ σ Connected
⌝);
a(REPEAT strip_tac THEN bc_thm_tac connected_pointwise_bc_thm THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 7 (PC_T1 "sets_ext1" strip_asm_tac));
a(GET_NTH_ASM_T 9 (PC_T1 "sets_ext1" strip_asm_tac));
a(∃_tac⌜s ∪ C ∪ s'⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LIST_GET_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜s''⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(∃_tac⌜s'⌝ THEN REPEAT strip_tac);
(* *** Goal "4" *** *)
a(bc_thm_tac ∪_∪_connected_thm THEN REPEAT strip_tac
	THEN_TRY (SOLVED_T (all_asm_fc_tac[])));
a(GET_NTH_ASM_T 6 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏separation_thm⦎ = save_thm ( "separation_thm", (
set_goal([], ⌜∀τ C D⦁
	τ ∈ Topology
∧	C ∈ τ Connected
∧	D ∈ τ Connected
∧	¬C ∪ D ∈ τ Connected
⇒	∃A B⦁	A ∈ τ ∧ B ∈ τ ∧ (C ∪ D) ∩ A ∩ B = {}
	∧	C ⊆ A
	∧	D ⊆ B
⌝);
a(rewrite_tac[connected_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(i_contr_tac THEN
	LIST_GET_NTH_ASM_T[1, 3, 5] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜C ⊆ B ∪ C' ∧ C ∩ B ∩ C' = {}⌝ THEN1
	(LIST_GET_NTH_ASM_T[3, 4] (MAP_EVERY ante_tac)
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(lemma_tac⌜D ⊆ B ∪ C' ∧ D ∩ B ∩ C' = {}⌝ THEN1
	(LIST_GET_NTH_ASM_T[5, 6] (MAP_EVERY ante_tac)
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T ⌜C ⊆ B ∨ C ⊆ C'⌝ ante_tac THEN1
	(DROP_NTH_ASM_T 13 bc_thm_tac THEN REPEAT strip_tac));
a(LEMMA_T ⌜D ⊆ B ∨ D ⊆ C'⌝ ante_tac THEN1
	(DROP_NTH_ASM_T 11 bc_thm_tac THEN REPEAT strip_tac));
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(i_contr_tac THEN
	LIST_GET_NTH_ASM_T[1, 2, 8] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜C'⌝ THEN ∃_tac⌜B⌝ THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 9 ante_tac THEN PC_T1"sets_ext1" prove_tac[]);
(* *** Goal "2.3" *** *)
a(∃_tac⌜B⌝ THEN ∃_tac⌜C'⌝ THEN REPEAT strip_tac);
(* *** Goal "2.4" *** *)
a(i_contr_tac THEN
	LIST_GET_NTH_ASM_T[1, 2, 7] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏finite_separation_thm⦎ = save_thm ( "finite_separation_thm", (
set_goal([], ⌜∀τ U A⦁
	τ ∈ Topology
∧	U ∈ Finite
∧	¬{} ∈ U
∧	U ⊆ τ Connected
∧	A ∈ U
∧	(∀B⦁B ∈ U ∧ ¬A = B ⇒ ¬A ∪ B ∈ τ Connected)
⇒	∃C D⦁	C ∈ τ ∧ D ∈ τ 
	∧	A ⊆ C ∧ ⋃(U \ {A}) ⊆ D
	∧	⋃U ∩ C ∩ D = {}
⌝);
a(REPEAT strip_tac);
a(cases_tac⌜∀b⦁b ∈ U ⇒ A = b⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜Space⋎T τ⌝ THEN ∃_tac⌜{}⌝);
a(ALL_FC_T rewrite_tac[space_t_open_thm, empty_open_thm]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀x u t⦁x ∈ u ∧ u ⊆ t ⇒ x ∈ t⌝]);
a(REPEAT strip_tac THEN1
	(POP_ASM_T ante_tac THEN rewrite_tac[connected_def]
	THEN PC_T1 "sets_ext1" prove_tac[]));
a(PC_T1"sets_ext1" REPEAT strip_tac
	THEN all_asm_fc_tac[] THEN all_var_elim_asm_tac1);
(* *** Goal "2" *** *)
a(lemma_tac⌜∃f⦁∀b⦁b ∈ U ∧ ¬A = b ⇒
	Fst (f b) ∈ τ ∧ Snd (f b) ∈ τ ∧
	A ⊆ Fst (f b) ∧ b ⊆ Snd (f b) ∧
	(A ∪ b) ∩ Fst (f b) ∩ Snd (f b) = {}⌝);
(* *** Goal "2.1" *** *)
a(prove_∃_tac THEN REPEAT strip_tac);
a(cases_tac⌜b' ∈ U ∧ ¬ A = b'⌝ THEN asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T[3, 4, 5] all_fc_tac);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀x u t⦁x ∈ u ∧ u ⊆ t ⇒ x ∈ t⌝]);
a(all_fc_tac[separation_thm]);
a(∃_tac⌜(A', B)⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜⋂{X | ∃b⦁b ∈ U ∧ ¬A = b ∧ X = Fst(f b)}⌝);
a(∃_tac⌜⋃{Y | ∃b⦁b ∈ U ∧ ¬A = b ∧ Y = Snd(f b)}⌝);
a(REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(bc_thm_tac finite_⋂_open_thm THEN REPEAT strip_tac);
(* *** Goal "2.2.1.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "2.2.1.2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN rewrite_tac[]);
a(∃_tac⌜Fst(f b)⌝ THEN ∃_tac⌜b⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1.3" *** *)
a(GET_NTH_ASM_T 8 ante_tac THEN DROP_ASMS_T discard_tac
	THEN REPEAT strip_tac THEN finite_induction_tac⌜U⌝);
(* *** Goal "2.2.1.3.1" *** *)
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜{a|F} = {}⌝,
	empty_finite_thm]);
(* *** Goal "2.2.1.3.2" *** *)
a(cases_tac⌜A = x⌝ THEN1 all_var_elim_asm_tac);
(* *** Goal "2.2.1.3.2.1" *** *)
a(LEMMA_T⌜{X|∃ b⦁ b ∈ {x} ∪ U ∧ ¬ x = b ∧ X = Fst (f b)}
            = {X|∃ b⦁ b ∈ U ∧ ¬ x = b ∧ X = Fst (f b)}⌝
	asm_rewrite_thm_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "2.2.1.3.2.1.1" *** *)
a(∃_tac⌜b⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1.3.2.1.2" *** *)
a(∃_tac⌜b⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1.3.2.2" *** *)
a(LEMMA_T⌜{X|∃ b⦁ b ∈ {x} ∪ U ∧ ¬ A = b ∧ X = Fst (f b)}
            = {Fst(f x)} ∪ {X|∃ b⦁ b ∈ U ∧ ¬ A = b ∧ X = Fst (f b)}⌝
	asm_rewrite_thm_tac THEN_LIST
	[id_tac,
	bc_thm_tac singleton_∪_finite_thm
		THEN REPEAT strip_tac]);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "2.2.1.3.2.2.1" *** *)
a(∃_tac⌜b⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1.3.2.2.2" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1.3.2.2.1" *** *)
a(∃_tac⌜b⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a(bc_thm_tac ⋃_open_thm THEN REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "2.2.3" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
a(LIST_GET_NTH_ASM_T[10, 15] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.4" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o conv_rule(RAND_C eq_sym_conv)));
a(all_asm_fc_tac[]);
a(∃_tac⌜Snd(f s)⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.4.1" *** *)
a(LIST_GET_NTH_ASM_T[9, 15] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.4.2" *** *)
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.5" *** *)
a(PC_T "sets_ext1"  strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(cases_tac⌜A = s⌝ THEN1 (POP_ASM_T (asm_tac o eq_sym_rule) THEN all_var_elim_asm_tac1));
(* *** Goal "2.2.5.1" *** *)
a(LIST_DROP_NTH_ASM_T [6, 7, 8] all_asm_fc_tac);
a(LIST_GET_NTH_ASM_T[1, 3, 9, 11] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.5.2" *** *)
a(DROP_NTH_ASM_T 5 (ante_tac o ∀_elim⌜Fst (f s)⌝));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2.5.2.1" *** *)
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2, 3, 7, 8, 9] all_asm_fc_tac);
a(LIST_GET_NTH_ASM_T[1, 2,  10] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏connected_extension_thm⦎ = save_thm ( "connected_extension_thm", (
set_goal([], ⌜∀τ U B⦁
	τ ∈ Topology
∧	U ∈ Finite
∧	¬{} ∈ U
∧	U ⊆ τ Connected
∧	B ∈ τ Connected
∧	⋃U ∪ B ∈ τ Connected
∧	¬⋃U ⊆ B
⇒	∃A⦁ A ∈ U ∧ A ∪ B ∈ τ Connected ∧ ¬A ⊆ B
⌝);
a(REPEAT strip_tac);
a(cases_tac⌜B = {}⌝);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN
	asm_rewrite_tac[] THEN PC_T "sets_ext1" strip_tac);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀x u t⦁x ∈ u ∧ u ⊆ t ⇒ x ∈ t⌝]);
a(cases_tac⌜s = {}⌝ THEN1 all_var_elim_asm_tac1);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(contr_tac);
a(PC_T1 "predicates" lemma_tac⌜
	{B} ∪ ({C | C ∈ U ∧ ¬C ⊆ B}) ∈ Finite
∧	¬{} ∈ {B} ∪ ({C | C ∈ U ∧ ¬C ⊆ B})
∧	{B} ∪ ({C | C ∈ U ∧ ¬C ⊆ B}) ⊆ τ Connected
∧	B ∈ {B} ∪ ({C | C ∈ U ∧ ¬C ⊆ B})
∧	(∀ C⦁ C ∈ {B} ∪ ({C | C ∈ U ∧ ¬C ⊆ B})
		∧ ¬ B = C ⇒ ¬ B ∪ C ∈ τ Connected)⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac singleton_∪_finite_thm);
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜U⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN1 asm_rewrite_tac[]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀x u t⦁x ∈ u ∧ u ⊆ t ⇒ x ∈ t⌝]);
(* *** Goal "2.4" *** *)
a(all_var_elim_asm_tac1);
(* *** Goal "2.5" *** *)
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀A⦁A ∪ C = C ∪ A⌝]);
a(contr_tac THEN spec_nth_asm_tac 5 ⌜C⌝);
(* *** Goal "2.6" *** *)
a(all_fc_tac[finite_separation_thm]);
a(swap_nth_asm_concl_tac 14 THEN rewrite_tac[connected_def]
	THEN REPEAT strip_tac);
a(i_contr_tac THEN POP_ASM_T ante_tac);
a(rewrite_tac[] THEN strip_tac THEN
	∃_tac⌜C⌝ THEN asm_rewrite_tac[]);
a(strip_tac THEN ∃_tac⌜D⌝ THEN asm_rewrite_tac[]);
a(lemma_tac ⌜⋃ ({B} ∪  {C|C ∈ U ∧ ¬C ⊆ B}) = ⋃U ∪ B⌝);
(* *** Goal "2.6.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "2.6.1.1" *** *)
a(all_var_elim_asm_tac);
(* *** Goal "2.6.1.2" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2.6.1.3" *** *)
a(cases_tac⌜x ∈ B⌝  THEN1 (∃_tac⌜B⌝ THEN REPEAT strip_tac));
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T[2, 4] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.6.1.4" *** *)
a(∃_tac⌜B⌝ THEN REPEAT strip_tac);
(* *** Goal "2.6.2" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a(asm_rewrite_tac[]);
a(LEMMA_T ⌜⋃ U ∪ B ⊆ C ∪ D⌝ rewrite_thm_tac);
(* *** Goal "2.6.2.1" *** *)
a(LEMMA_T ⌜⋃ U ∪ B = ⋃ (({B} ∪ {C|C ∈ U ∧ ¬ C ⊆ B}) \ {B}) ∪ B⌝ rewrite_thm_tac);
(* *** Goal "2.6.2.1.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "2.6.2.1.1.1" *** *)
a(swap_nth_asm_concl_tac 1 THEN REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.6.2.1.1.1.1" *** *)
a(LIST_GET_NTH_ASM_T[2, 4] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.6.2.1.1.1.2" *** *)
a(contr_tac THEN all_var_elim_asm_tac1);
(* *** Goal "2.6.2.1.1.2" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2.6.2.1.2" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀s v c d⦁ v ⊆ c ∧ s ⊆ d ⇒ s ∪ v ⊆ c ∪ d⌝]);
(* *** Goal "2.6.2.2" *** *)
a(contr_tac);
(* *** Goal "2.6.2.2.1" *** *)
a(LIST_DROP_NTH_ASM_T [1, 2, 3, 4, 15] (MAP_EVERY (PC_T1 "sets_ext1" strip_asm_tac)));
a(spec_nth_asm_tac 4 ⌜x⌝);
(* *** Goal "2.6.2.2.1.1" *** *)
a(spec_nth_asm_tac 1 ⌜s⌝);
(* *** Goal "2.6.2.2.1.1.1" *** *)
a(LIST_GET_NTH_ASM_T[1, 4, 6] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.6.2.2.1.1.2" *** *)
a(LIST_GET_NTH_ASM_T[1, 3, 5] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.6.2.2.1.2" *** *)
a(lemma_tac⌜x ∈ C⌝ THEN1 GET_NTH_ASM_T 8 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.6.2.2.1.2.1" *** *)
a(spec_nth_asm_tac 1 ⌜s⌝);
(* *** Goal "2.6.2.2.1.2.2" *** *)
a(spec_nth_asm_tac 8 ⌜x⌝);
(* *** Goal "2.6.2.2.1.2.2.1" *** *)
a(spec_nth_asm_tac 1 ⌜s⌝);
(* *** Goal "2.6.2.2.1.2.2.2" *** *)
a(spec_nth_asm_tac 3 ⌜s'⌝);
(* *** Goal "2.6.2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [1, 2, 3, 4, 5, 14] (MAP_EVERY (PC_T1 "sets_ext1" strip_asm_tac)));
a(spec_nth_asm_tac 6 ⌜x⌝);
a(spec_nth_asm_tac 3 ⌜x⌝);
a(spec_nth_asm_tac 7 ⌜x⌝);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

set_goal([], ⌜∀V A B⦁V ⊆ {A} ∪ {B} ⇒ V = {} ∨ V = {A} ∨ V = {B} ∨ V = {A} ∪ {B}⌝);
a(PC_T1"sets_ext1"  rewrite_tac[]);
a(contr_tac THEN_TRY all_var_elim_asm_tac1
	THEN  asm_fc_tac[] THEN_TRY all_var_elim_asm_tac1);
val ⦏⊆_doubleton_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML

set_goal([], ⌜∀L B⦁ B ∈ Elems L ⇒ B ⊆ ⋃(Elems L)⌝);
a(∀_tac);
a(list_induction_tac⌜L⌝ THEN asm_rewrite_tac[elems_def,
	enum_set_clauses,
	pc_rule1"sets_ext1" prove_rule[]
		⌜∀u v⦁ ⋃(u ∪ v) = ⋃u ∪ ⋃ v⌝]);
a(REPEAT strip_tac THEN1 all_var_elim_asm_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[] THEN PC_T1 "sets_ext1" asm_prove_tac[]);
val ⦏⊆_⋃_elems_lemma⦎ = pop_thm();

=TEX
%%%%
%%%%

=SML

set_goal([], ⌜ ∀τ U A⦁
	τ ∈ Topology
∧	U ∈ Finite
∧	¬{} ∈ U
∧	U ⊆ τ Connected
∧	⋃U ∈ τ Connected
∧	A ∈ U
⇒	∃L⦁	L 0 = [A]
∧	(∀m⦁ 	Elems (L m) ⊆ U)
∧	(∀m⦁ 	⋃(Elems (L m)) ∈ τ Connected)
∧	(∀m⦁ 	if	¬⋃U ⊆ ⋃(Elems (L m))
		then	∃B⦁	B ∈ U
			∧	B ∪ ⋃(Elems (L m)) ∈ τ Connected
			∧	¬B ⊆ ⋃(Elems (L m))
			∧	L(m + 1) = Cons B (L m)
		else	L (m + 1) = L m)
∧	(∀m⦁ 	L m ∈ Distinct)
⌝);
a(REPEAT strip_tac);
a(once_rewrite_tac[taut_rule⌜∀p1 p2 p3 p4 p5⦁
	p1 ∧ p2 ∧ p3 ∧ p4 ∧ p5 ⇔
	p1 ∧ p2 ∧ p3 ∧ p4 ∧ (p4 ⇒ p5)⌝]);
a(lemma_tac ⌜∃f⦁
	∀V⦁
	if	V ∈ τ Connected
	∧	V ⊆ ⋃U
 	∧	¬ ⋃ U ⊆ V
	then	f V ∈ U
	∧	f V ∪ V ∈ τ Connected
	∧	¬ f V ⊆ V
	else	f V = {}⌝
	THEN1 prove_∃_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN
	cases_tac⌜V' ∈ τ Connected ∧ V' ⊆ ⋃U ∧ ¬ ⋃U ⊆ V'⌝
	THEN asm_rewrite_tac[] THEN_TRY prove_∃_tac);
a(bc_thm_tac connected_extension_thm THEN REPEAT strip_tac);
a(ALL_FC_T asm_rewrite_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀u v⦁ v ⊆ u ⇒ u ∪ v = u⌝]);
(* *** Goal "2" *** *)
a(lemma_tac ⌜∃L⦁
	L 0  = [A]
∧	∀m⦁ L (m + 1) =
		if 	¬f(⋃(Elems(L m))) = {}
		then	Cons (f(⋃(Elems(L m)))) (L m)
		else	L m⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∀ m⦁ Elems (L m) ⊆ U⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝
	THEN asm_rewrite_tac[elems_def]);
(* *** Goal "2.1.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac);
(* *** Goal "2.1.2" *** *)
a(cases_tac⌜f (⋃ (Elems (L m))) = {}⌝ THEN
	asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 5 (ante_tac o ∀_elim⌜⋃ (Elems (L m))⌝));
a(cases_tac⌜⋃ (Elems (L m)) ∈ τ Connected
	∧ ⋃ (Elems (L m)) ⊆ ⋃ U
	∧ ¬ ⋃ U ⊆ ⋃ (Elems (L m))⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN asm_rewrite_tac[elems_def]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀x b c⦁x ∈ c ∧ b ⊆ c ⇒ {x} ∪ b ⊆ c⌝]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∀ m⦁ ⋃ (Elems (L m)) ∈ τ Connected⌝);
(* *** Goal "2.2.1" *** *)
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝
	THEN asm_rewrite_tac[elems_def, enum_set_clauses]);
(* *** Goal "2.2.1.1" *** *)
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀x b c⦁x ∈ b ∧ b ⊆ c ⇒ x ∈ c⌝]);
(* *** Goal "2.2.1.2" *** *)
a(cases_tac⌜f (⋃ (Elems (L m))) = {}⌝ THEN
	asm_rewrite_tac[]);
a(rewrite_tac[elems_def,
	enum_set_clauses,
	pc_rule1"sets_ext1" prove_rule[]
		⌜∀u v⦁ ⋃(u ∪ v) = ⋃u ∪ ⋃ v⌝]);
a(DROP_NTH_ASM_T 6 (ante_tac o ∀_elim⌜⋃ (Elems (L m))⌝));
a(cases_tac⌜⋃ (Elems (L m)) ∈ τ Connected
	∧ ⋃ (Elems (L m)) ⊆ ⋃ U
	∧ ¬ ⋃ U ⊆ ⋃ (Elems (L m))⌝ THEN asm_rewrite_tac[]);
a(taut_tac);
(* *** Goal "2.2.2" *** *)
a(∃_tac⌜L⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2.2.2.3" *** *)
a(DROP_NTH_ASM_T 6 (ante_tac o ∀_elim⌜⋃ (Elems (L m))⌝));
a(lemma_tac⌜Elems(L m) ⊆ U⌝ THEN asm_rewrite_tac[]);
a(ALL_FC_T asm_rewrite_tac[pc_rule1"sets_ext1" prove_rule[]
	⌜∀u v⦁ v ⊆ u ⇒ ⋃v ⊆ ⋃u ⌝]);
a(REPEAT strip_tac THEN ∃_tac⌜f (⋃ (Elems (L m)))⌝
	THEN REPEAT strip_tac);
a(cases_tac⌜f (⋃ (Elems (L m))) = {}⌝ THEN
	asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.4" *** *)
a(DROP_NTH_ASM_T 6 (ante_tac o ∀_elim⌜⋃ (Elems (L m))⌝));
a(asm_rewrite_tac[]);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.5" *** *)
a(induction_tac⌜m⌝ THEN1
	asm_rewrite_tac[distinct_def, elems_def]);
a(DROP_NTH_ASM_T 2 (ante_tac o ∀_elim⌜m⌝));
a(cases_tac⌜⋃U ⊆ ⋃(Elems (L m))⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
a(asm_rewrite_tac[distinct_def]);
a(swap_nth_asm_concl_tac 2);
a(all_fc_tac[⊆_⋃_elems_lemma]);
val ⦏connected_chain_lemma1⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML

set_goal([], ⌜∀list x⦁ ¬list = Cons x list⌝);
a(∀_tac THEN conv_tac(ONCE_MAP_C eq_sym_conv));
a(list_induction_tac ⌜list⌝ THEN REPEAT strip_tac
	THEN asm_rewrite_tac[nil_cons_def]);
val ⦏cons_lemma⦎ = pop_thm();

=TEX
%%%%
%%%%

=SML

val ⦏connected_chain_thm⦎ = save_thm ( "connected_chain_thm", (
set_goal([], ⌜ ∀τ U A⦁
	τ ∈ Topology
∧	U ∈ Finite
∧	¬{} ∈ U
∧	U ⊆ τ Connected
∧	⋃U ∈ τ Connected
∧	A ∈ U
⇒	∃L n⦁	L 0 = [A]
∧	(∀m⦁ 	⋃(Elems (L m)) ∈ τ Connected)
∧	(∀m⦁ 	Elems (L m) ⊆ U)
∧	(∀m⦁ 	m < n
	⇒	∃B⦁	B ∈ U
		∧	¬B ⊆ ⋃(Elems (L m))
		∧	L(m + 1) = Cons B (L m))
∧	⋃U = ⋃(Elems (L n))
∧	(∀m⦁ 	L m ∈ Distinct)
⌝);
a(REPEAT strip_tac THEN all_fc_tac[connected_chain_lemma1]);
a(lemma_tac⌜∃N⦁ L (N + 1) = L N⌝ THEN1 contr_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜∀m⦁#(L m) = m + 1⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(induction_tac⌜m⌝ THEN1 asm_rewrite_tac[length_def]);
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜m⌝));
a(cases_tac ⌜⋃ U ⊆ ⋃ (Elems (L m))⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN asm_rewrite_tac[length_def]);
(* *** Goal "1.2" *** *)
a(LEMMA_T⌜#(Elems(L (#U))) = #(L (#U))⌝ ante_tac THEN1
	(bc_thm_tac distinct_size_length_thm
		THEN asm_rewrite_tac[]));
a(asm_rewrite_tac[]);
a(LEMMA_T⌜#(Elems(L (#U))) ≤ #U⌝ ante_tac THEN1
	(bc_thm_tac ⊆_size_thm THEN asm_rewrite_tac[]));
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜L⌝ THEN ∃_tac⌜Min{n | L(n+1) = L n}⌝);
a(asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜m⌝));
a(cases_tac⌜¬ ⋃ U ⊆ ⋃ (Elems (L m))⌝ THEN asm_rewrite_tac[]
	THEN1 prove_tac[]);
a(strip_tac THEN i_contr_tac);
a(lemma_tac ⌜Min {n|L (n + 1) = L n} ≤ m⌝ THEN_LIST
	[bc_thm_tac min_≤_thm, PC_T1 "lin_arith" asm_prove_tac[]]);
a(REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∀m⦁⋃(Elems(L m)) ⊆ ⋃U⌝ THEN1
	(strip_tac THEN bc_thm_tac
	(pc_rule1 "sets_ext1" prove_rule[]
		⌜∀v u⦁v ⊆ u ⇒ ⋃v ⊆ ⋃u⌝) THEN
			asm_rewrite_tac[]));
a(asm_rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
		⌜∀a b⦁ a = b ⇔ a ⊆ b ∧ b ⊆ a⌝]);
a(contr_tac);
a(lemma_tac⌜Min {n|L(n + 1) = L n} ∈ {n|L(n + 1) = L n}⌝ THEN1
	(bc_thm_tac min_∈_thm THEN
		∃_tac⌜N⌝ THEN REPEAT strip_tac));
a(DROP_NTH_ASM_T 6 (ante_tac o ∀_elim⌜Min {n|L (n + 1) = L n}⌝)
	THEN asm_rewrite_tac[cons_lemma]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏connected_triad_thm⦎ = save_thm ( "connected_triad_thm", (
set_goal([],⌜∀τ A B C⦁
	τ ∈ Topology
∧	A ∈ τ Connected
∧	B ∈ τ Connected
∧	C ∈ τ Connected
∧	A ∪ B ∪ C ∈ τ Connected
⇒	A ∪ C ∈ τ Connected ∨ B ∪ C ∈ τ Connected⌝);
a(contr_tac);
a(swap_nth_asm_concl_tac 3 THEN rewrite_tac[connected_def] THEN strip_tac);
a(∨_right_tac THEN conv_tac (TOP_MAP_C ¬_∀_conv));
a(all_fc_tac[separation_thm]);
a(∃_tac⌜A'' ∪ A'⌝ THEN ∃_tac⌜B'' ∩ B'⌝);
a(ALL_FC_T rewrite_tac[∪_open_thm, ∩_open_thm]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_GET_NTH_ASM_T [1, 2, 6, 7] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(LIST_GET_NTH_ASM_T [1, 2, 3, 6, 7, 8] (MAP_EVERY ante_tac)
	THEN DROP_ASMS_T discard_tac
	THEN PC_T1 "sets_ext1" prove_tac[]
	THEN REPEAT (contr_tac THEN all_asm_fc_tac[]));
(* *** Goal "3" *** *)
a(contr_tac THEN lemma_tac⌜C ⊆ A'' ∪ A'⌝ THEN1
	(POP_ASM_T ante_tac THEN  PC_T1 "sets_ext1" prove_tac[]));
a(cases_tac ⌜C = {}⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "3.1" *** *)
a(swap_nth_asm_concl_tac 10 THEN1 asm_rewrite_tac[]);
(* *** Goal "3.2" *** *)
a((LIST_GET_NTH_ASM_T [1, 2, 4, 6, 9, 11] (MAP_EVERY ante_tac)
		THEN DROP_ASMS_T  discard_tac
		THEN PC_T "sets_ext1" contr_tac));
a(LIST_DROP_NTH_ASM_T [2, 3, 4, 5, 6] (MAP_EVERY (strip_asm_tac o ∀_elim⌜x⌝)));
(* *** Goal "4" *** *)
a(contr_tac THEN lemma_tac⌜A ⊆ B''⌝ THEN1
	(POP_ASM_T ante_tac THEN  PC_T1 "sets_ext1" prove_tac[]));
a(cases_tac ⌜A = {}⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "4.1" *** *)
a(swap_nth_asm_concl_tac 12 THEN1 asm_rewrite_tac[]);
(* *** Goal "4.2" *** *)
a((LIST_GET_NTH_ASM_T [1, 2, 5, 6] (MAP_EVERY ante_tac)
		THEN DROP_ASMS_T  discard_tac
		THEN PC_T "sets_ext1" contr_tac));
a(LIST_DROP_NTH_ASM_T [2, 3, 4] (MAP_EVERY (strip_asm_tac o ∀_elim⌜x⌝)));
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏connected_step_thm⦎ = save_thm ( "connected_step_thm", (
set_goal([], ⌜ ∀τ U; A: 'a SET⦁
	τ ∈ Topology
∧	U ∈ Finite
∧	U ⊆ τ Connected
∧	⋃U ∈ τ Connected
∧	A ∈ U
⇒	A = ⋃U
∨	∃B V⦁
	B  ∈ U
∧	¬B = A
∧	V ⊆ U
∧	⋃V ∈ τ Connected
∧	¬B ⊆ ⋃V
∧	⋃U = B ∪ ⋃V
⌝);
a(REPEAT strip_tac THEN
	PC_T1 "predicates" lemma_tac⌜
	U \  {{}:'a SET}∈ Finite
∧	¬{} ∈ U \  {{}}
∧	U  \  {{}} ⊆ τ Connected
∧	⋃(U \ {{}}) = ⋃U⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜U⌝ THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b⦁a \ b ⊆ a⌝]);
(* *** Goal "2" *** *)
a(bc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]
	 THEN ∃_tac⌜U⌝ THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b⦁a \ b ⊆ a⌝]);
(* *** Goal "3" *** *)
a(PC_T "sets_ext1" strip_tac THEN prove_tac[]);
a(∃_tac⌜s⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "4" *** *)
a(lemma_tac⌜⋃(U \ {{}}) ∈ τ Connected⌝ THEN1 asm_rewrite_tac[]);
a(cases_tac⌜A = {}⌝  THEN1 all_var_elim_asm_tac1);
(* *** Goal "4.1" *** *)
a(DROP_NTH_ASM_T 6 (PC_T1 "sets_ext1" strip_asm_tac));
a(PC_T1 "predicates" all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀x⦁x ∈ s ∧ s ∈ U ⇒ s ∈ U \ {{}}⌝]);
a(all_fc_tac[connected_chain_thm]);
a(strip_asm_tac(∀_elim⌜n⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1);
(* *** Goal "4.1.1" *** *)
a(∃_tac⌜s⌝ THEN ∃_tac⌜{}⌝ THEN
	ALL_FC_T asm_rewrite_tac[enum_set_clauses,
			empty_connected_thm]);
a(DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[elems_def,
		enum_set_clauses]);
a(REPEAT strip_tac THEN
	GET_ASM_T ⌜x ∈ s⌝ ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "4.1.2" *** *)
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜i⌝));
a(∃_tac⌜B⌝ THEN ∃_tac⌜Elems(L i)⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 6 ante_tac THEN asm_rewrite_tac[
	pc_rule1"sets_ext1" prove_rule[]
		⌜∀u v⦁⋃(u ∪ v) = ⋃u ∪ ⋃ v⌝,
	elems_def, enum_set_clauses]);
a(REPEAT strip_tac);
a(bc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]
	 THEN ∃_tac⌜U \ {{}}⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "4.2" *** *)
a(PC_T1 "predicates" lemma_tac⌜A ∈ U \ {{}}⌝ THEN1
	REPEAT strip_tac);
a(all_fc_tac[connected_chain_thm]);
a(strip_asm_tac(∀_elim⌜n⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1);
(* *** Goal "4.2.1" *** *)
a(i_contr_tac THEN DROP_NTH_ASM_T 2 ante_tac);
a(asm_rewrite_tac[elems_def, enum_set_clauses]);
a(contr_tac THEN all_var_elim_asm_tac1);
(* *** Goal "4.2.2" *** *)
a(GET_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜i⌝));
a(∃_tac⌜B⌝ THEN ∃_tac⌜Elems(L i)⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 6 ante_tac THEN asm_rewrite_tac[
	pc_rule1"sets_ext1" prove_rule[]
		⌜∀u v⦁⋃(u ∪ v) = ⋃u ∪ ⋃ v⌝,
	elems_def, enum_set_clauses]);
a(REPEAT strip_tac);
(* *** Goal "4.2.2.1" *** *)
a(contr_tac THEN all_var_elim_asm_tac);
a(GET_NTH_ASM_T 4 (ante_tac o ∀_elim⌜i + 1⌝));
a(GET_NTH_ASM_T 2 rewrite_thm_tac);
a(asm_rewrite_tac[distinct_def]);
a(LIST_DROP_NTH_ASM_T [5, 8] (MAP_EVERY ante_tac));
a(DROP_ASMS_T discard_tac THEN induction_tac⌜i⌝
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[elems_def]);
(* *** Goal "4.2.2.1.1" *** *)
a(i_contr_tac THEN SPEC_NTH_ASM_T 1 ⌜m'⌝ ante_tac);
a(LEMMA_T ⌜m' < (i + 1) + 1⌝ rewrite_thm_tac THEN1
	PC_T1 "lin_arith" asm_prove_tac[]);
a(conv_tac ¬_∃_conv THEN asm_rewrite_tac[]);
(* *** Goal "4.2.2.1.2" *** *)
a(SPEC_NTH_ASM_T 1 ⌜i⌝ ante_tac);
a(LEMMA_T ⌜i < (i + 1) + 1⌝ rewrite_thm_tac THEN1
	PC_T1 "lin_arith" prove_tac[]);
a(REPEAT strip_tac THEN asm_rewrite_tac[elems_def]
	THEN REPEAT strip_tac);
(* *** Goal "4.2.2.2" *** *)
a(bc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]
	 THEN ∃_tac⌜U \ {{}}⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
\subsection{Homeomorphisms}
%%%%
%%%%
The identity function is a homeomorphism.
=SML

val ⦏id_homomorphism_thm⦎ = save_thm ( "id_homomorphism_thm", (
set_goal([], ⌜∀τ⦁
	τ ∈ Topology
⇒	(λx⦁ x) ∈ (τ, τ) Homeomorphism⌝);
a(rewrite_tac [homeomorphism_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[id_continuous_thm]);
(* *** Goal "2" *** *)
a(∃_tac⌜λy⦁ y⌝);
a(ALL_FC_T rewrite_tac[id_continuous_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
The composite of two homeomorphisms is a homeomorphism:
=SML

val ⦏comp_homeomorphism_thm⦎ = save_thm ( "comp_homeomorphism_thm", (
set_goal([], ⌜∀f g ρ σ τ⦁
	f ∈ (ρ, σ) Homeomorphism
∧	g ∈ (σ, τ) Homeomorphism
∧	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	(λx⦁ g(f x)) ∈ (ρ, τ) Homeomorphism
⌝);
a(rewrite_tac [homeomorphism_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac [comp_continuous_thm]);
(* *** Goal "2" *** *)
a(∃_tac⌜λy⦁ g'(g'' y)⌝);
a(ALL_FC_T rewrite_tac [comp_continuous_thm]);
a(all_asm_ante_tac THEN rewrite_tac[continuous_def] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(all_asm_fc_tac[] THEN ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(all_asm_fc_tac[] THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
The cartesian product of two homeomoprhisms is a homeomorphism:
=SML

val ⦏product_homeomorphism_thm⦎ = save_thm ( "product_homeomorphism_thm", (
set_goal([], ⌜∀ f : 'a → 'b; g : 'c → 'd; ρ : 'a SET SET; σ : 'b SET SET; τ : 'c SET SET; υ : 'd SET SET⦁
	f ∈ (ρ, σ) Homeomorphism
∧	g ∈ (τ, υ) Homeomorphism
∧	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	υ ∈ Topology
⇒	(λ(x, y)⦁(f x, g y)) ∈ ((ρ ×⋎T τ), (σ ×⋎T υ)) Homeomorphism
⌝);
a(rewrite_tac [homeomorphism_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜
	(λ (x, y)⦁ (f x, g y)) = (λz⦁( (λz⦁f((λ(x, y)⦁ x) z)) z, (λz⦁g((λ(x, y)⦁ y) z)) z))⌝
	pure_rewrite_thm_tac THEN1 rewrite_tac[]);
a(bc_thm_tac product_continuous_thm);
a(ALL_FC_T pure_asm_rewrite_tac[product_topology_thm]);
a(REPEAT strip_tac THEN bc_thm_tac comp_continuous_thm);
(* *** Goal "1.1" *** *)
a(∃_tac⌜ρ⌝ THEN REPEAT strip_tac
	THEN ALL_FC_T rewrite_tac[left_proj_continuous_thm, right_proj_continuous_thm,
		product_topology_thm]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜τ⌝ THEN REPEAT strip_tac
	THEN ALL_FC_T rewrite_tac [left_proj_continuous_thm, right_proj_continuous_thm,
		product_topology_thm]);
(* *** Goal "2" *** *)
a(∃_tac⌜λ(x, y)⦁ (g' x, g'' y)⌝);
a(ALL_FC_T pure_rewrite_tac[product_topology_space_t_thm] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LEMMA_T ⌜
	(λ (x, y)⦁ (g' x, g'' y)) = (λz⦁( (λz⦁g'((λ(x, y)⦁ x) z)) z, (λz⦁g''((λ(x, y)⦁ y) z)) z))⌝
	pure_rewrite_thm_tac THEN1 rewrite_tac[]);
a(bc_thm_tac product_continuous_thm);
a(ALL_FC_T pure_asm_rewrite_tac[product_topology_thm]);
a(REPEAT strip_tac THEN bc_thm_tac comp_continuous_thm);
(* *** Goal "2.1.1" *** *)
a(∃_tac⌜σ⌝ THEN REPEAT strip_tac
	THEN ALL_FC_T rewrite_tac [left_proj_continuous_thm, right_proj_continuous_thm,
		product_topology_thm]);
(* *** Goal "2.1.2" *** *)
a(∃_tac⌜υ⌝ THEN REPEAT strip_tac
	THEN ALL_FC_T rewrite_tac[left_proj_continuous_thm, right_proj_continuous_thm,
		product_topology_thm]);
(* *** Goal "2.2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[×_def]);
a(REPEAT strip_tac THEN ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2.3" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[×_def]);
a(REPEAT strip_tac THEN ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2.4" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[×_def]);
a(REPEAT strip_tac THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%
A space is homeomorphich with its product with the unit space.
=SML

val ⦏product_unit_homeomorphism_thm⦎ = save_thm ( "product_unit_homeomorphism_thm", (
set_goal([], ⌜∀τ⦁
	τ ∈ Topology
⇒	(λx⦁(x, One)) ∈ (τ, τ ×⋎T 1⋎T) Homeomorphism
⌝);
a(rewrite_tac [homeomorphism_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(basic_continuity_tac[unit_topology_thm,
	range_unit_topology_continuous_thm,
	space_t_unit_topology_thm]);
(* *** Goal "2" *** *)
a(∃_tac⌜Fst⌝ THEN rewrite_tac[one_def]);
a(basic_continuity_tac[unit_topology_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

The function on a binary product that interchanges the factors is a homeomorphism.

=SML

val ⦏swap_homeomorphism_thm⦎ = save_thm ("swap_homeomorphism_thm", (
set_goal([], ⌜∀σ τ⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	(λ(x, y)⦁(y, x)) ∈ (σ ×⋎T τ, τ ×⋎T σ) Homeomorphism
⌝);
a(rewrite_tac [homeomorphism_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(basic_continuity_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜(λ(y, x)⦁(x, y))⌝ THEN rewrite_tac[]);
a(basic_continuity_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
A homeomorphism is an open mapping (i.e., it maps open sets to open sets):
=SML

val ⦏homeomorphism_open_mapping_thm⦎ = save_thm ( "homeomorphism_open_mapping_thm", (
set_goal([], ⌜∀f σ τ A⦁
	f ∈ (σ, τ) Homeomorphism
∧	A ∈ σ
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	{y | ∃x⦁ x ∈ A ∧ y = f x} ∈ τ
⌝);
a(rewrite_tac [homeomorphism_def, continuous_def] THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [6] all_fc_tac);
a(LEMMA_T ⌜ {y|∃ x⦁ x ∈ A ∧ y = f x} = {x|x ∈ Space⋎T τ ∧ g x ∈ A}⌝ asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1);
a(GET_NTH_ASM_T 11 bc_thm_tac);
a(ALL_FC_T rewrite_tac[∈_space_t_thm]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(all_fc_tac[∈_space_t_thm]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜g x⌝ THEN REPEAT strip_tac);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%
A homeomorphism is a closed mapping (i.e., it maps closed sets to closed sets):
=SML

val ⦏homeomorphism_closed_mapping_thm⦎ = save_thm ( "homeomorphism_closed_mapping_thm", (
set_goal([], ⌜∀f σ τ A⦁
	f ∈ (σ, τ) Homeomorphism
∧	A ∈ σ Closed
∧	σ ∈ Topology
∧	τ ∈ Topology
⇒	{y | ∃x⦁ x ∈ A ∧ y = f x} ∈ τ Closed
⌝);
a(rewrite_tac [homeomorphism_def, continuous_closed_thm] THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [6] all_fc_tac);
a(LEMMA_T ⌜ {y|∃ x⦁ x ∈ A ∧ y = f x} = {x|x ∈ Space⋎T τ ∧ g x ∈ A}⌝ asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1);
a(GET_NTH_ASM_T 11 bc_thm_tac);
a(ALL_FC_T rewrite_tac[∈_closed_∈_space_t_thm]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(all_fc_tac[∈_closed_∈_space_t_thm]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜g x⌝ THEN REPEAT strip_tac);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
A homeomorphism is one-to-one on the space of its domain:
=SML

val ⦏homeomorphism_one_one_thm⦎ = save_thm ( "homeomorphism_one_one_thm", (
set_goal([], ⌜∀f σ τ x y⦁
	f ∈ (σ, τ) Homeomorphism
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	x ∈ Space⋎T σ ∧ y ∈ Space⋎T σ
∧	f x = f y
⇒	x = y
⌝);
a(rewrite_tac [homeomorphism_def] THEN REPEAT strip_tac);
a(LEMMA_T ⌜g(f x) = g(f y)⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
A homeomorphism is onto on the space of its range:
=SML

val ⦏homeomorphism_onto_thm⦎ = save_thm ( "homeomorphism_onto_thm", (
set_goal([], ⌜∀f σ τ y⦁
	f ∈ (σ, τ) Homeomorphism
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	y ∈ Space⋎T τ
⇒	∃x⦁x ∈ Space⋎T σ ∧ y = f x
⌝);
a(rewrite_tac [homeomorphism_def, continuous_def] THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T[7] all_fc_tac);
a(∃_tac⌜g y⌝ THEN REPEAT strip_tac);
a(ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
A function is homomorphism iff it is one-to-one (on the space of its domain), onto (the space of its range),
continuous and open:
=SML

val ⦏homeomorphism_one_one_open_mapping_thm⦎ = save_thm ( "homeomorphism_one_one_open_mapping_thm", (
set_goal([], ⌜∀f σ τ⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	(	f ∈ (σ, τ) Homeomorphism
	⇔	(∀x y⦁ x ∈ Space⋎T σ ∧ y ∈ Space⋎T σ ∧ f x = f y ⇒ x = y)
	∧	(∀y⦁ y ∈ Space⋎T τ ⇒ ∃x⦁x ∈ Space⋎T σ ∧ y = f x)
	∧	f ∈ (σ, τ) Continuous
	∧	(∀A⦁A ∈ σ ⇒ {y | ∃x⦁ x ∈ A ∧ y = f x} ∈ τ))
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[homeomorphism_one_one_thm]);
(* *** Goal "2" *** *)
a(bc_thm_tac homeomorphism_onto_thm);
a(∃_tac⌜τ⌝ THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac [homeomorphism_def] THEN REPEAT strip_tac);
(* *** Goal "4" *** *)
a(all_fc_tac[homeomorphism_open_mapping_thm]);
(* *** Goal "5" *** *)
a(rewrite_tac[homeomorphism_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∃g⦁∀y⦁y ∈ Space⋎T τ ⇒ g y ∈ Space⋎T σ ∧ y = f(g y)⌝ THEN1 prove_∃_tac);
(* *** Goal "5.1" *** *)
a(REPEAT strip_tac THEN cases_tac ⌜y' ∈ Space⋎T τ⌝ THEN asm_rewrite_tac[]);
a(GET_NTH_ASM_T 4 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "5.2" *** *)
a(∃_tac⌜g⌝ THEN rewrite_tac[continuous_def] THEN REPEAT strip_tac);
(* *** Goal "5.2.1" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "5.2.2" *** *)
a(LIST_GET_NTH_ASM_T [3] all_fc_tac);
a(LEMMA_T⌜{x|x ∈ Space⋎T τ ∧ g x ∈ A} = {y|∃ x⦁ x ∈ A ∧ y = f x}⌝ asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "5.2.2.1" *** *)
a(∃_tac⌜g x⌝ THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
(* *** Goal "5.2.2.2" *** *)
a(all_var_elim_asm_tac1);
a(all_fc_tac[∈_space_t_thm]);
a(GET_NTH_ASM_T 9 ante_tac THEN rewrite_tac[continuous_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
(* *** Goal "5.2.2.3" *** *)
a(all_var_elim_asm_tac1);
a(all_fc_tac[∈_space_t_thm]);
a(LEMMA_T⌜g(f x') = x'⌝ asm_rewrite_thm_tac);
a(GET_NTH_ASM_T 9 ante_tac THEN rewrite_tac[continuous_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [9] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [14] all_fc_tac);
a(conv_tac eq_sym_conv THEN REPEAT strip_tac);
(* *** Goal "5.2.3" *** *)
a(GET_NTH_ASM_T 4 ante_tac THEN rewrite_tac[continuous_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [9] all_fc_tac);
a(conv_tac eq_sym_conv THEN REPEAT strip_tac);
(* *** Goal "5.2.4" *** *)
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(all_var_elim_asm_tac1);
a(LEMMA_T⌜g(f x) = x⌝ asm_rewrite_thm_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(conv_tac eq_sym_conv THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%
A function is homeomorphism iff it is one-to-one (on the space of its domain), onto (the space of its range),
continuous and closed:
=SML

val ⦏homeomorphism_one_one_closed_mapping_thm⦎ = save_thm ( "homeomorphism_one_one_closed_mapping_thm", (
set_goal([], ⌜∀f σ τ⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	(	f ∈ (σ, τ) Homeomorphism
	⇔	(∀x y⦁ x ∈ Space⋎T σ ∧ y ∈ Space⋎T σ ∧ f x = f y ⇒ x = y)
	∧	(∀y⦁ y ∈ Space⋎T τ ⇒ ∃x⦁x ∈ Space⋎T σ ∧ y = f x)
	∧	f ∈ (σ, τ) Continuous
	∧	(∀A⦁A ∈ σ Closed ⇒ {y | ∃x⦁ x ∈ A ∧ y = f x} ∈ τ Closed))
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[homeomorphism_one_one_thm]);
(* *** Goal "2" *** *)
a(bc_thm_tac homeomorphism_onto_thm);
a(∃_tac⌜τ⌝ THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac [homeomorphism_def] THEN REPEAT strip_tac);
(* *** Goal "4" *** *)
a(all_fc_tac[homeomorphism_closed_mapping_thm]);
(* *** Goal "5" *** *)
a(rewrite_tac[homeomorphism_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∃g⦁∀y⦁y ∈ Space⋎T τ ⇒ g y ∈ Space⋎T σ ∧ y = f(g y)⌝ THEN1 prove_∃_tac);
(* *** Goal "5.1" *** *)
a(REPEAT strip_tac THEN cases_tac ⌜y' ∈ Space⋎T τ⌝ THEN asm_rewrite_tac[]);
a(GET_NTH_ASM_T 4 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "5.2" *** *)
a(∃_tac⌜g⌝ THEN rewrite_tac[continuous_closed_thm] THEN REPEAT strip_tac);
(* *** Goal "5.2.1" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "5.2.2" *** *)
a(LIST_GET_NTH_ASM_T [3] all_fc_tac);
a(LEMMA_T⌜{x|x ∈ Space⋎T τ ∧ g x ∈ A} = {y|∃ x⦁ x ∈ A ∧ y = f x}⌝ asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "5.2.2.1" *** *)
a(∃_tac⌜g x⌝ THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
(* *** Goal "5.2.2.2" *** *)
a(all_var_elim_asm_tac1);
a(all_fc_tac[∈_closed_∈_space_t_thm]);
a(GET_NTH_ASM_T 7 ante_tac THEN rewrite_tac[continuous_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
(* *** Goal "5.2.2.3" *** *)
a(all_var_elim_asm_tac1);
a(all_fc_tac[∈_closed_∈_space_t_thm]);
a(LEMMA_T⌜g(f x') = x'⌝ asm_rewrite_thm_tac);
a(GET_NTH_ASM_T 7 ante_tac THEN rewrite_tac[continuous_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [12] all_fc_tac);
a(conv_tac eq_sym_conv THEN REPEAT strip_tac);
(* *** Goal "5.2.3" *** *)
a(GET_NTH_ASM_T 4 ante_tac THEN rewrite_tac[continuous_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [9] all_fc_tac);
a(conv_tac eq_sym_conv THEN REPEAT strip_tac);
(* *** Goal "5.2.4" *** *)
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(all_var_elim_asm_tac1);
a(LEMMA_T⌜g(f x) = x⌝ asm_rewrite_thm_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(conv_tac eq_sym_conv THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
The useful principle about functions between Hausdorff spaces.

=SML

val ⦏⊆_compact_homeomorphism_thm⦎ = save_thm ( "⊆_compact_homeomorphism_thm", (
set_goal([], ⌜∀f σ τ B C⦁
	σ ∈ Topology
∧	σ ∈ Hausdorff
∧	τ ∈ Topology
∧	τ ∈ Hausdorff
∧	C ∈ σ Compact
∧	B ⊆ C
∧	f ∈ (σ, τ) Continuous
∧	(∀x y⦁ x ∈ B ∧ y ∈ C ∧ f x = f y ⇒ x = y)
⇒	f ∈ (B ◁⋎T σ, {y | ∃x⦁ x ∈ B ∧ y = f x} ◁⋎T τ) Homeomorphism
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜B ◁⋎T σ ∈ Topology ∧ {y | ∃x⦁ x ∈ B ∧ y = f x} ◁⋎T τ ∈ Topology⌝
	THEN1 (REPEAT strip_tac THEN basic_topology_tac[]));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[homeomorphism_one_one_closed_mapping_thm]);
a(all_fc_tac[compact_closed_thm]);
a(lemma_tac⌜C ⊆ Space⋎T σ⌝ THEN1 all_fc_tac[closed_open_neighbourhood_thm]);
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀b c s⦁b ⊆ c ∧ c ⊆ s ⇒ b ⊆ s⌝]);
a(lemma_tac⌜{y|∃ x⦁ x ∈ B ∧ y = f x} ⊆ Space⋎T τ⌝);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 8 (bc_thm_tac o ∧_left_elim o rewrite_rule[continuous_def]));
a(LIST_DROP_NTH_ASM_T [2] (PC_T1"sets_ext1" all_fc_tac));
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm1]);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 10 bc_thm_tac THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [11] (PC_T1"sets_ext1" all_fc_tac));
(* *** Goal "2.2" *** *)
a(bc_thm_tac subspace_continuous_thm THEN asm_rewrite_tac[]);
a(prove_tac[]);
(* *** Goal "2.3" *** *)
a(POP_ASM_T ante_tac);
a(ALL_FC_T rewrite_tac[subspace_topology_closed_thm] THEN strip_tac);
a(rename_tac[(⌜B'⌝, "D")] THEN all_var_elim_asm_tac1);
a(lemma_tac⌜D ∩ C ∈ σ Closed⌝ THEN1 all_fc_tac[∩_closed_thm]);
a(lemma_tac⌜D ∩ C ⊆ C⌝ THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(all_fc_tac[closed_⊆_compact_thm]);
a(DROP_NTH_ASM_T 14 discard_tac THEN all_fc_tac[image_compact_thm]);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_fc_tac[compact_closed_thm]);
a(∃_tac⌜{y|∃ x⦁ x ∈ D ∩ C ∧ y = f x}⌝ THEN REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "2.3.1" *** *)
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [1, 16] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.3.2" *** *)
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal "2.3.3" *** *)
a(POP_ASM_T (strip_asm_tac o eq_sym_rule));
a(LIST_DROP_NTH_ASM_T [16] all_fc_tac THEN all_var_elim_asm_tac);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
pop_thm()
));



=TEX
\subsection{Interior, Boundary and Closure Operators}
=TEX
%%%%
%%%%
The interior and boundary of a set are subsets of the ambient space.
=SML

val ⦏interior_boundary_⊆_space_t_thm⦎ = save_thm ( "interior_boundary_⊆_space_t_thm", (
set_goal([], ⌜∀τ A⦁
	τ Interior A ⊆ Space⋎T τ
∧	τ Boundary A ⊆ Space⋎T τ
⌝);
a(rewrite_tac [interior_def, boundary_def] THEN REPEAT strip_tac THEN_LIST
	[PC_T1 "sets_ext1" prove_tac[space_t_def],
	 PC_T1 "sets_ext1" prove_tac[]]);
pop_thm()
));

=TEX
%%%%
%%%%
The interior a set is a subset of the set.
=SML

val ⦏interior_⊆_thm⦎ = save_thm ( "interior_⊆_thm", (
set_goal([], ⌜∀τ A⦁
	τ Interior A ⊆ A
⌝);
a(rewrite_tac [interior_def] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
The boundary of $A$ is the complement of the union of the interior of $A$ and
the interior of its complement.
=SML

val ⦏boundary_interior_thm⦎ = save_thm ( "boundary_interior_thm", (
set_goal([], ⌜∀τ A⦁
	τ ∈ Topology
⇒	τ Boundary A = Space⋎T τ \ (τ Interior A ∪ τ Interior (Space⋎T τ \ A))
⌝);
a(rewrite_tac [interior_def, boundary_def] THEN PC_T "sets_ext1" contr_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(DROP_NTH_ASM_T 4 (strip_asm_tac o ∀_elim⌜B⌝));
a(swap_nth_asm_concl_tac 1 THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN all_asm_fc_tac[∈_space_t_thm]);
(* *** Goal "4" *** *)
a(DROP_NTH_ASM_T 5 (strip_asm_tac o ∀_elim⌜B⌝));
a(PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
The interior of a product is the product of the interiors:
=SML

val ⦏interior_×_thm⦎ = save_thm ( "interior_×_thm", (
set_goal([], ⌜∀σ τ A B ⦁
	(σ ×⋎T τ) Interior (A × B) = (σ Interior A × τ Interior B)
⌝);
a(REPEAT strip_tac THEN PC_T "sets_ext1" strip_tac);
a(rewrite_tac[product_topology_def, interior_def, ×_def]
	THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [3] (PC_T1 "sets_ext1" all_fc_tac));
a(∃_tac⌜A'⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [3] (PC_T1 "sets_ext1" all_fc_tac));
a(∃_tac⌜B''⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(∃_tac ⌜B' × B''⌝ THEN rewrite_tac[×_def] THEN
	PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY (SOLVED_T (all_asm_fc_tac[])));
a(∃_tac⌜B'⌝ THEN ∃_tac⌜B''⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
A subset of a space is open iff it is disjoint from its boundary:
=SML

val ⦏open_⇔_disjoint_boundary_thm⦎ = save_thm ( "open_⇔_disjoint_boundary_thm", (
set_goal([], ⌜∀τ A ⦁
	τ ∈ Topology
⇒	(A ∈ τ ⇔ A ⊆ Space⋎T τ ∧ A ∩ τ Boundary A = {})
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]);
a(rewrite_tac[boundary_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(all_fc_tac[∈_space_t_thm]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(LIST_GET_NTH_ASM_T [3] all_fc_tac);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜x⌝)
	THEN_TRY SOLVED_T (PC_T1 "sets_ext1" asm_prove_tac[]));
a(∃_tac⌜B⌝ THEN PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
A subset of a space is closed iff it contains its boundary:
=SML

val ⦏closed_⇔_boundary_⊆_thm⦎ = save_thm ( "closed_⇔_boundary_⊆_thm", (
set_goal([], ⌜∀τ A ⦁
	τ ∈ Topology
⇒	(A ∈ τ Closed ⇔ A ⊆ Space⋎T τ ∧ τ Boundary A ⊆ A)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[boundary_interior_thm,
	closed_open_complement_thm,
	open_⇔_disjoint_boundary_thm]);
a(rewrite_tac[taut_rule⌜∀p q r⦁ (p ∧ q ⇔ p ∧ r) ⇔ (p ⇒ (q ⇔ r))⌝]);
a(⇒_tac THEN LEMMA_T ⌜Space⋎T τ \ A ⊆ Space⋎T τ ∧
		Space⋎T τ \ (Space⋎T τ \ A) = A⌝ rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜τ Interior (Space⋎T τ \ A) ⊆ Space⋎T τ \ A ∧ τ Interior A ⊆ A⌝
	THEN1 rewrite_tac[interior_⊆_thm]);
a(all_asm_ante_tac THEN PC_T1 "sets_ext1" rewrite_tac[]
	THEN contr_tac
	THEN(asm_fc_tac[] THEN asm_fc_tac[]));
pop_thm()
));

=TEX
%%%%
%%%%
The interior of a set is the union of all its open subsets.
=SML

val ⦏interior_⋃_thm⦎ = save_thm ( "interior_⋃_thm", (
set_goal([], ⌜∀τ A ⦁
	τ ∈ Topology
⇒	τ Interior A = ⋃{B | B ∈ τ ∧ B ⊆ A}
⌝);
a(REPEAT strip_tac THEN rewrite_tac[interior_def]);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
The closure of a set is the complement of the interior of its complement.
=SML

val ⦏closure_interior_complement_thm⦎ = save_thm ( "closure_interior_complement_thm", (
set_goal([], ⌜∀τ A ⦁
	τ ∈ Topology
⇒	τ Closure A = Space⋎T τ \ τ Interior (Space⋎T τ \ A)
⌝);
a(REPEAT strip_tac);
a(rewrite_tac[closure_def]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[closed_open_complement_thm, interior_⋃_thm]);
a(PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[empty_open_thm]);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN prove_tac[]);
(* *** Goal "2" *** *)
a(bc_thm_tac (pc_rule1 "sets_ext1" prove_rule[] ⌜x ∈ Space⋎T τ \ s ⇒ ¬x ∈ s⌝));
a(∃_tac⌜τ⌝ THEN DROP_NTH_ASM_T 3 bc_thm_tac);
a(asm_prove_tac[]);
a(LEMMA_T ⌜Space⋎T τ \ (Space⋎T τ \ s) = s⌝ asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(spec_nth_asm_tac 4 ⌜Space⋎T τ \ s⌝);
a(spec_nth_asm_tac 4 ⌜x'⌝);
pop_thm()
));

=TEX
\subsection{Discrete topology}

=TEX
%%%%
%%%%

=SML

val ⦏open_singletons_discrete_thm⦎ = save_thm ( "open_singletons_discrete_thm", (
set_goal([], ⌜
	∀τ⦁ τ ∈ Topology ⇒ (τ ∈ Discrete⋎T ⇔ (∀x⦁x ∈ Space⋎T τ ⇒ {x} ∈ τ))
⌝);
a(rewrite_tac[topology_def, discrete_t_def, space_t_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac THEN all_var_elim_asm_tac);
a(contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜A = ⋃{y | ∃z⦁ z ∈ A  ∧ y = {z}}⌝ once_rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(∃_tac⌜{x}⌝ THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1.2" *** *)
a(all_asm_fc_tac[] THEN all_var_elim_asm_tac);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(bc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀X⦁ x ⊆ X ∧ z ∈ x ⇒ z ∈ X⌝]);
a(∃_tac⌜A⌝ THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏discrete_t_continuous_thm⦎ = save_thm ( "discrete_t_continuous_thm", (
set_goal([], ⌜
	∀σ τ f⦁
	σ ∈ Topology ∧ τ ∈ Topology ∧ σ ∈ Discrete⋎T
⇒	(f ∈ (σ, τ) Continuous ⇔ (∀x⦁ x ∈ Space⋎T σ ⇒ f x ∈ Space⋎T τ))
⌝);
a(REPEAT ∀_tac THEN rewrite_tac [continuous_def, discrete_t_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
pop_thm()
));



=TEX
%%%%
%%%%

=SML

val ⦏connected_discrete_continuous_thm⦎ = save_thm ( "connected_discrete_continuous_thm", (
set_goal([], ⌜
∀σ τ f⦁
	σ ∈  Topology ∧ τ ∈ Topology ∧
	Space⋎T σ ∈ σ Connected ∧
	τ ∈ Discrete⋎T ∧
	f ∈ (σ, τ) Continuous
⇒	∃a⦁ (∀x⦁ x ∈ Space⋎T σ ⇒ f x = a)
⌝);
a(rewrite_tac[connected_def, continuous_def, discrete_t_def]
	THEN REPEAT strip_tac);
a(cases_tac ⌜Space⋎T σ = {}⌝ THEN_TRY asm_rewrite_tac[]);
a(POP_ASM_T (PC_T1 "sets_ext1" strip_asm_tac));
a(∃_tac⌜f x⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜{y | y ∈ Space⋎T τ ∧ ¬y = f x} ⊆ Space⋎T τ⌝ THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(lemma_tac⌜{y | y ∈ Space⋎T τ ∧ y = f x} ⊆ Space⋎T τ⌝ THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [7] (ALL_FC_T (MAP_EVERY ante_tac)));
a(rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac⌜Space⋎T σ ⊆ {x'|x' ∈ Space⋎T σ ∧ f x' ∈ Space⋎T τ ∧ ¬ f x' = f x}
           ∪ {x'|x' ∈ Space⋎T σ ∧ f x' ∈ Space⋎T τ ∧ f x' = f x}⌝);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY (SOLVED_T (all_asm_fc_tac[])));
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 11 (strip_asm_tac o
	list_∀_elim [⌜{x'|x' ∈ Space⋎T σ ∧ f x' ∈ Space⋎T τ ∧ ¬ f x' = f x}⌝,
		⌜{x'|x' ∈ Space⋎T σ ∧ f x' ∈ Space⋎T τ ∧ f x' = f x}⌝]));
(* *** Goal "2.1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 1);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2" *** *)
a(swap_nth_asm_concl_tac 1 THEN PC_T1 "sets_ext1" rewrite_tac[] THEN strip_tac);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.3" *** *)
a(swap_nth_asm_concl_tac 1 THEN PC_T1 "sets_ext1" rewrite_tac[] THEN strip_tac);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
pop_thm()
));



=TEX
\subsection{Covering Projections}
=TEX
%%%%
%%%%

=SML
val ⦏covering_projection_continuous_thm⦎ = save_thm ( "covering_projection_continuous_thm", (
set_goal([], ⌜∀σ τ p ⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
⇒	p ∈ (σ, τ) Continuous
⌝);
a(rewrite_tac [covering_projection_def] THEN taut_tac);
pop_thm()
));


=TEX
%%%%
%%%%
The following lemmas lead to the unique lifting property for connected sets.
=SML


val ⦏unique_lifting_lemma1⦎ = (* not saved *) snd ( "unique_lifting_lemma1", (
set_goal([], ⌜∀ρ σ τ; p:'b → 'c; f g : 'a → 'b ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
∧	f ∈ (ρ, σ) Continuous
∧	g ∈ (ρ, σ) Continuous
∧	(∀x⦁ x ∈ Space⋎T ρ ⇒ p(f x) = p(g x))
⇒	{x | x ∈ Space⋎T ρ ∧ g x = f x} ∈ ρ
⌝);
a(rewrite_tac[covering_projection_def] THEN REPEAT strip_tac);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]);
a(REPEAT strip_tac);
a(lemma_tac⌜f x ∈ Space⋎T σ⌝ THEN1 all_fc_tac[continuous_∈_space_t_thm]);
a(lemma_tac⌜p(f x) ∈ Space⋎T τ⌝ THEN1 all_fc_tac[continuous_∈_space_t_thm]);
a(LIST_DROP_NTH_ASM_T [8] all_fc_tac);
a(spec_nth_asm_tac 3 ⌜f x⌝);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a u s⦁a ∈ u ∧ u ⊆ s ⇒ a ∈ s⌝]);
a(all_fc_tac[continuous_open_thm]);
a(lemma_tac⌜g x ∈ A⌝ THEN1 asm_rewrite_tac[]);
a(∃_tac⌜{y|y ∈ Space⋎T ρ ∧ f y ∈ A} ∩ {y|y ∈ Space⋎T ρ ∧ g y ∈ A}⌝
	THEN ALL_FC_T asm_rewrite_tac[∩_open_thm]
	THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [11] all_fc_tac);
a(lemma_tac⌜f x' ∈ Space⋎T σ⌝ THEN1 all_fc_tac[continuous_∈_space_t_thm]);
a(lemma_tac⌜g x' ∈ Space⋎T σ⌝ THEN1 all_fc_tac[continuous_∈_space_t_thm]);
a(bc_thm_tac (∀_elim⌜p⌝ homeomorphism_one_one_thm));
a(MAP_EVERY ∃_tac [⌜C ◁⋎T τ⌝, ⌜A ◁⋎T σ⌝, ⌜p⌝]
	THEN ALL_FC_T asm_rewrite_tac[subspace_topology_thm,
		subspace_topology_space_t_thm2]);
a(LIST_GET_NTH_ASM_T [23] (ALL_FC_T rewrite_tac));
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏unique_lifting_lemma2⦎ = (* not saved *) snd ( "unique_lifting_lemma2", (
set_goal([], ⌜∀ρ σ τ; p:'b → 'c; f g : 'a → 'b ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
∧	f ∈ (ρ, σ) Continuous
∧	g ∈ (ρ, σ) Continuous
∧	(∀x⦁ x ∈ Space⋎T ρ ⇒ p(f x) = p(g x))
⇒	{x | x ∈ Space⋎T ρ ∧ ¬g x = f x} ∈ ρ
⌝);
a(rewrite_tac[covering_projection_def] THEN REPEAT strip_tac);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]);
a(REPEAT strip_tac);
a(all_fc_tac[continuous_∈_space_t_thm]);
a(lemma_tac⌜p(f x) ∈ Space⋎T τ⌝ THEN1 all_fc_tac[continuous_∈_space_t_thm]);
a(LIST_DROP_NTH_ASM_T [9] all_fc_tac);
a(LIST_GET_NTH_ASM_T [12] all_fc_tac);
a(POP_ASM_T (strip_asm_tac o eq_sym_rule));
a(lemma_tac⌜p(g x) ∈ C⌝
	THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a u s⦁a ∈ u ∧ u ⊆ s ⇒ a ∈ s⌝]);
a(all_fc_tac[continuous_open_thm]);
a(∃_tac⌜{y|y ∈ Space⋎T ρ ∧ f y ∈ A'} ∩ {y|y ∈ Space⋎T ρ ∧ g y ∈ A}⌝
	THEN ALL_FC_T asm_rewrite_tac[∩_open_thm]
	THEN REPEAT strip_tac);
a(PC_T "sets_ext1" contr_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜ ∀a b x y⦁x ∈ a ∧ y ∈ b ∧ y = x ⇒ ¬a ∩ b  = {}⌝]);
a(LIST_DROP_NTH_ASM_T [22] all_fc_tac THEN all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [17] all_fc_tac);
a(swap_nth_asm_concl_tac 24);
a(lemma_tac⌜f x' ∈ Space⋎T σ⌝ THEN1 all_fc_tac[continuous_∈_space_t_thm]);
a(lemma_tac⌜g x' ∈ Space⋎T σ⌝ THEN1 all_fc_tac[continuous_∈_space_t_thm]);
a(bc_thm_tac (∀_elim⌜p⌝ homeomorphism_one_one_thm));
a(MAP_EVERY ∃_tac [⌜C ◁⋎T τ⌝, ⌜A ◁⋎T σ⌝, ⌜p⌝]
	THEN ALL_FC_T asm_rewrite_tac[subspace_topology_thm,
		subspace_topology_space_t_thm2]);
pop_thm()
));

=TEX
%%%%
%%%%
The unique lifting property for continuous functions from connected sets to covering projections.
=SML
val ⦏unique_lifting_thm⦎ = save_thm ( "unique_lifting_thm", (
set_goal([], ⌜∀ρ σ τ; p:'b → 'c ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	Space⋎T ρ ∈ ρ Connected
∧	p ∈ (σ, τ) CoveringProjection
⇒	(ρ, (p, σ, τ)) ∈ UniqueLiftingProperty
⌝);
a(rewrite_tac [unique_lifting_property_def] THEN REPEAT strip_tac
	THEN1 all_fc_tac[covering_projection_continuous_thm]);
a(swap_nth_asm_concl_tac 9 THEN rewrite_tac[connected_def]
	THEN REPEAT strip_tac);
a(all_fc_tac[unique_lifting_lemma1, unique_lifting_lemma2]);
a(∃_tac⌜{x | x ∈ Space⋎T ρ ∧ g x = f x}⌝ THEN REPEAT strip_tac);
a(∃_tac⌜{x | x ∈ Space⋎T ρ ∧ ¬g x = f x}⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜a⌝ THEN asm_rewrite_tac[]);
pop_thm()
));
=TEX
%%%%
%%%%
The unique lifting property formulated to be easy to use with back-chaining.
=SML
val ⦏unique_lifting_bc_thm⦎ = save_thm ( "unique_lifting_bc_thm", (
set_goal([], ⌜∀ρ σ τ; p:'b → 'c; f g : 'a → 'b; a : 'a ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	Space⋎T ρ ∈ ρ Connected
∧	p ∈ (σ, τ) CoveringProjection
∧	f ∈ (ρ, σ) Continuous
∧	g ∈ (ρ, σ) Continuous
∧	(∀ x⦁ x ∈ Space⋎T ρ ⇒ p (f x) = p (g x))
∧	a ∈ Space⋎T ρ
∧	g a = f a
⇒	(∀ x⦁ x ∈ Space⋎T ρ ⇒ g x = f x)
⌝);
a(REPEAT strip_tac THEN ALL_FC_T (MAP_EVERY ante_tac) [unique_lifting_thm]);
a(rewrite_tac[unique_lifting_property_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
pop_thm()
));

=TEX
\section{METRIC SPACES --- THEOREMS}
=SML
open_theory "metric_spaces";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=TEX
\subsection{The Definitions}
=SML
val ⦏metric_def⦎ = get_spec⌜Metric⌝;
val ⦏metric_topology_def⦎ = get_spec⌜$MetricTopology⌝;
val ⦏list_metric_def⦎ = get_spec⌜ListMetric⌝;
=TEX
%%%%
%%%%

=SML

val ⦏metric_topology_thm⦎ = save_thm ( "metric_topology_thm", (
set_goal([], ⌜∀D⦁D ∈ Metric ⇒ D MetricTopology ∈ Topology⌝);
a(rewrite_tac[topology_def, metric_def, metric_topology_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x b c⦁x ∈ b ∧ b ⊆ c ⇒ x ∈  c⌝]);
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(∃_tac⌜e⌝ THEN REPEAT strip_tac);
a(∃_tac⌜s⌝ THEN ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [3, 4] all_fc_tac);
a(cases_tac⌜e ≤ e'⌝);
(* *** Goal "2.1" *** *)
a(∃_tac⌜e⌝ THEN PC_T1 "predicates" REPEAT strip_tac);
a(lemma_tac⌜D(x, y) < e'⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4, 6] all_fc_tac THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(∃_tac⌜e'⌝ THEN PC_T1 "predicates" REPEAT strip_tac);
a(lemma_tac⌜D(x, y) < e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4, 6] all_fc_tac THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏space_t_metric_topology_thm⦎ = save_thm ( "space_t_metric_topology_thm", (
set_goal([], ⌜∀D⦁
	D ∈ Metric
⇒	Space⋎T (D MetricTopology) = Universe
⌝);
a(PC_T1 "sets_ext1" rewrite_tac[metric_def, metric_topology_def, space_t_def]
	THEN REPEAT strip_tac);
a(∃_tac⌜Universe⌝ THEN rewrite_tac[]);
a(∃_tac⌜1/2⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%


=SML

val ⦏open_ball_open_thm⦎ = save_thm ( "open_ball_open_thm", (
set_goal([], ⌜∀D e x⦁ℕℝ 0 <  e ∧ D ∈ Metric ⇒ {y | D (x, y) < e} ∈ D MetricTopology⌝);
a(rewrite_tac[metric_topology_def, metric_def] THEN REPEAT strip_tac);
a(∃_tac⌜e - D(x, x')⌝ THEN REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜D(x, y) ≤ D(x, x') + D(x', y)⌝ THEN1 asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%


=SML

val ⦏open_ball_neighbourhood_thm⦎ = save_thm ( "open_ball_neighbourhood_thm", (
set_goal([], ⌜∀D e x⦁ℕℝ 0 <  e ∧ D ∈ Metric ⇒ x ∈ {y | D(x, y) < e}⌝);
a(rewrite_tac[metric_def] THEN REPEAT strip_tac);
a(lemma_tac⌜D(x, x) = ℕℝ 0⌝ THEN asm_rewrite_tac[]);
pop_thm()
));



=TEX
%%%%
%%%%

=SML

val ⦏metric_topology_hausdorff_thm⦎ = save_thm ( "metric_topology_hausdorff_thm", (
set_goal([], ⌜∀D⦁
	D ∈ Metric
⇒	D MetricTopology ∈ Hausdorff
⌝);
a(REPEAT strip_tac THEN TOP_ASM_T ante_tac);
a(rewrite_tac[metric_def, hausdorff_def, space_t_metric_topology_thm]
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 ante_tac);
a(lemma_tac⌜0. ≤ D(x, y) ∧ ¬D(x, y) = 0.⌝
	THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜0. < 1/2 * D(x, y)⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN strip_tac);
a(∃_tac⌜{z | D(x, z) < 1/2 * D(x, y)}⌝
	THEN ∃_tac⌜{z | D(y, z) < 1/2 * D(x, y)}⌝
	THEN ALL_FC_T rewrite_tac[open_ball_open_thm]);
a(POP_ASM_T ante_tac
	THEN LEMMA_T⌜∀z⦁ D(z, z) = 0.⌝ asm_rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(LEMMA_T⌜D(x, y) ≤ D(x, x') + D(x', y)⌝ ante_tac
	THEN1 DROP_NTH_ASM_T 10 rewrite_thm_tac);
a(rewrite_tac[]);
a(LEMMA_T ⌜D(x', y) = D(y, x')⌝ rewrite_thm_tac
	THEN1 (DROP_NTH_ASM_T 3
		(fn th => conv_tac(LEFT_C(once_rewrite_conv[th])))
		THEN REPEAT strip_tac));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏product_metric_thm⦎ = save_thm ( "product_metric_thm", (
set_goal([], ⌜∀D1 D2⦁
	D1 ∈ Metric ∧ D2 ∈ Metric
⇒	(λ((x1, x2), (y1, y2))⦁ D1(x1, y1) + D2(x2, y2)) ∈ Metric
⌝);
a(rewrite_tac[metric_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y⦁ℕℝ 0 ≤ x ∧ ℕℝ 0 ≤ y ⇒ ℕℝ 0 ≤ x + y⌝) THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac ⌜ℕℝ 0 ≤ D1(Fst x, Fst y) ∧ ℕℝ 0 ≤ D2(Snd x, Snd y)⌝
	THEN1 asm_rewrite_tac[]);
a(lemma_tac ⌜D1(Fst x, Fst y) = ℕℝ 0 ∧ D2(Snd x, Snd y) = ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
a(pure_once_rewrite_tac[prove_rule[]⌜∀p⦁p = (Fst p, Snd p)⌝]);
a(pure_asm_rewrite_tac[] THEN rewrite_tac[]);
(* *** Goal "3" *** *)
a(LEMMA_T⌜x = y ∧ (∀x⦁ D1(x, x) = ℕℝ 0) ∧ (∀y⦁D2(y, y) = ℕℝ 0)⌝ rewrite_thm_tac
	THEN LIST_GET_NTH_ASM_T [1, 4, 8] rewrite_tac);
(* *** Goal "4" *** *)
a(GET_NTH_ASM_T 6 (rewrite_thm_tac o ∀_elim⌜Fst y⌝));
a(GET_NTH_ASM_T 2 (rewrite_thm_tac o ∀_elim⌜Snd y⌝));
(* *** Goal "5" *** *)
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c d e f:ℝ⦁a ≤ c + e ∧ b ≤ d + f ⇒ a + b ≤ (c + d) + e + f⌝));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏product_metric_topology_thm⦎ = save_thm ( "product_metric_topology_thm", (
set_goal([], ⌜∀D1 D2⦁
	D1 ∈ Metric ∧ D2 ∈ Metric
⇒	(λ((x1, x2), (y1, y2))⦁ D1(x1, y1) + D2(x2, y2)) MetricTopology   =
	(D1 MetricTopology ×⋎T D2 MetricTopology)
⌝);
a(rewrite_tac[metric_def, metric_topology_def, product_topology_def] THEN
	PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(lemma_tac⌜ℕℝ 0 < (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(∃_tac⌜{x1 | D1(x', x1)  < (1/2)*e}⌝ THEN ∃_tac⌜{x2 | D2(y, x2)  < (1/2)*e}⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(∃_tac⌜(1/2)*e - D1(x' , x'')⌝ THEN REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜D1(x', y') ≤ D1(x', x'') + D1(x'', y')⌝ THEN1 GET_NTH_ASM_T 11 rewrite_thm_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜(1/2)*e - D2(y , x'')⌝ THEN REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜D2(y, y') ≤ D2(y, x'') + D2(x'', y')⌝ THEN1 GET_NTH_ASM_T 7 rewrite_thm_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.3" *** *)
a(LEMMA_T ⌜∀x⦁ D1(x, x) = ℕℝ 0⌝ asm_rewrite_thm_tac
	THEN1 LIST_GET_NTH_ASM_T [1, 11] rewrite_tac);
(* *** Goal "1.4" *** *)
a(LEMMA_T ⌜∀x⦁ D2(x, x) = ℕℝ 0⌝ asm_rewrite_thm_tac
	THEN LIST_GET_NTH_ASM_T [1, 7] rewrite_tac);
(* *** Goal "1.5" *** *)
a(rewrite_tac[×_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (bc_thm_tac o rewrite_rule[]));
a(rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 2 (ante_tac o list_∀_elim[⌜Fst x'⌝, ⌜Snd x'⌝]));
a(rewrite_tac[] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4, 5] all_fc_tac);
a(cases_tac⌜e < e'⌝);
(* *** Goal "2.1" *** *)
a(∃_tac⌜e⌝ THEN REPEAT strip_tac);
a(bc_thm_tac (pc_rule1 "sets_ext1" prove_rule[]⌜∀a x y⦁ a ⊆ x ∧ y ∈ a ⇒ y ∈ x⌝));
a(∃_tac⌜A × B⌝ THEN REPEAT strip_tac);
a(lemma_tac ⌜ℕℝ 0 ≤ D1 (Fst x', Fst y) ∧ ℕℝ 0 ≤  D2 (Snd x', Snd y)⌝
	THEN1 LIST_GET_NTH_ASM_T [14, 18] rewrite_tac);
a(lemma_tac ⌜D1 (Fst x', Fst y) < e' ∧ D2 (Snd x', Snd y) < e⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T[7, 9] all_fc_tac);
a(rewrite_tac[×_def] THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(∃_tac⌜e'⌝ THEN REPEAT strip_tac);
a(bc_thm_tac (pc_rule1 "sets_ext1" prove_rule[]⌜∀a x y⦁ a ⊆ x ∧ y ∈ a ⇒ y ∈ x⌝));
a(∃_tac⌜A × B⌝ THEN REPEAT strip_tac);
a(lemma_tac ⌜ℕℝ 0 ≤ D1 (Fst x', Fst y) ∧ ℕℝ 0 ≤  D2 (Snd x', Snd y)⌝
	THEN1 LIST_GET_NTH_ASM_T [14, 18] rewrite_tac);
a(lemma_tac ⌜D1 (Fst x', Fst y) < e' ∧ D2 (Snd x', Snd y) < e⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T[7, 9] all_fc_tac);
a(rewrite_tac[×_def] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏lebesgue_number_thm⦎ = save_thm ( "lebesgue_number_thm", (
set_goal([], ⌜∀D X U⦁
	D ∈ Metric
∧	X ∈ (D MetricTopology) Compact
∧	U ⊆ D MetricTopology
∧	X ⊆ ⋃U
⇒	∃e⦁ ℕℝ 0 < e
∧	∀x⦁ x ∈ X ⇒ ∃A⦁ x ∈  A ∧ A ∈ U ∧ ∀y⦁ D(x, y) < e ⇒ y ∈ A
⌝);
a(contr_tac);
a(all_fc_tac [metric_topology_thm]);
a(lemma_tac⌜∃s⦁(∀m:ℕ⦁ s m ∈ X) ∧ (∀A; m:ℕ⦁A ∈ U ⇒ ∃y⦁ D(s m, y) < ℕℝ (m + 1) ⋏-⋏1 ∧ ¬y ∈ A)⌝
	THEN1 (prove_∃_tac THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a(lemma_tac⌜ℕℝ 0 < ℕℝ (m' + 1)⋏-⋏1⌝ THEN1
	(bc_thm_tac  ℝ_0_less_0_less_recip_thm THEN
		rewrite_tac [ℕℝ_less_thm] THEN PC_T1 "lin_arith" prove_tac[]));
a(spec_nth_asm_tac 3 ⌜ℕℝ (m' + 1)⋏-⋏1⌝);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜A⌝);
(* *** Goal "1.1" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(LEMMA_T ⌜D(x, x) = ℕℝ 0⌝ asm_rewrite_thm_tac);
a(DROP_NTH_ASM_T 11 (rewrite_thm_tac o rewrite_rule[metric_def]));
(* *** Goal "1.2" *** *)
a(∃_tac⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(all_fc_tac[compact_sequentially_compact_thm]);
a(DROP_NTH_ASM_T 7 (PC_T1 "sets_ext1" strip_asm_tac));
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀a⦁s' ∈ U ∧ U ⊆ a ⇒ s' ∈ a⌝]);
a(spec_nth_asm_tac 4 ⌜s'⌝);
a(GET_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[metric_topology_def]));
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(lemma_tac⌜ℕℝ 0  < (1/2)*e ⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 3 discard_tac);
a(lemma_tac⌜{y | D(x, y) < (1/2)*e} ∈ D MetricTopology⌝
	THEN1 (bc_thm_tac open_ball_open_thm THEN REPEAT strip_tac));
a(LEMMA_T⌜x ∈ {y | D(x, y) < (1/2)*e}⌝ asm_tac
	THEN1 (bc_thm_tac open_ball_neighbourhood_thm THEN REPEAT strip_tac));
a(PC_T1 "predicates" (spec_nth_asm_tac 9) ⌜{y | D(x, y) < (1/2)*e}⌝);
a(all_fc_tac[ℝ_archimedean_recip_thm]);
a(spec_nth_asm_tac 2 ⌜m+1⌝);
a(lemma_tac⌜ℕℝ 0 < ℕℝ(m+1) ∧ ℕℝ 0 < ℕℝ(n+1) ∧ ℕℝ(m+1) < ℕℝ(n+1)⌝
	THEN1 (rewrite_tac [ℕℝ_less_thm] THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ(n+1)⋏-⋏1  < ℕℝ(m+1)⋏-⋏1⌝
	THEN1 (bc_thm_tac ℝ_less_recip_less_thm THEN REPEAT strip_tac));
a(lemma_tac⌜ℕℝ 0 < ℕℝ(m+1)⋏-⋏1 ∧ ℕℝ 0 < ℕℝ(n+1)⋏-⋏1⌝
	THEN1 (ALL_FC_T rewrite_tac [ℝ_0_less_0_less_recip_thm]));
a(list_spec_nth_asm_tac 21 [⌜s'⌝, ⌜n⌝]);
a(swap_nth_asm_concl_tac 1 THEN DROP_NTH_ASM_T 15 bc_thm_tac);
a(lemma_tac⌜D(x, y) ≤ D(x, s n) + D(s n, y)⌝
	THEN1 DROP_NTH_ASM_T 27 (rewrite_thm_tac o rewrite_rule[metric_def]));
a(lemma_tac⌜D(s n, y) < (1/2)*e⌝
	THEN1 REPEAT (all_fc_tac[ℝ_less_trans_thm]));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏collar_thm⦎ = save_thm ( "collar_thm", (
set_goal([], ⌜∀D X U⦁
	D ∈ Metric
∧	X ∈ (D MetricTopology) Compact
∧	A ∈ D MetricTopology
∧	X ⊆ A
⇒	∃e⦁ ℕℝ 0 < e
∧	∀x y⦁ x ∈ X ∧ y ∈ Space⋎T τ ∧ D(x, y) < e ⇒ y ∈ A
⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜X ⊆ ⋃{A} ∧ {A} ⊆ D MetricTopology⌝  THEN1 asm_rewrite_tac[enum_set_clauses]);
a(strip_asm_tac (list_∀_elim[⌜D⌝, ⌜X⌝, ⌜{A}⌝] lebesgue_number_thm));
a(∃_tac⌜e⌝ THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
pop_thm()
));
=TEX
%%%%
%%%%
The proof that the list metric function actually maps metrics to metrics is a little
tricky.
Naive nested inductions work for the properties involving just two
variables, but the triangle inequality is not tractable to the naive approach.
For the triangle inequality, we first show decompose the list metric
function into a sum of two simpler functions. $P\;D$ here is the pseudo-metric mentioned in the discussion of the definition.
=SML



val ⦏list_pseudo_metric_lemma1⦎ = (* not saved *) snd ( "list_pseudo_metric_lemma1", (
set_goal([], ⌜∃P⦁
	(∀D x v y w⦁
	P D ([], []) = 0.
∧	P D (Cons x v, []) = D(x, Arbitrary) + P D (v, [])
∧	P D ([], Cons y w) = D(Arbitrary, y) + P D ([], w)
∧	P D (Cons x v, Cons y w) = D (x, y) + P D (v, w))
∧	∀D v w⦁
	ListMetric D (v, w) =
	Abs(ℕℝ(#v) - ℕℝ (#w)) + P D (v, w)
⌝);
a(strip_asm_tac (prove_∃_rule
 ⌜∃P⦁
	∀D: 'a × 'a → ℝ; x v y w⦁
	P D ([], []) = 0.
∧	P D (Cons x v, []) = D(x, Arbitrary) + P D (v, [])
∧	P D ([], Cons y w) = D(Arbitrary, y) + P D ([], w)
∧	P D (Cons x v, Cons y w) = D (x, y) + P D (v, w)
⌝));
a(∃_tac⌜P⌝ THEN asm_rewrite_tac[] THEN REPEAT_N 2 strip_tac);
a(list_induction_tac⌜v⌝ THEN REPEAT strip_tac
	THEN list_induction_tac⌜w:'a LIST⌝
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[list_metric_def, length_def,
		ℕℝ_plus_homomorphism_thm]);
(* *** Goal "1" *** *)
a(lemma_tac⌜0. ≤ ℕℝ(#w)⌝ THEN1 rewrite_tac[ℕℝ_≤_thm]);
a(LEMMA_T⌜∀x⦁0. ≤ x ⇒ ¬0. ≤ ~x + ~1.⌝
	(fn th => all_fc_tac[th])
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_abs_def] THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜0. ≤ ℕℝ(#v)⌝ THEN1 rewrite_tac[ℕℝ_≤_thm]);
a(LEMMA_T⌜∀x⦁0. ≤ x ⇒ 0. ≤ x + 1.⌝
	(fn th => all_fc_tac[th])
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_abs_def] THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "3" *** *)
a(conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(cases_tac⌜0. ≤ ℕℝ (# v) + ~ (ℕℝ (# w))⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
Now we show that if $P$ is as in the preceding lemma and $D$ satisfies
the triangle inequality and the rule $D(x, x) = 0$, then $P\;D$ satisfies
the triangle inequality. To reduce the number of case splits and inductions,
we prove that $P\;D$ is invariant under padding
on the right with the arbitrary element. This means that we can pad
the three vectors and so reduce to the case when the lengths of the vectors are equal. This then admits to an induction on the common length.
=SML

val ⦏list_pseudo_metric_lemma2⦎ = (* not saved *) snd ( "list_pseudo_metric_lemma2", (
set_goal([], ⌜∀P; D : 'a × 'a → ℝ⦁
	(∀x v y w⦁
	P D ([], []) = 0.
∧	P D (Cons x v, []) = D(x, Arbitrary) + P D (v, [])
∧	P D ([], Cons y w) = D(Arbitrary, y) + P D ([], w)
∧	P D (Cons x v, Cons y w) = D (x, y) + P D (v, w))
∧	(∀x⦁ D (x, x) = 0.)
∧	(∀x y z⦁ D (x, z) ≤ D (x, y) + D(y, z))
⇒	P D (u, w) ≤ P D (u, v) + P D (v, w)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜
	(∀v w⦁ P D (v @ [Arbitrary], w) = P D (v, w))
∧	(∀w v⦁ P D (v, w @ [Arbitrary]) = P D (v, w))⌝
	THEN1 ∧_tac);
(* *** Goal "1" *** *)
a(∀_tac THEN list_induction_tac ⌜v:'a LIST⌝ THEN asm_rewrite_tac[append_def]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(list_induction_tac ⌜w⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(list_induction_tac ⌜w⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∀_tac THEN list_induction_tac ⌜w:'a LIST⌝ THEN asm_rewrite_tac[append_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(list_induction_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(list_induction_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜∃pad⦁∀j v⦁ pad v 0 = v ∧ pad v (j+1) = pad v j @ [Arbitrary]⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∀j v⦁#(pad v j) = #v + j⌝
	THEN1 (∀_tac THEN induction_tac⌜j:ℕ⌝
	THEN asm_rewrite_tac[length_append_thm, length_def, plus_assoc_thm]));
a(lemma_tac⌜∀j v w⦁P D (pad v j, w) = P D (v, w)⌝
	THEN1 (∀_tac THEN induction_tac⌜j:ℕ⌝
	THEN asm_rewrite_tac[]));
a(lemma_tac⌜∀j v w⦁P D (v, pad w j) = P D (v, w)⌝
	THEN1 (∀_tac THEN induction_tac⌜j:ℕ⌝
	THEN asm_rewrite_tac[]));
a(lemma_tac⌜∃i j k⦁ #u + i = #v + j ∧ #v + j = #w + k⌝
	THEN1 (MAP_EVERY ∃_tac [⌜#v + #w⌝, ⌜#u + #w⌝, ⌜#u + #v⌝]
		THEN1 PC_T1 "lin_arith" prove_tac[]));
a(lemma_tac⌜#(pad u i) = #(pad v j) ∧ #(pad v j) = #(pad w k)⌝
	THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜
	P D (u, w) = P D (pad u i, pad w k)
∧	P D (u, v) = P D (pad u i, pad v j)
∧	P D (v, w) = P D (pad v j, pad w k)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜∀u v w⦁#u = #v ∧ #v =#w ⇒ P D (u, w) ≤ P D (u, v) + P D (v, w)⌝
	(fn th => bc_thm_tac th THEN REPEAT strip_tac));
a(LIST_DROP_NTH_ASM_T [1, 2, 3, 4] discard_tac THEN REPEAT strip_tac);
a(lemma_tac⌜∃m⦁ #u = m⌝ THEN1 prove_∃_tac);
a(LIST_DROP_NTH_ASM_T [2, 3, 1] (MAP_EVERY ante_tac));
a(MAP_EVERY intro_∀_tac1 [⌜w⌝, ⌜v⌝, ⌜u⌝]);
a(induction_tac⌜m⌝);
(* *** Goal "3.1" *** *)
a(REPEAT ∀_tac THEN strip_tac THEN asm_rewrite_tac[]);
a(STRIP_T (strip_asm_tac o eq_sym_rule) THEN asm_rewrite_tac[]);
a(STRIP_T (ante_tac o eq_sym_rule)
	THEN POP_ASM_T ante_tac THEN POP_ASM_T ante_tac);
a(rewrite_tac[length_0_thm]);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "3.2" *** *)
a(REPEAT ∀_tac THEN strip_tac THEN asm_rewrite_tac[]);
a(STRIP_T (strip_asm_tac o eq_sym_rule) THEN asm_rewrite_tac[]);
a(STRIP_T (strip_asm_tac o eq_sym_rule));
a(MAP_EVERY (fn t => strip_asm_tac(∀_elim t list_cases_thm)
	THEN all_var_elim_asm_tac1 THEN1
		(all_asm_ante_tac THEN rewrite_tac[length_def]))
	[⌜u⌝, ⌜v⌝, ⌜w⌝]);
a(LIST_DROP_NTH_ASM_T [1, 2, 3] (MAP_EVERY (strip_asm_tac o rewrite_rule[length_def])));
a(asm_rewrite_tac[ℝ_plus_assoc_thm]);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b c x y z:ℝ⦁a ≤ b + c ∧ x ≤ y + z ⇒
		a + x ≤ b + y + c + z⌝)
	THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 (bc_thm_tac o rewrite_rule[taut_rule⌜
	∀p q r⦁p ⇒ q ⇒ r ⇔ p ∧ q ⇒ r⌝])
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
Now we can do the remaining properties by naive inductions.
We separate out non-negativity and symmetry for convenience.
=SML

val ⦏list_metric_nonneg_thm⦎ = save_thm ( "list_metric_nonneg_thm", (
set_goal([], ⌜∀D x⦁
	D ∈ Metric
⇒	0. ≤ ListMetric D (x, y)
⌝);
a(rewrite_tac[metric_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [1, 2, 3] discard_tac);
a(intro_∀_tac1⌜y⌝ THEN list_induction_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(list_induction_tac ⌜y⌝ THEN asm_rewrite_tac[list_metric_def] THEN REPEAT strip_tac);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁0. ≤ x ∧ 0. ≤ y ⇒ 0. ≤ 1. + x + y⌝)
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(list_induction_tac ⌜y⌝ THEN rewrite_tac[list_metric_def] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁0. ≤ x ∧ 0. ≤ y ⇒ 0. ≤ 1. + x + y⌝)
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁0. ≤ x ∧ 0. ≤ y ⇒ 0. ≤ x + y⌝)
	THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML


val ⦏list_metric_sym_thm⦎ = save_thm ( "list_metric_sym_thm", (
set_goal([], ⌜∀D x y⦁
	D ∈ Metric
⇒	ListMetric D (x, y) = ListMetric D (y, x)
⌝);
a(rewrite_tac[metric_def] THEN REPEAT strip_tac);
a(intro_∀_tac1⌜y⌝ THEN list_induction_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(list_induction_tac⌜y⌝ THEN REPEAT strip_tac
	THEN rewrite_tac[list_metric_def]);
a(DROP_NTH_ASM_T 3 (once_asm_rewrite_thm_tac o ∀_elim⌜x⌝)
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(strip_asm_tac(∀_elim⌜y⌝ list_cases_thm)
	THEN all_var_elim_asm_tac1 THEN rewrite_tac[list_metric_def]);
(* *** Goal "2.1" *** *)
a(POP_ASM_T rewrite_thm_tac);
a(DROP_NTH_ASM_T 2 (once_asm_rewrite_thm_tac o ∀_elim⌜x'⌝)
	THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 3 (once_asm_rewrite_thm_tac o ∀_elim⌜x'⌝)
	THEN strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML


val ⦏list_metric_metric_thm⦎ = save_thm ( "list_metric_metric_thm", (
set_goal([], ⌜∀D⦁
	D ∈ Metric
⇒	ListMetric D ∈ Metric
⌝);
a(REPEAT strip_tac THEN TOP_ASM_T ante_tac);
a(rewrite_tac[metric_def] THEN ⇒_tac);
a(all_fc_tac[list_metric_nonneg_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 4 discard_tac);
a(POP_ASM_T ante_tac THEN lemma_tac⌜∃m⦁ Length x = m⌝ THEN1 prove_∃_tac);
a(POP_ASM_T ante_tac THEN intro_∀_tac1⌜y⌝ THEN intro_∀_tac1⌜x⌝);
a(induction_tac⌜m⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(POP_ASM_T ante_tac THEN POP_ASM_T ante_tac
	THEN rewrite_tac[length_0_thm]
	THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac THEN strip_asm_tac(∀_elim⌜y⌝ list_cases_thm)
	THEN asm_rewrite_tac[list_metric_def]);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁0. ≤ x ∧ 0. ≤ y ⇒ ¬1. + x + y = 0.⌝)
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜¬x = []⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac1
	THEN all_asm_ante_tac THEN rewrite_tac[length_def]));
a(DROP_NTH_ASM_T 2 ante_tac THEN strip_asm_tac(∀_elim⌜x⌝ list_cases_thm));
a(strip_asm_tac(∀_elim⌜y⌝ list_cases_thm)
	THEN all_var_elim_asm_tac1 THEN1 asm_rewrite_tac[list_metric_def]);
(* *** Goal "2.2.1" *** *)
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁0. ≤ x ∧ 0. ≤ y ⇒ ¬1. + x + y = 0.⌝)
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[list_metric_def, length_def]);
a(REPEAT_UNTIL is_∧ strip_tac);
a(FC_T (MAP_EVERY ante_tac) [pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y⦁ x + y = 0. ∧ 0. ≤ x ∧ 0. ≤ y ⇒ x = 0. ∧ y = 0.⌝]);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac);
a(list_induction_tac⌜y⌝ THEN asm_rewrite_tac[list_metric_def]);
(* *** Goal "4" *** *)
a(bc_thm_tac list_metric_sym_thm THEN REPEAT strip_tac);
(* *** Goal "5" *** *)
a(strip_asm_tac list_pseudo_metric_lemma1 THEN asm_rewrite_tac[ℝ_plus_assoc_thm]);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b c x y z:ℝ⦁a ≤ b + c ∧ x ≤ y + z ⇒
		a + x ≤ b + y + c + z⌝)
	THEN REPEAT strip_tac);
(* *** Goal "5.1" *** *)
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜ℕℝ (# x) + ~ (ℕℝ (# z)) =
	(ℕℝ (# x) + ~ (ℕℝ (# y))) + (ℕℝ (# y) + ~ (ℕℝ (# z)))⌝, ℝ_abs_plus_thm]);
(* *** Goal "5.1" *** *)
a(bc_thm_tac list_pseudo_metric_lemma2);
a(DROP_NTH_ASM_T 5 discard_tac THEN asm_rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

=TEX
\section{THE REAL LINE AND THE PLANE --- THEOREMS}
=SML
open_theory "topology_ℝ";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=TEX
\subsection{The Definitions}
=SML
val ⦏d_ℝ_def⦎ = get_spec⌜D⋎R⌝;
val ⦏d_ℝ_2_def⦎ = get_spec⌜D⋎R2⌝;
val ⦏d_ℝ_2_def1⦎ = save_thm ( "d_ℝ_2_def1", (
set_goal([], ⌜∀xy1 xy2⦁ D⋎R2 (xy1, xy2) = Abs(Fst xy2 - Fst xy1)  + Abs(Snd xy2 - Snd  xy1)⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule[]⌜∀p:ℝ × ℝ⦁p = (Fst p, Snd p)⌝]);
a(pure_rewrite_tac[d_ℝ_2_def]);
a(rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

We show that the open sets as defined in \cite{LEMMA1/HOL/WRK066}  do indeed comprise a topology on
the real line with the expected basic properties. The proofs are very easy, because
most of the work has already been done in \cite{LEMMA1/HOL/WRK066}.
First, the open sets do form a topology:
%%%%
%%%%

=SML

val ⦏open_ℝ_topology_thm⦎ = save_thm ( "open_ℝ_topology_thm", (
set_goal([], ⌜O⋎R ∈ Topology⌝);
a(rewrite_tac[topology_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[⋃_open_ℝ_thm]);
(* *** Goal "2" *** *)
a(all_fc_tac[∩_open_ℝ_thm]);
pop_thm()
));

=TEX
The carrier set of the topology is the entire real line:
%%%%
%%%%

=SML

val ⦏space_t_ℝ_thm⦎ = save_thm ( "space_t_ℝ_thm", (
set_goal([], ⌜Space⋎T O⋎R = Universe⌝);
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(bc_thm_tac ∈_space_t_thm);
a(∃_tac⌜Universe⌝ THEN rewrite_tac[open_ℝ_topology_thm, empty_universe_open_closed_thm]);
pop_thm()
));

=TEX
The definition from \cite{LEMMA1/HOL/WRK066} of a closed set agrees with the abstract one:
%%%%
%%%%

=SML

val ⦏closed_closed_ℝ_thm⦎ = save_thm ( "closed_closed_ℝ_thm", (
set_goal([], ⌜O⋎R Closed = Closed⋎R⌝);
a(rewrite_tac[closed_def, closed_ℝ_def, space_t_ℝ_thm] THEN REPEAT strip_tac);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[pc_rule1"sets_ext1" prove_rule[complement_clauses]⌜∀a:'a SET⦁~(~a) = a⌝]);
(* *** Goal "2" *** *)
a(∃_tac⌜~x⌝ THEN
	asm_rewrite_tac[pc_rule1"sets_ext1" prove_rule[complement_clauses]⌜∀a:'a SET⦁~(~a) = a⌝]);
pop_thm()
));

=TEX
The definition from \cite{LEMMA1/HOL/WRK066} of a connected set agrees with the abstract one:
%%%%
%%%%

=SML

val ⦏compact_compact_ℝ_thm⦎ = save_thm ( "compact_compact_ℝ_thm", (
set_goal([], ⌜O⋎R Compact = Compact⋎R⌝);
a(rewrite_tac[compact_def, compact_ℝ_def, space_t_ℝ_thm] THEN REPEAT strip_tac);
pop_thm()
));

=TEX

Constant functions are continuous:
%%%%
%%%%

=SML

val ⦏open_ℝ_const_continuous_thm⦎ = save_thm("open_ℝ_const_continuous_thm",
	all_∀_intro(
	rewrite_rule[open_ℝ_topology_thm, space_t_ℝ_thm]
	(list_∀_elim[⌜σ : 'a SET SET⌝, ⌜O⋎R⌝] const_continuous_thm)));

=TEX

as is the identity function:
%%%%
%%%%

=SML

val ⦏open_ℝ_id_continuous_thm⦎ = save_thm("open_ℝ_id_continuous_thm",
	rewrite_rule[open_ℝ_topology_thm]
	(∀_elim⌜O⋎R⌝ id_continuous_thm));


=TEX
Finally (amongst the basic properties), functions are continuous in the abstract sense
iff they are everywhere continuous in the sense of \cite{LEMMA1/HOL/WRK066}.
%%%%
%%%%

=SML

val ⦏continuous_cts_at_ℝ_thm⦎ = save_thm ( "continuous_cts_at_ℝ_thm", (
set_goal([], ⌜∀f⦁ f ∈ (O⋎R, O⋎R) Continuous ⇔ ∀x⦁f Cts x⌝);
a(rewrite_tac[continuous_def, cts_open_ℝ_thm, space_t_ℝ_thm] THEN REPEAT strip_tac);
pop_thm()
));

val ⦏cts_at_ℝ_continuous_thm⦎ = save_thm( "cts_at_ℝ_continuous_thm",
	conv_rule(BINDER_C eq_sym_conv) continuous_cts_at_ℝ_thm);

=TEX
With a distant view to doing some algebraic topology, we now look at connectedness,
which was not much studied in \cite{LEMMA1/HOL/WRK066}. Our intention is to characterise the connected
subsets of the real line. The plan is to use material from this document and from \cite{LEMMA1/HOL/WRK066}
as appropriate to best effect. We show that the real line as a whole is connected using
the intermediate value theorem, from which we infer that closed intervals are connected
using a continous mapping of the real line onto a closed interval. From this we infer that
a subset of the real line is connected iff it contains the closed interval lying between
any two of its points, using the pointwise characterisation of connectedness and the
fact that closed intervals are connected.

That the real line is topologically connected is a consequence of the intermediate
value theorem: if the disjoint open sets $B$ and $C$ exhausted the real line,
then the function which is 0 on $B$ and 1 on $C$ would be continuous but
would not take on any real value (e.g., $1/2$) strictly between 0 and 1, contradicting
the intermediate value theorem. (That the real line is connected is proved in \cite{LEMMA1/HOL/WRK066}, but
the proof is not as nice as this one.)
%%%%
%%%%

=SML

val ⦏universe_ℝ_connected_thm⦎ = save_thm ( "universe_ℝ_connected_thm", (
set_goal([], ⌜Universe ∈ O⋎R Connected⌝);
a(rewrite_tac[connected_def, space_t_ℝ_thm] THEN PC_T1 "sets_ext1" rewrite_tac[]);
a(strip_asm_tac open_ℝ_topology_thm THEN contr_tac);
a(lemma_tac⌜∃f⦁∀t⦁ f t = if t ∈ B then ℕℝ 0 else ℕℝ 1⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜∀t⦁f Cts t⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[cts_open_ℝ_thm] THEN REPEAT strip_tac);
a(cases_tac⌜ℕℝ 0 ∈ A⌝ THEN cases_tac⌜ℕℝ 1 ∈ A⌝);
(* *** Goal "1.1" *** *)
a(LEMMA_T ⌜{x | f x ∈ A} = Space⋎T O⋎R⌝ rewrite_thm_tac THEN_LIST
	[rewrite_tac[space_t_ℝ_thm], ALL_FC_T rewrite_tac[space_t_open_thm]]);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN asm_rewrite_tac[]);
a(cases_tac ⌜x'' ∈ B⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(LEMMA_T ⌜{x | f x ∈ A} = B⌝  asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a(LEMMA_T ⌜{z | f z ∈ A} = C⌝  asm_rewrite_thm_tac);
a(LEMMA_T⌜∀t⦁t ∈ B ⇔ ¬t ∈ C⌝ asm_rewrite_thm_tac THEN1 asm_prove_tac[]);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "1.4" *** *)
a(LEMMA_T ⌜{x | f x ∈ A} = {}⌝ rewrite_thm_tac THEN_LIST
	[PC_T "sets_ext1" contr_tac, ALL_FC_T rewrite_tac[empty_open_thm]]);
a(POP_ASM_T ante_tac THEN spec_nth_asm_tac 8 ⌜x''⌝ THEN asm_rewrite_tac[]);
a(LEMMA_T⌜∀t⦁t ∈ B ⇔ ¬t ∈ C⌝ asm_rewrite_thm_tac THEN1 asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∀t⦁¬f t = 1/2⌝ THEN1 (strip_tac THEN cases_tac⌜t ∈ B⌝ THEN asm_rewrite_tac[]));
a(lemma_tac⌜f x = ℕℝ 1⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜f x' = ℕℝ 0⌝ THEN1
	(cases_tac ⌜x' ∈ B⌝ THEN asm_rewrite_tac[] THEN asm_prove_tac[]));
a(DROP_NTH_ASM_T 5 discard_tac);
a(lemma_tac⌜¬x = x'⌝ THEN1  (contr_tac THEN all_var_elim_asm_tac THEN asm_prove_tac[]));
a(strip_asm_tac (list_∀_elim[⌜x⌝, ⌜x'⌝] ℝ_less_cases_thm));
(* *** Goal "2.1" *** *)
a(ante_tac(list_∀_elim[⌜f⌝, ⌜x⌝, ⌜x'⌝] intermediate_value_thm)
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜1/2⌝  THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(ante_tac(list_∀_elim[⌜f⌝, ⌜x'⌝, ⌜x⌝] intermediate_value_thm)
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜1/2⌝  THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
We can now apply the theorem that continuous images of connected sets are connected
to show that closed intervals are connected, using a useful theorem from \cite{LEMMA1/HOL/WRK066}
to construct a continuous mapping of the real line onto any given closed interval.
%%%%
%%%%

=SML

val ⦏closed_interval_connected_thm⦎ = save_thm ( "closed_interval_connected_thm", (
set_goal([], ⌜∀x y⦁ x < y ⇒ ClosedInterval x y ∈ O⋎R Connected⌝);
a(REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜x⌝, ⌜y⌝,  ⌜λt:ℝ⦁t⌝] cts_extension_thm1));
a(asm_rewrite_tac[id_cts_thm,
	conv_rule(ONCE_MAP_C eq_sym_conv) continuous_cts_at_ℝ_thm] THEN strip_tac);
a(strip_asm_tac universe_ℝ_connected_thm THEN strip_asm_tac open_ℝ_topology_thm);
a(all_fc_tac[image_connected_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]);
a(bc_thm_tac(prove_rule[]⌜∀x y a⦁x = y ⇒ x ∈ a ⇒ y ∈ a⌝));
a(rewrite_tac[closed_interval_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1);
a(cases_tac⌜x'' < x⌝ THEN1 ALL_ASM_FC_T rewrite_tac[]);
a(cases_tac⌜y < x''⌝ THEN1
	(ALL_ASM_FC_T rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜x ≤ x'' ∧ x'' ≤ y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(cases_tac⌜y < x''⌝ THEN1 ALL_ASM_FC_T rewrite_tac[]);
a(cases_tac⌜x'' < x⌝ THEN1
	(ALL_ASM_FC_T rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜x ≤ x'' ∧ x'' ≤ y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜x'⌝ THEN ALL_ASM_FC_T asm_rewrite_tac[]);
pop_thm()
));


=TEX
We can now characterise the connected subsets of the real line as those
which sets which contain every point lying between any two members.
%%%%
%%%%

=SML

val ⦏subspace_ℝ_space_t_thm⦎ = save_thm ( "subspace_ℝ_space_t_thm", (
set_goal([], ⌜∀X⦁
		Space⋎T (X ◁⋎T O⋎R) = X⌝
);
a(strip_tac THEN bc_thm_tac subspace_topology_space_t_thm1);
a(rewrite_tac[open_ℝ_topology_thm, space_t_ℝ_thm]);
pop_thm()
));




=TEX
We can now characterise the connected subsets of the real line as those
which sets which contain every point lying between any two members.
%%%%
%%%%

=SML

val ⦏connected_ℝ_thm⦎ = save_thm ( "connected_ℝ_thm", (
set_goal([], ⌜∀X⦁
		X ∈ O⋎R Connected
	⇔	∀x y z⦁x ∈ X ∧ y ∈ X ∧ x ≤ z ∧ z ≤ y ⇒ z ∈ X⌝
);
a(REPEAT_N 3 strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[connected_def, ℝ_≤_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac THEN contr_tac);
a(strip_asm_tac (∀_elim⌜z⌝ half_infinite_intervals_open_thm));
a(lemma_tac⌜X ⊆ {t|t < z} ∪ {t | z < t}⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a((cases_tac⌜x' = z⌝ THEN1 all_var_elim_asm_tac) THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜X ∩ {t|t < z} ∩ {t | z < t} = {}⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(lemma_tac⌜¬X ⊆ {t|t < z}⌝ THEN PC_T "sets_ext1" contr_tac);
(* *** Goal "1.2.2.1" *** *)
a(spec_nth_asm_tac 1 ⌜y⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2.2" *** *)
a(lemma_tac⌜¬X ⊆ {t|z < t}⌝ THEN PC_T "sets_ext1" contr_tac);
(* *** Goal "1.2.2.2.1" *** *)
a(spec_nth_asm_tac 1 ⌜x⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2.2.2" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN strip_asm_tac open_ℝ_topology_thm);
a(bc_thm_tac connected_pointwise_bc_thm);
a(REPEAT strip_tac);
a(strip_asm_tac (list_∀_elim[⌜x⌝, ⌜y⌝] ℝ_less_cases_thm));
(* *** Goal "2.1" *** *)
a(∃_tac⌜ClosedInterval x y⌝);
a(ALL_FC_T rewrite_tac[closed_interval_connected_thm]);
a(PC_T1 "sets_ext1" rewrite_tac[closed_interval_def]);
a(REPEAT strip_tac THEN all_asm_fc_tac[] THEN asm_rewrite_tac[ℝ_≤_def]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜{x}⌝ THEN asm_rewrite_tac[enum_set_clauses]);
a(lemma_tac⌜y ∈ Space⋎T O⋎R⌝ THEN1 rewrite_tac[space_t_ℝ_thm]);
a(ALL_FC_T rewrite_tac[singleton_connected_thm]);
(* *** Goal "2.3" *** *)
a(∃_tac⌜ClosedInterval y x⌝);
a(ALL_FC_T rewrite_tac[closed_interval_connected_thm]);
a(PC_T1 "sets_ext1" rewrite_tac[closed_interval_def]);
a(REPEAT strip_tac THEN rename_tac[] THEN all_asm_fc_tac[] THEN asm_rewrite_tac[ℝ_≤_def]);
pop_thm()
));


val ⦏ℝ_×_ℝ_topology_thm⦎ = save_thm("ℝ_×_ℝ_topology_thm",
	(rewrite_rule[] o list_∀_elim[⌜O⋎R⌝, ⌜O⋎R⌝]) product_topology_thm);
=TEX
Note there is essentially no arithmetic involved in the following. The only fact being
used is that the open intervals provide a basis for the topology of the real line
that is closed under finite intersections.
%%%%
%%%%

=SML

val ⦏continuous_ℝ_×_ℝ_ℝ_thm⦎ = save_thm ( "continuous_ℝ_×_ℝ_ℝ_thm", (
set_goal([], ⌜∀X f⦁
	X ∈ (O⋎R ×⋎T O⋎R)
⇒	(f ∈ (X ◁⋎T (O⋎R ×⋎T O⋎R), O⋎R) Continuous
	⇔	∀x y u v⦁ f(u, v) ∈ OpenInterval x y ∧ (u, v) ∈ X ⇒
		∃a b c d⦁u ∈ OpenInterval a b ∧ v ∈ OpenInterval c d ∧
			∀s t⦁	s ∈ OpenInterval a b ∧ t ∈ OpenInterval c d ∧ (s, t) ∈ X
			⇒	f(s, t) ∈ OpenInterval x y)⌝);
a(rewrite_tac[continuous_def]);
a(strip_asm_tac open_ℝ_topology_thm);
a(all_fc_tac[product_topology_thm]);
a(ALL_FC_T rewrite_tac [subspace_topology_space_t_thm, product_topology_space_t_thm]);
a(rewrite_tac[space_t_ℝ_thm]);
a(rewrite_tac [open_ℝ_def, product_topology_def, subspace_topology_def,
	merge_pcs_rule1 ["'bin_rel", "sets_ext"] prove_rule[]⌜(Universe × Universe) = Universe⌝]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 4 discard_tac);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜OpenInterval x y⌝));
(* *** Goal "1.1" *** *)
a(swap_nth_asm_concl_tac 1 THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(∃_tac⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜(u, v) ∈ B ∩ X⌝ THEN1
	(POP_ASM_T (rewrite_thm_tac o eq_sym_rule) THEN asm_rewrite_tac[]));
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [4, 5] all_fc_tac);
a(MAP_EVERY ∃_tac [⌜x''⌝, ⌜y''⌝, ⌜x'⌝, ⌜y'⌝] THEN REPEAT strip_tac);
a(LEMMA_T⌜(s, t) ∈ B ∩ X⌝ ante_tac THEN1 REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(lemma_tac⌜(s, t) ∈ (A × B')⌝ THEN1 asm_rewrite_tac[×_def]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
(* *** Goal "1.2.2" *** *)
a(DROP_NTH_ASM_T 12 (rewrite_thm_tac o eq_sym_rule) THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜{(s, t) | (s, t) ∈ X ∧  f(s, t) ∈ A }⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [4, 5, 10] all_fc_tac);
a(MAP_EVERY ∃_tac [⌜OpenInterval a b ∩ OpenInterval x''' y'''⌝,
	⌜OpenInterval c d ∩ OpenInterval x''  y''⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(strip_asm_tac (list_∀_elim[⌜a⌝, ⌜b⌝, ⌜x'''⌝, ⌜y'''⌝] ∩_open_interval_thm));
a(MAP_EVERY ∃_tac [⌜x''''⌝,	⌜y''''⌝]);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule) THEN REPEAT strip_tac);
(* *** Goal "2.1.2" *** *)
a(strip_asm_tac (list_∀_elim[⌜c⌝, ⌜d⌝, ⌜x''⌝, ⌜y''⌝] ∩_open_interval_thm));
a(MAP_EVERY ∃_tac [⌜x''''⌝,	⌜y''''⌝]);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule) THEN REPEAT strip_tac);
(* *** Goal "2.1.3" *** *)
a(rewrite_tac[×_def] THEN PC_T1 "sets_ext1" rewrite_tac[]);
a(REPEAT ∀_tac THEN ⇒_tac);
a(once_rewrite_tac[taut_rule⌜∀a b⦁a ∧ b ⇔ a ∧ (a ⇒ b)⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1.3.1" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
a(lemma_tac⌜(x1, x2) ∈ (A' × B)⌝ THEN1 asm_rewrite_tac[×_def]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀x a b⦁x ∈ a ∧ a ⊆ b ⇒ x ∈ b⌝]);
(* *** Goal "2.1.3.2" *** *)
a(all_asm_fc_tac[] THEN PC_T1 "sets_ext1" all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
The special case of the above theorem when $X$ is the whole space is very useful:.
%%%%
%%%%

=SML

val ⦏continuous_ℝ_×_ℝ_ℝ_thm1⦎ = save_thm ( "continuous_ℝ_×_ℝ_ℝ_thm1", (
set_goal([], ⌜∀f⦁
	f ∈ ((O⋎R ×⋎T O⋎R), O⋎R) Continuous
	⇔	∀x y u v⦁ f(u, v) ∈ OpenInterval x y ⇒
		∃a b c d⦁u ∈ OpenInterval a b ∧ v ∈ OpenInterval c d ∧
			∀s t⦁	s ∈ OpenInterval a b ∧ t ∈ OpenInterval c d
			⇒	f(s, t) ∈ OpenInterval x y⌝);
a(ante_tac(∀_elim⌜Space⋎T (O⋎R ×⋎T O⋎R)⌝ continuous_ℝ_×_ℝ_ℝ_thm));
a(strip_asm_tac open_ℝ_topology_thm);
a(all_fc_tac[product_topology_thm]);
a(ALL_FC_T rewrite_tac [trivial_subspace_topology_thm, space_t_open_thm]);
a(ALL_FC_T rewrite_tac [product_topology_space_t_thm]);
a(rewrite_tac[space_t_ℝ_thm,
	merge_pcs_rule1 ["'bin_rel", "sets_ext"] prove_rule[]⌜(Universe × Universe) = Universe⌝]);
pop_thm()
));

=TEX
The plan is to use the following to derive an equivalent condition to the above
phrased in terms of absolute values for use in showing that multiplication defines a
continuous mapping of the plane to the real line.
%%%%
%%%%

=SML

set_goal([], ⌜∀X⦁
	(∀x y u v⦁ f(u, v) ∈ OpenInterval x y ∧ (u, v) ∈ X ⇒
		∃a b c d⦁u ∈ OpenInterval a b ∧ v ∈ OpenInterval c d ∧
			∀s t⦁	s ∈ OpenInterval a b ∧ t ∈ OpenInterval c d ∧ (s, t) ∈ X
			⇒	f(s, t) ∈ OpenInterval x y)
⇔	(∀e u v⦁ ℕℝ 0 < e ∧ (u, v) ∈ X ⇒
		∃d1 d2 ⦁ ℕℝ 0 < d1 ∧ ℕℝ 0 < d2 ∧
			∀s t⦁	Abs(s - u) < d1 ∧ Abs(t - v) < d2 ∧ (s, t) ∈ X
			⇒	Abs(f(s, t) - f(u, v)) < e)
⌝);
a(rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(list_spec_nth_asm_tac 3 [⌜f(u, v) + ~e⌝, ⌜f(u, v) + e⌝, ⌜u⌝, ⌜v⌝]
	THEN_TRY SOLVED_T(PC_T1"ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ 0 < u + ~a ∧  ℕℝ 0 < b + ~u ∧ ℕℝ 0 < v + ~c ∧ ℕℝ 0 < d + ~v⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜u + ~a < b + ~u⌝ THEN cases_tac⌜v + ~c < d + ~v⌝);
(* *** Goal "1.1" *** *)
a(∃_tac⌜u + ~a⌝ THEN ∃_tac⌜v + ~c⌝ THEN  asm_rewrite_tac[]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm] THEN REPEAT ∀_tac THEN ⇒_tac);
a(DROP_NTH_ASM_T 12 bc_thm_tac);
a(PC_T1"ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜u + ~a⌝ THEN ∃_tac⌜d + ~v⌝ THEN  asm_rewrite_tac[]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm] THEN REPEAT ∀_tac THEN ⇒_tac);
a(DROP_NTH_ASM_T 12 bc_thm_tac);
a(PC_T1"ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.3" *** *)
a(∃_tac⌜b + ~u⌝ THEN ∃_tac⌜v + ~c⌝ THEN  asm_rewrite_tac[]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm] THEN REPEAT ∀_tac THEN ⇒_tac);
a(DROP_NTH_ASM_T 12 bc_thm_tac);
a(PC_T1"ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.4" *** *)
a(∃_tac⌜b + ~u⌝ THEN ∃_tac⌜d + ~v⌝ THEN  asm_rewrite_tac[]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm] THEN REPEAT ∀_tac THEN ⇒_tac);
a(DROP_NTH_ASM_T 12 bc_thm_tac);
a(PC_T1"ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∃e⦁ℕℝ 0 < e ∧ e ≤ f(u, v) + ~x ∧ e ≤  y + ~(f(u, v))⌝ THEN1
	(cases_tac ⌜f(u, v) + ~x ≤ y + ~(f(u, v))⌝  THEN_LIST
	[∃_tac⌜f(u, v) + ~x⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[],
	 ∃_tac⌜y + ~(f(u, v))⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]]));
a(all_asm_fc_tac[]);
a(MAP_EVERY ∃_tac [⌜u + ~d1⌝, ⌜u + d1⌝, ⌜v + ~d2⌝, ⌜v + d2⌝]);
a(strip_tac THEN_TRY SOLVED_T (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(strip_tac THEN_TRY SOLVED_T (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(REPEAT ∀_tac THEN ⇒_tac);
a(LIST_SPEC_NTH_ASM_T 6 [⌜s⌝, ⌜t⌝] ante_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏continuous_ℝ_×_ℝ_ℝ_lemma⦎ = pop_thm ();
=TEX
%%%%
%%%%

=SML
val ⦏continuous_ℝ_×_ℝ_ℝ_thm3⦎ = save_thm(
	"continuous_ℝ_×_ℝ_ℝ_thm3",
	rewrite_rule[continuous_ℝ_×_ℝ_ℝ_lemma] continuous_ℝ_×_ℝ_ℝ_thm);
val ⦏continuous_ℝ_×_ℝ_ℝ_thm4⦎ = save_thm(
	"continuous_ℝ_×_ℝ_ℝ_thm4",
	rewrite_rule[
		rewrite_rule[](∀_elim⌜Universe:(ℝ × ℝ) SET⌝
			continuous_ℝ_×_ℝ_ℝ_lemma)] continuous_ℝ_×_ℝ_ℝ_thm1);
=TEX
The above lets us make light work of showing the addition viewed as a function from the plane
to the real line is continuous:
%%%%
%%%%

=SML

val ⦏plus_continuous_ℝ_×_ℝ_thm⦎ = save_thm ( "plus_continuous_ℝ_×_ℝ_thm", (
set_goal([], ⌜ (Uncurry $+) ∈ ((O⋎R ×⋎T O⋎R), O⋎R) Continuous ⌝);
a(rewrite_tac[continuous_ℝ_×_ℝ_ℝ_thm1] THEN REPEAT strip_tac);
a(MAP_EVERY ∃_tac[ ⌜u - (1/2)*(u + v - x)⌝, ⌜u + (1/2)*(y - (u + v))⌝,
	⌜v - (1/2)*(u + v - x)⌝, ⌜v + (1/2)*(y - (u + v))⌝]);
a(POP_ASM_T ante_tac THEN rewrite_tac[open_interval_def] THEN REPEAT strip_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏times_continuous_ℝ_×_ℝ_thm⦎ = save_thm ( "times_continuous_ℝ_×_ℝ_thm", (
set_goal([], ⌜ (Uncurry $*) ∈ ((O⋎R ×⋎T O⋎R), O⋎R) Continuous ⌝);
a(rewrite_tac[continuous_ℝ_×_ℝ_ℝ_thm4] THEN REPEAT strip_tac);
a(lemma_tac⌜∃t⦁Abs u + ℕℝ 1 < t ∧ Abs v < t⌝);
(* *** Goal "1" *** *)
a(cases_tac ⌜Abs u + ℕℝ 1 <  Abs v⌝ THEN_LIST [
	∃_tac ⌜ Abs v + ℕℝ 1⌝, ∃_tac⌜Abs u + ℕℝ 2⌝]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜ℕℝ 0  < ℕℝ 2 * t⌝ THEN1
	(strip_asm_tac(∀_elim⌜v⌝ℝ_0_≤_abs_thm) THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ 0 < e * (ℕℝ 2 * t) ⋏-⋏1⌝ THEN1
	(all_fc_tac[ℝ_0_less_0_less_recip_thm] THEN all_fc_tac[ℝ_0_less_0_less_times_thm]));
a(lemma_tac⌜∃d⦁ℕℝ 0 <  d ∧ d < ℕℝ 1 ∧ d <  e * (ℕℝ 2 * t) ⋏-⋏1⌝);
(* *** Goal "2.1" *** *)
a(cases_tac ⌜ℕℝ 1 < e * (ℕℝ 2 * t) ⋏-⋏1⌝THEN_LIST [
	∃_tac ⌜1/2⌝, ∃_tac⌜(1/2)* e * (ℕℝ 2 * t) ⋏-⋏1⌝]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜d⌝ THEN ∃_tac⌜d⌝ THEN REPEAT strip_tac);
a(bc_thm_tac (rewrite_rule[]times_lim_seq_lemma));
a(∃_tac⌜t⌝ THEN REPEAT strip_tac THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 ante_tac THEN ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm]);
a(DROP_NTH_ASM_T 8 ante_tac);
a(cases_tac⌜ℕℝ 0 ≤ s⌝ THEN cases_tac ⌜ℕℝ 0 ≤ u⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏cond_continuous_ℝ_thm⦎ = save_thm ( "cond_continuous_ℝ_thm", (
set_goal([], ⌜∀b c f g σ τ⦁
	σ ∈  Topology
∧	τ ∈  Topology
∧	c ∈ (σ, O⋎R) Continuous
∧	f ∈ (σ, τ) Continuous
∧	g ∈ (σ, τ) Continuous
∧	(∀x⦁x ∈ Space⋎T σ ∧ c x = b ⇒ f x = g x)
⇒	(λx⦁if c x ≤ b then f x else g x) ∈ (σ, τ) Continuous
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜∀x⦁c x ≤ b ⇔ x ∈ {t|c t ≤ b}⌝ pure_once_rewrite_thm_tac THEN1
	rewrite_tac[]);
a(bc_thm_tac cond_continuous_thm THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_¬_≤_less_thm] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(strip_asm_tac (list_∀_elim[⌜c x⌝, ⌜b⌝] ℝ_less_cases_thm) THEN
	REPEAT strip_tac THEN  i_contr_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜{t | t < b} ∈ O⋎R⌝ THEN1
	rewrite_tac[half_infinite_intervals_open_thm]);
a(DROP_NTH_ASM_T 7 (fn th => all_fc_tac[rewrite_rule[continuous_def] th]));
a(spec_nth_asm_tac 5 ⌜{x|x ∈ Space⋎T σ ∧ c x ∈ {t|t < b}}⌝);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜{t | b < t} ∈ O⋎R⌝ THEN1
	rewrite_tac[half_infinite_intervals_open_thm]);
a(DROP_NTH_ASM_T 7 (fn th => all_fc_tac[rewrite_rule[continuous_def] th]));
a(spec_nth_asm_tac 5 ⌜{x|x ∈ Space⋎T σ ∧ c x ∈ {t|b < t}}⌝);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏d_ℝ_metric_thm⦎ = save_thm ( "d_ℝ_metric_thm", (
set_goal([], ⌜
	D⋎R ∈ Metric
⌝);
a(rewrite_tac[metric_def, d_ℝ_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[ℝ_0_≤_abs_thm]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_abs_eq_0_thm] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[ℝ_abs_0_thm]);
(* *** Goal "4" *** *)
a(pure_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜y + ~x = ~(x + ~y)⌝, ℝ_abs_minus_thm]);
a(rewrite_tac[]);
(* *** Goal "5" *** *)
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜z + ~x = (y + ~x) + (z + ~y)⌝, ℝ_abs_plus_thm]);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏d_ℝ_open_ℝ_thm⦎ = save_thm ( "d_ℝ_open_ℝ_thm", (
set_goal([], ⌜
	D⋎R MetricTopology = O⋎R
⌝);
a(PC_T1 "sets_ext1" rewrite_tac[metric_topology_def, open_ℝ_delta_thm, d_ℝ_def] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏d_ℝ_2_metric_thm⦎ = save_thm ( "d_ℝ_2_metric_thm", (
set_goal([], ⌜
	D⋎R2 ∈ Metric
⌝);
a(LEMMA_T ⌜D⋎R2 = (λ ((x1, x2), y1, y2)⦁ D⋎R (x1, y1) + D⋎R (x2, y2))⌝ rewrite_thm_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[d_ℝ_def] THEN REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule[]⌜x = (Fst x, Snd x)⌝]);
a(pure_rewrite_tac[d_ℝ_2_def1]);
a(rewrite_tac[]);
(* *** Goal "2" *** *)
a(bc_thm_tac product_metric_thm THEN rewrite_tac[d_ℝ_metric_thm]);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏d_ℝ_2_open_ℝ_×_open_ℝ_thm⦎ = save_thm ( "d_ℝ_2_open_ℝ_×_open_ℝ_thm", (
set_goal([], ⌜
	D⋎R2 MetricTopology = (O⋎R ×⋎T O⋎R)
⌝);
a(LEMMA_T ⌜D⋎R2 = (λ ((x1, x2), y1, y2)⦁ D⋎R (x1, y1) + D⋎R (x2, y2))⌝ rewrite_thm_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[d_ℝ_def] THEN REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule[]⌜x = (Fst x, Snd x)⌝]);
a(pure_rewrite_tac[d_ℝ_2_def1]);
a(rewrite_tac[]);
(* *** Goal "2" *** *)
a(strip_asm_tac d_ℝ_metric_thm);
a(ALL_FC_T rewrite_tac[product_metric_topology_thm]);
a(rewrite_tac[d_ℝ_open_ℝ_thm]);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏open_ℝ_hausdorff_thm⦎ = save_thm ( "open_ℝ_hausdorff_thm", (
set_goal([], ⌜
	O⋎R ∈ Hausdorff
⌝);
a(rewrite_tac[eq_sym_rule d_ℝ_open_ℝ_thm]
	THEN bc_thm_tac metric_topology_hausdorff_thm
	THEN rewrite_tac[d_ℝ_metric_thm]);
pop_thm()
));


=TEX

%%%%
%%%%

=SML

val ⦏open_ℝ_×_open_ℝ_hausdorff_thm⦎ = save_thm ( "open_ℝ_×_open_ℝ_hausdorff_thm", (
set_goal([], ⌜
	(O⋎R ×⋎T O⋎R) ∈ Hausdorff
⌝);
a(rewrite_tac[eq_sym_rule d_ℝ_2_open_ℝ_×_open_ℝ_thm]
	THEN bc_thm_tac metric_topology_hausdorff_thm
	THEN rewrite_tac[d_ℝ_2_metric_thm]);
pop_thm()
));


=TEX
We specialise the theorem on Lebesgue numbers to the real line.
%%%%
%%%%

=SML
val ⦏ℝ_lebesgue_number_thm⦎ = save_thm (
	"ℝ_lebesgue_number_thm",
	pc_rule1 "predicates"
	rewrite_rule[d_ℝ_def, d_ℝ_metric_thm, d_ℝ_open_ℝ_thm, compact_compact_ℝ_thm]
	(∀_elim⌜D⋎R⌝lebesgue_number_thm));

val ⦏closed_interval_lebesgue_number_thm⦎ = save_thm (
	"closed_interval_lebesgue_number_thm",
	all_∀_intro(
	pc_rule1 "predicates"
	rewrite_rule[closed_interval_compact_thm]
	(∀_elim⌜ClosedInterval y z⌝ ℝ_lebesgue_number_thm)));
=TEX

The following lemma allows us to dissect the unit interval into a list of subintervals of bounded width for any given bound on the width.
%%%%
%%%%
=SML

val ⦏dissect_unit_interval_thm⦎ = save_thm ( "dissect_unit_interval_thm", (
set_goal([], ⌜∀x⦁
	0. < x
⇒	∃n t⦁ 0 < n ∧ t 0 = 0. ∧ t n = 1.
∧	(∀i j⦁ i < j ⇒ t i < t j)
∧	(∀i⦁t (i + 1) - t i < x)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃n t⦁ t 0 = 0. ∧ t n = 1.
∧	(∀i⦁t i < t (i + 1) ∧ t (i + 1) < t i + x)⌝);
(* *** Goal "1" *** *)
a(lemma_tac⌜∃n y⦁ 0. < y ∧ y < x ∧ ℕℝ n * y = 1.⌝);
(* *** Goal "1.1" *** *)
a(strip_asm_tac (∀_elim⌜x⌝ ℝ_archimedean_recip_thm));
a(lemma_tac⌜0. < ℕℝ(m + 1)⌝ THEN1 rewrite_tac[ℕℝ_less_thm]);
a(lemma_tac⌜¬ℕℝ(m + 1) = 0.⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(∃_tac⌜m+1⌝ THEN ∃_tac⌜ℕℝ(m+1) ⋏-⋏1⌝ THEN
	ALL_FC_T asm_rewrite_tac[ℝ_0_less_0_less_recip_thm,
		ℝ_recip_clauses]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜n⌝ THEN ∃_tac⌜λi⦁ ℕℝ i * y⌝ THEN asm_rewrite_tac[
		ℕℝ_plus_homomorphism_thm,
		ℝ_times_plus_distrib_thm]);
(* *** Goal "2" *** *)
a(∃_tac⌜n⌝ THEN ∃_tac⌜t⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(swap_nth_asm_concl_tac 2 THEN LEMMA_T⌜n = 0⌝ asm_rewrite_thm_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(LEMMA_T ⌜i + 1 ≤ j⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(POP_ASM_T discard_tac THEN induction_tac⌜i'⌝ THEN asm_rewrite_tac[plus_assoc_thm1]);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜t ((i + 1) + i')⌝ THEN
	asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a(lemma_tac⌜t (i + 1) < t i + x⌝ THEN1 asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
We now give a result that is used in proving that covering projections
are fibrations. Let $T$ be any space and $x \in T$. Assume $U$ is a
set of open sets in $T \times [0, 1]$ that cover $\{x\} \times [0, 1]$.
Then there is an open subset $A$ of $T$ and a finite sequence of
numbers $t_0 = 0 < t_1 < t_2 < \ldots < t_n = 1$ such that for each $i$
there is a $B_i \in U$ such that $A \times [t_i, t_{i+1}] \subseteq B_i$.
%%%%
%%%%

=SML

val ⦏product_interval_cover_thm1⦎ = save_thm ( "product_interval_cover_thm1", (
set_goal([], ⌜∀τ U x⦁
	τ ∈ Topology
∧	U ⊆ (τ ×⋎T O⋎R)
∧	x ∈ Space⋎T τ
∧	(∀s⦁ s ∈ ClosedInterval 0. 1. ⇒ ∃B⦁ (x, s) ∈ B ∧ B ∈ U) 
⇒	∃n t A⦁ t 0 = 0. ∧ t n = 1. ∧ (∀i⦁t i < t (i + 1))
	∧	x ∈ A
	∧	A ∈ τ
	∧	∀i⦁ i < n ⇒ ∃B⦁ B ∈ U ∧ (A × ClosedInterval (t i) (t (i+1))) ⊆ B
⌝);
a(strip_asm_tac open_ℝ_topology_thm);
a(REPEAT strip_tac);
a(lemma_tac⌜(τ ×⋎T O⋎R) ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(lemma_tac⌜
	{I | I ∈ O⋎R ∧
	∃X B⦁ x ∈ X ∧ X ∈ τ ∧ B ∈ U ∧ (X × I) ⊆ B} ⊆ O⋎R⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(lemma_tac⌜
	ClosedInterval 0. 1. ⊆
	⋃ {I | I ∈ O⋎R ∧ ∃X B⦁ x ∈ X ∧ X ∈ τ ∧ B ∈ U ∧ (X × I) ⊆ B}
⌝);
(* *** Goal "1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀b u t⦁ b ∈ u ∧ u ⊆ t ⇒ b ∈ t⌝]
	THEN swap_nth_asm_concl_tac 1);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]);
a(rewrite_tac[product_topology_def] THEN swap_nth_asm_concl_tac 1
	THEN strip_tac THEN rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜B''⌝ THEN REPEAT strip_tac);
a(∃_tac⌜A⌝ THEN ∃_tac⌜B⌝ THEN REPEAT strip_tac);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b c⦁ a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝]);
(* *** Goal "2" *** *)
a(all_fc_tac[closed_interval_lebesgue_number_thm]);
a(all_fc_tac[dissect_unit_interval_thm]);
a(∃_tac⌜n⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
a(lemma_tac⌜∃Q⦁∀i⦁ i < n ⇒
	x ∈ Q i ∧ Q i ∈ τ ∧
	∃B⦁B ∈ U ∧ (Q i × ClosedInterval (t i) (t(i + 1))) ⊆ B⌝
	THEN prove_∃_tac THEN strip_tac);
(* *** Goal "2.1" *** *)
a(cases_tac⌜i' < n⌝ THEN asm_rewrite_tac[]);
a(lemma_tac⌜t i' ∈ ClosedInterval 0. 1.⌝);
(* *** Goal "2.1.1" *** *)
a(rewrite_tac[closed_interval_def]);
a(cases_tac⌜i' = 0⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜0 < i'⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(rewrite_tac[ℝ_≤_def] THEN LIST_DROP_NTH_ASM_T [5] (ALL_FC_T (MAP_EVERY ante_tac)));
a(asm_rewrite_tac[] THEN taut_tac);
(* *** Goal "2.1.2" *** *)
a(LIST_DROP_NTH_ASM_T [8] all_fc_tac);
a(∃_tac⌜X⌝ THEN REPEAT strip_tac THEN ∃_tac⌜B⌝ THEN REPEAT strip_tac);
a(bc_thm_tac(pc_rule1 "sets_ext1" prove_rule[]
		⌜∀a b c⦁ a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝)
	THEN ∃_tac⌜X × A⌝ THEN REPEAT strip_tac);
a(bc_thm_tac(pc_rule1 "sets_ext1" prove_rule[×_def]
		⌜∀x i a⦁ i ⊆ a ⇒ (x × i) ⊆ (x × a)⌝));
a(rewrite_tac[closed_interval_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(lemma_tac⌜Abs(x' - t i') < e⌝);
(* *** Goal "2.1.2.1" *** *)
a(rewrite_tac[ℝ_abs_def]);
a(LEMMA_T ⌜0. ≤ x' + ~ (t i')⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜t(i' + 1) - t i' < e⌝ THEN1 asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
(* *** Goal "2.2" *** *)
a(strip_asm_tac(rewrite_rule[range_finite_size_thm]
	(list_∀_elim[⌜Q⌝, ⌜{i | i < n}⌝]finite_image_thm)));
a(∃_tac⌜⋂{y|∃ x⦁ x < n ∧ y = Q x}⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(all_var_elim_asm_tac1 THEN LIST_DROP_NTH_ASM_T [3] all_fc_tac);
(* *** Goal "2.2.2" *** *)
a(bc_thm_tac (⋂_open_thm) THEN asm_rewrite_tac[]);
a(strip_tac THEN1 PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a(∃_tac⌜Q 0⌝ THEN asm_rewrite_tac[]);
a(∃_tac⌜0⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN LIST_DROP_NTH_ASM_T [3] all_fc_tac);
(* *** Goal "2.2.3" *** *)
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜i⌝));
a(∃_tac⌜B⌝ THEN REPEAT strip_tac);
a(bc_thm_tac(pc_rule1 "sets_ext1" prove_rule[]
		⌜∀a b c⦁ a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝)
	THEN ∃_tac⌜Q i × ClosedInterval (t i) (t (i + 1))⌝ THEN REPEAT strip_tac);
a(bc_thm_tac(pc_rule1 "sets_ext1" prove_rule[×_def]
		⌜∀x y i⦁ x ⊆ y ⇒ (x × i) ⊆ (y × i)⌝));
a(DROP_NTH_ASM_T 5 ante_tac THEN DROP_ASMS_T discard_tac);
a(strip_tac THEN PC_T "sets_ext1" strip_tac);
a(rewrite_tac[⋂_def] THEN REPEAT strip_tac);
a(asm_prove_tac[]);
(* *** Goal "2.3" *** *)
a(strip_tac THEN DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏inc_seq_thm⦎ = save_thm ( "inc_seq_thm", (
set_goal([], ⌜∀t: ℕ → ℝ; i j⦁
	(∀i⦁ t i < t (i + 1))
⇔	(∀i j⦁ i < j ⇒ t i < t j)⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac THEN induction_tac⌜j⌝ THEN strip_tac);
(* *** Goal "1.1" *** *)
a(lemma_tac⌜i = j⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜t j⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T bc_thm_tac THEN rewrite_tac[]);
(* *** Goal "2" *** *)
pop_thm()
));

val ⦏product_interval_cover_thm⦎ = save_thm ("product_interval_cover_thm",
	rewrite_rule[inc_seq_thm] product_interval_cover_thm1);
=TEX

We instantiate the morphism-proving tools to prove continuity of functions
in this theory.
First we give the theorems asserting that various basic functions are indeed continuous with respect to specific topologies in the required form.

=SML
rewrite_rule[cts_at_ℝ_continuous_thm] minus_cts_thm;

=TEX
=SML

local
	
val ⦏ℝ_continuity_fact_thms⦎ : THM list =
	map (rewrite_rule[cts_at_ℝ_continuous_thm]) (
		ℝ_ℕ_exp_cts_thm::
		minus_cts_thm::
		exp_cts_thm::
		(map all_∀_intro o strip_∧_rule o all_∀_elim)
			sin_cos_cts_thm) @ [
	plus_continuous_ℝ_×_ℝ_thm,
	times_continuous_ℝ_×_ℝ_thm,
	open_ℝ_topology_thm,
	space_t_ℝ_thm];


in
(*
=TEX
=SML
*)
fun ⦏ℝ_continuity_tac⦎ (thms : THM list): TACTIC = (
	basic_continuity_tac (thms @ ℝ_continuity_fact_thms)
);
end (* local ... in ... end *);

=TEX
It is now useful to set up a proof context to eliminate various trivial facts.
%%%%
%%%%

=SML
val _ = delete_pc "'topology_ℝ" handle Fail _ => ();
val _ = new_pc "'topology_ℝ";

val _ = add_rw_thms [
	open_ℝ_topology_thm,
	space_t_ℝ_thm,
	open_ℝ_id_continuous_thm,
	(rewrite_rule[open_ℝ_topology_thm] o ∀_elim⌜O⋎R⌝) open_ℝ_const_continuous_thm
	]
	"'topology_ℝ";
local
	fun ⦏thms_to_eqn_cxt⦎ (thms:THM list) : EQN_CXT = (
		flat(map (cthm_eqn_cxt initial_rw_canon) thms)
	);
	val pos_bits = thms_to_eqn_cxt [open_ℝ_topology_thm];
	val neg_strips = map (mk_¬ ** RAND_C) pos_bits;
	val new_strips = pos_bits @ neg_strips;
in
	val _ = set_st_eqn_cxt new_strips "'topology_ℝ";
	val _ = set_sc_eqn_cxt new_strips "'topology_ℝ";

end;

val _ = set_pr_tac basic_prove_tac "'topology_ℝ";
val _ = set_pr_conv basic_prove_conv "'topology_ℝ";

(*
val _ = commit_pc "'topology_ℝ";
*)


=TEX

%%%%
%%%%
\section{PATHS AND HOMOTOPY--- THEOREMS}
=SML
open_theory "homotopy";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'topology_ℝ", "'ℝ"];
=TEX
\subsection{The Definitions}
=SML
val ⦏paths_def⦎ = get_spec⌜$Paths⌝;
val ⦏loops_def⦎ = get_spec⌜$Loops⌝;
val ⦏path_connected_def⦎ = get_spec⌜$PathConnected⌝;
val ⦏locally_path_connected_def⦎ = get_spec⌜LocallyPathConnected⌝;
val ⦏homotopy_def⦎ = get_spec⌜$Homotopy⌝;
val ⦏homotopic_def⦎ = get_spec⌜$Homotopic⌝;
val ⦏path_plus_def⦎ = get_spec⌜$+⋎P⌝;
val ⦏path_0_def⦎ = get_spec⌜0⋎P⌝;
val ⦏path_minus_def⦎ = get_spec⌜~⋎P⌝;
val ⦏iota_i_def⦎ = get_spec⌜IotaI⌝;
val ⦏path_lifting_property_def⦎ = get_spec⌜PathLiftingProperty⌝;
val ⦏homotopy_lifting_property_def⦎ = get_spec⌜HomotopyLiftingProperty⌝;
val ⦏path_homotopic_def⦎ = get_spec⌜PathHomotopic⌝;
=TEX
\subsection{Path-connectedness}
Path-connectedness implies connectedness, because a path, as the continuous image of
a connected set is itself connected.
%%%%
%%%%
=SML

val ⦏path_connected_connected_thm⦎ = save_thm ( "path_connected_connected_thm", (
set_goal([], ⌜∀τ X⦁
	τ ∈ Topology
∧	X ∈ τ PathConnected
⇒	X ∈ τ Connected
⌝);
a(rewrite_tac[path_connected_def, paths_def] THEN REPEAT strip_tac);
a(bc_thm_tac connected_pointwise_bc_thm THEN REPEAT strip_tac);
a(list_spec_nth_asm_tac 3 [⌜x⌝, ⌜y⌝]);
a(ante_tac(list_∀_elim[⌜f⌝, ⌜Universe:ℝ SET⌝, ⌜O⋎R⌝, ⌜τ⌝] image_connected_thm));
a(pure_asm_rewrite_tac[open_ℝ_topology_thm, universe_ℝ_connected_thm]);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜{y|∃ x⦁ y = f x}⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1 THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜ℕℝ 0⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜ℕℝ 1⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏product_path_connected_thm⦎ = save_thm ( "product_path_connected_thm", (
set_goal([], ⌜∀σ τ X Y⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	X ∈ σ PathConnected
∧	Y ∈ τ PathConnected
⇒	(X × Y) ∈ (σ ×⋎T τ) PathConnected
⌝);
a(rewrite_tac[path_connected_def, paths_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[product_topology_space_t_thm]);
a(LIST_GET_NTH_ASM_T [2, 4] (MAP_EVERY ante_tac));
a(MERGE_PCS_T1 ["'bin_rel", "sets_ext1"] prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN POP_ASM_T ante_tac);
a(rewrite_tac[×_def] THEN REPEAT strip_tac);
a(list_spec_nth_asm_tac 7 [⌜Fst x⌝, ⌜Fst y⌝]);
a(list_spec_nth_asm_tac 11 [⌜Snd x⌝, ⌜Snd y⌝]);
(* *** Goal "2.1" *** *)
a(∃_tac⌜λt⦁(f t, f' t)⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac
	THEN_TRY SOLVED_T (ALL_ASM_FC_T asm_rewrite_tac[]));
a(bc_thm_tac product_continuous_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
\subsection{Homotopy Classes}
%%%%
%%%%
=SML

val ⦏homotopic_refl_thm⦎ = save_thm ( "homotopic_refl_thm", (
set_goal([], ⌜∀σ X τ f⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	Refl ((σ, τ) Continuous, (σ, X, τ) Homotopic) 
⌝);
a(rewrite_tac[refl_def, homotopy_def, homotopic_def ] THEN REPEAT strip_tac);
a(∃_tac⌜λ y⦁ x (Fst y)⌝ THEN asm_rewrite_tac[]);
a(ℝ_continuity_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
val ⦏λ_un_β_rand_conv⦎ : CONV = (fn tm =>
	let	val (v, _) = dest_λ tm;
	in	SIMPLE_λ_C (RAND_C (un_β_conv v)) tm
	end
);

val ⦏homotopic_sym_thm⦎ = save_thm ( "homotopic_sym_thm", (
set_goal([], ⌜∀σ : 'a SET SET; X τ f g⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	Sym ((σ, τ) Continuous, (σ, X, τ) Homotopic) 
⌝);
a(rewrite_tac[sym_def, homotopy_def, homotopic_def ] THEN REPEAT strip_tac);
a(∃_tac⌜λ xt⦁ H(Fst xt, ℕℝ 1 -  Snd xt)⌝ THEN asm_rewrite_tac[]);
a(ℝ_continuity_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏homotopic_trans_thm⦎ = save_thm ( "homotopic_trans_thm", (
set_goal([], ⌜∀σ : 'a SET SET; X τ f g h⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	Trans ((σ, τ) Continuous, (σ, X, τ) Homotopic) 
⌝);
a(rewrite_tac[trans_def, homotopy_def, homotopic_def ] THEN REPEAT strip_tac);
a(∃_tac⌜
	λ xt⦁
	if	Snd xt ≤ 1/2
	then	H(Fst xt, ℕℝ 2 * Snd xt)
	else	H'(Fst xt, ℕℝ 2 * (Snd xt + ~ (1/2)))⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_tac open_ℝ_topology_thm THEN ALL_FC_T asm_rewrite_tac[product_topology_thm]);
a(REPEAT strip_tac THEN_TRY ℝ_continuity_tac[]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜∀t⦁ H(x', t) = y x' ∧ H'(x', t) = y x'⌝ rewrite_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LIST_DROP_NTH_ASM_T [6] (rewrite_tac o map (conv_rule(ONCE_MAP_C eq_sym_conv))));
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(LIST_DROP_NTH_ASM_T [3] (rewrite_tac o map (conv_rule(ONCE_MAP_C eq_sym_conv))));
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2.3" *** *)
a(REPEAT (if_cases_tac THEN  asm_rewrite_tac[]));
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏homotopic_equiv_thm⦎ = save_thm ( "homotopic_equiv_thm", (
set_goal([], ⌜∀σ : 'a SET SET; X τ f g h⦁
	σ ∈ Topology
∧	τ ∈ Topology
⇒	Equiv ((σ, τ) Continuous, (σ, X, τ) Homotopic) 
⌝);
a(REPEAT strip_tac THEN rewrite_tac[equiv_def]);
a(ALL_FC_T rewrite_tac[homotopic_refl_thm, homotopic_sym_thm, homotopic_trans_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏homotopy_⊆_thm⦎ = save_thm ( "homotopy_⊆_thm", (
set_goal([], ⌜∀σ X Y τ H⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	H ∈ (σ, X, τ) Homotopy
∧	Y ⊆ X
⇒	H ∈ (σ, Y, τ) Homotopy
⌝);
a(rewrite_tac[ homotopy_def ] THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
a(ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏homotopic_⊆_thm⦎ = save_thm ( "homotopic_⊆_thm", (
set_goal([], ⌜∀σ X Y τ f g⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	((σ, X, τ) Homotopic) f g
∧	Y ⊆ X
⇒	((σ, Y, τ) Homotopic) f g
⌝);
a(rewrite_tac[ homotopic_def ] THEN REPEAT strip_tac);
a(∃_tac⌜H⌝ THEN ALL_FC_T asm_rewrite_tac[homotopy_⊆_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏homotopic_comp_left_thm⦎ = save_thm ( "homotopic_comp_left_thm", (
set_goal([], ⌜∀ρ σ τ X f g h⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	((ρ, X, σ) Homotopic) f g
∧	h ∈ (σ,τ) Continuous
⇒	((ρ, X, τ) Homotopic) (λx⦁h(f x)) (λx⦁h(g x))
⌝);
a(rewrite_tac[ homotopy_def, homotopic_def ] THEN REPEAT strip_tac);
a(∃_tac⌜λxt⦁ h(H xt)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac comp_continuous_thm);
a(∃_tac⌜σ⌝ THEN REPEAT strip_tac);
a(bc_thm_tac product_topology_thm THEN asm_rewrite_tac[open_ℝ_topology_thm]);
(* *** Goal "2" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏homotopic_comp_right_thm⦎ = save_thm ( "homotopic_comp_right_thm", (
set_goal([], ⌜∀ρ σ τ X f g h⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	((σ, X, τ) Homotopic) f g
∧	h ∈ (ρ,σ) Continuous
⇒	((ρ, {x | h x ∈ X}, τ) Homotopic) (λx⦁f(h x)) (λx⦁g(h x))
⌝);
a(rewrite_tac[ homotopy_def, homotopic_def ] THEN REPEAT strip_tac);
a(∃_tac⌜λxt⦁ H ((λxt⦁ (h(Fst xt), Snd xt)) xt)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac comp_continuous_thm);
a(asm_tac open_ℝ_topology_thm);
a(∃_tac⌜(σ ×⋎T O⋎R)⌝ THEN ALL_FC_T asm_rewrite_tac[product_topology_thm]);
a(pure_once_rewrite_tac[prove_rule[]⌜∀x⦁h(Fst x) = (λx⦁h(Fst x))x⌝]);
a(bc_thm_tac product_continuous_thm);
a(ALL_FC_T asm_rewrite_tac[product_topology_thm] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(bc_thm_tac comp_continuous_thm);
a(∃_tac⌜ρ⌝ THEN ALL_FC_T asm_rewrite_tac[product_topology_thm]);
a(rewrite_tac[prove_rule[]⌜Fst = (λ(x, y)⦁ x)⌝]);
a(bc_thm_tac left_proj_continuous_thm THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(rewrite_tac[prove_rule[]⌜Snd = (λ(x, y)⦁ y)⌝]);
a(bc_thm_tac right_proj_continuous_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏homotopic_ℝ_thm⦎ = save_thm ( "homotopic_ℝ_thm", (
set_goal([], ⌜∀τ f g ⦁
	τ ∈ Topology
∧	f ∈ (τ,O⋎R) Continuous
∧	g ∈ (τ,O⋎R) Continuous
⇒	((τ, {x | g x = f x}, O⋎R) Homotopic) f g
⌝);
a(rewrite_tac[ homotopy_def, homotopic_def ] THEN REPEAT strip_tac);
a(∃_tac⌜λxt⦁ (ℕℝ 1 + ~(Snd xt))*f (Fst xt) + (Snd xt)*g(Fst xt) ⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ℝ_continuity_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));



=TEX
%%%%
%%%%

We honour the implied promise to prove that a continuous function on $X \times [a, b]$ can always be extended to a continuous function on $X \times ℝ$. We first show that $[-\infty, b]$ is a retract of ℝ:
=SML

val ⦏half_open_interval_retract_thm⦎ = save_thm ( "half_open_interval_retract_thm", (
set_goal([], ⌜∀b⦁
	(λs⦁ if s ≤ b then s else b) ∈
	(O⋎R, {s | s ≤ b} ◁⋎T O⋎R) Continuous
⌝);
a(REPEAT strip_tac THEN asm_tac open_ℝ_topology_thm);
a(lemma_tac⌜{s | s ≤ b} ⊆ Space⋎T O⋎R⌝
	THEN1 rewrite_tac[space_t_ℝ_thm]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac
	[subspace_range_continuous_⇔_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜x ≤ b⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

Next we show that $[a, b]$ is a retract of ℝ:
=SML
=SML

val ⦏closed_interval_retract_thm⦎ = save_thm ( "closed_interval_retract_thm", (
set_goal([], ⌜∀a b⦁
	a ≤ b
⇒	(λs⦁ if s ≤ a then a else if s ≤ b then s else b) ∈
	(O⋎R, ClosedInterval a b ◁⋎T O⋎R) Continuous
⌝);
a(REPEAT strip_tac THEN asm_tac open_ℝ_topology_thm);
a(lemma_tac⌜ClosedInterval a b ⊆ Space⋎T O⋎R⌝
	THEN1 rewrite_tac[]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac
	[subspace_range_continuous_⇔_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_rewrite_tac[]);
a(REPEAT strip_tac THEN_TRY ℝ_continuity_tac[] THEN_TRY asm_rewrite_tac[]);
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[closed_interval_def]);
a(cases_tac⌜x ≤ a⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜x ≤ b⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
Now we have that $X \times [a, b]$ is a retract of $X \times ℝ$:
=SML

val ⦏×_closed_interval_retract_thm⦎ = save_thm ( "×_closed_interval_retract_thm", (
set_goal([], ⌜∀τ X a b⦁
	τ ∈ Topology
∧	X ⊆ Space⋎T τ
∧	a ≤ b
⇒	(λ(x, s)⦁ (x, if s ≤ a then a else if s ≤ b then s else b)) ∈
	((X × Universe) ◁⋎T (τ ×⋎T O⋎R),
		(X × ClosedInterval a b) ◁⋎T (τ ×⋎T O⋎R)) Continuous
⌝);
a(REPEAT strip_tac THEN asm_tac open_ℝ_topology_thm);
a(lemma_tac⌜τ ×⋎T O⋎R ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(lemma_tac⌜(X × ClosedInterval a b) ⊆ Space⋎T (τ ×⋎T O⋎R)⌝);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[product_topology_space_t_thm]);
a(DROP_NTH_ASM_T 4 ante_tac);
a(MERGE_PCS_T1 ["'pair", "sets_ext1"] prove_tac[×_def]);
(* *** Goal "2" *** *)
a(lemma_tac⌜(X × Universe) ◁⋎T τ ×⋎T O⋎R ∈ Topology⌝
	THEN1 (bc_tac[subspace_topology_thm, product_topology_thm] THEN REPEAT strip_tac));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac
	[subspace_range_continuous_⇔_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LEMMA_T ⌜(λ (x:'a, s)⦁ (x, (if s ≤ a then a else if s ≤ b then s else b))) =
	(λ xs⦁ (Fst xs, (λxs⦁if Snd xs ≤ a then a else if Snd xs ≤ b then Snd xs else b) xs))⌝
	pure_rewrite_thm_tac
	THEN1 prove_tac[]);
a(bc_thm_tac product_continuous_thm THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(bc_tac[subspace_domain_continuous_thm, fst_continuous_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.1.2" *** *)
a(bc_thm_tac subspace_domain_continuous_thm THEN REPEAT strip_tac);
a(LEMMA_T ⌜(λ xs⦁ if Snd xs ≤ a then a else if Snd xs ≤ b then Snd xs else b) =
	(λxs⦁ (λ s⦁ if s ≤ a then a else if s ≤ b then s else b)(Snd xs))⌝
	pure_rewrite_thm_tac
	THEN1 prove_tac[]);
a(bc_thm_tac comp_continuous_thm);
a(∃_tac⌜O⋎R⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1.2.1" *** *)
a(bc_thm_tac snd_continuous_thm THEN REPEAT strip_tac);
(* *** Goal "2.1.2.2" *** *)
a(all_fc_tac[closed_interval_retract_thm]);
a(all_fc_tac[subspace_range_continuous_thm]);
(* *** Goal "2.2" *** *)
a(POP_ASM_T ante_tac);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm,
	product_topology_space_t_thm]);
a(rewrite_tac[×_def] THEN REPEAT strip_tac);
a(rewrite_tac[closed_interval_def]);
a(if_cases_tac THEN asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
From the above, we get the following saying that any function continuous on $X \times [a, b]$ can be continuously extended to a function on $X \times ℝ$:
=SML

val ⦏closed_interval_extension_thm⦎ = save_thm ( "closed_interval_extension_thm", (
set_goal([], ⌜∀ρ; σ; f : 'a × ℝ → 'b; X a b⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	X ⊆ Space⋎T ρ
∧	a ≤ b
∧	f ∈ ((X × ClosedInterval a b) ◁⋎T ρ ×⋎T O⋎R, σ) Continuous
⇒	∃g : 'a × ℝ → 'b⦁
	g ∈ ((X × Universe) ◁⋎T (ρ ×⋎T O⋎R), σ) Continuous
∧	∀x s⦁	x ∈ X ∧ s ∈ ClosedInterval a b
	⇒	g(x, s) = f(x, s)
⌝);
a(REPEAT strip_tac THEN all_fc_tac[×_closed_interval_retract_thm]);
a(asm_tac open_ℝ_topology_thm);
a(∃_tac⌜λxs⦁f((λ (x, s)⦁ (x, (if s ≤ a then a else if s ≤ b then s else b))) xs)⌝
	THEN strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac comp_continuous_thm THEN REPEAT strip_tac);
a(∃_tac⌜(X × ClosedInterval a b) ◁⋎T ρ ×⋎T O⋎R⌝);
a(asm_rewrite_tac[] THEN REPEAT strip_tac
	THEN bc_tac[subspace_topology_thm, product_topology_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
a(cases_tac⌜s = a⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜¬s ≤ a⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%
From the above, we get the following saying that is $f$ is continuous on $X \times [a, b]$ and $g$ is continuous on $X \times [b, c]$ and $f$ and $g$
agree on $X \times \{b\}$ then $f$ and $g$ can be glued together to give a continuous function on $X \gtimes [a, c]$ that agrees with $f$
on $X \times [a, b]$ and with $g$ on $X \times [b, c]$.
=SML

val ⦏×_interval_glueing_thm⦎ = save_thm ( "×_interval_glueing_thm", (
set_goal([], ⌜∀ρ; σ; f g : 'a × ℝ → 'b; X a b⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	X ⊆ Space⋎T ρ
∧	a ≤ b ∧ b ≤ c
∧	f ∈ ((X × ClosedInterval a b) ◁⋎T ρ ×⋎T O⋎R, σ) Continuous
∧	g ∈ ((X × ClosedInterval b c) ◁⋎T ρ ×⋎T O⋎R, σ) Continuous
∧	(∀x⦁ x ∈ X ⇒ f(x, b) = g(x, b))
⇒	∃h : 'a × ℝ → 'b⦁
	h ∈ ((X × ClosedInterval a c) ◁⋎T ρ ×⋎T O⋎R, σ) Continuous
∧	(∀x s⦁	x ∈ X ∧ s ∈ ClosedInterval a b
	⇒	h(x, s) = f(x, s))
∧	(∀x s⦁	x ∈ X ∧ s ∈ ClosedInterval b c
	⇒	h(x, s) = g(x, s))
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[closed_interval_extension_thm]);
a(asm_tac open_ℝ_topology_thm);
a(LIST_DROP_NTH_ASM_T [7, 8] discard_tac
	THEN rename_tac[(⌜g'⌝, "eg"), (⌜g''⌝, "ef")]);
a(∃_tac⌜λxs⦁ if Snd xs ≤ b then ef xs else eg xs⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜(X × ClosedInterval a c) ⊆ (X × Universe)⌝
	THEN1 MERGE_PCS_T1 ["'pair", "sets_ext1"] prove_tac[×_def]);
a(lemma_tac⌜ρ ×⋎T O⋎R ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(ALL_FC_T (once_rewrite_tac o map (conv_rule (ONCE_MAP_C eq_sym_conv)))
	 [⊆_subspace_topology_thm]);
a(bc_thm_tac subspace_domain_continuous_thm);
a(REPEAT strip_tac THEN1 (bc_thm_tac subspace_topology_thm THEN REPEAT strip_tac));
a(LEMMA_T ⌜∀xs⦁Snd xs ≤ b ⇔ xs ∈ {(x, s) | s ≤ b}⌝ pure_once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(lemma_tac⌜(X × Universe) ◁⋎T ρ ×⋎T O⋎R ∈ Topology⌝
	THEN1 (bc_thm_tac subspace_topology_thm THEN REPEAT strip_tac));
a(bc_thm_tac cond_continuous_thm THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 ante_tac);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]);
a(rewrite_tac[×_def] THEN strip_tac);
a(lemma_tac⌜Snd x = b⌝);
(* *** Goal "1.1" *** *)
a(lemma_tac⌜Snd x < b ∨ Snd x = b ∨ b < Snd x⌝
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[] THEN i_contr_tac);
(* *** Goal "1.1.1" *** *)
a(swap_nth_asm_concl_tac 4 THEN strip_tac);
a(∃_tac⌜X × OpenInterval (Snd x + ~1.) b⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1.1.1" *** *)
a(PC_T1 "sets_ext1" asm_rewrite_tac[×_def, open_interval_def]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.1.1.2" *** *)
a(rewrite_tac[subspace_topology_def]);
a(∃_tac⌜Space⋎T ρ ×  OpenInterval (Snd x + ~ 1.) b⌝
	THEN REPEAT strip_tac);
(* *** Goal "1.1.1.2.1" *** *)
a(rewrite_tac[product_topology_def, ×_def] THEN REPEAT strip_tac);
a(∃_tac⌜Space⋎T ρ⌝ THEN ∃_tac⌜OpenInterval (Snd x + ~ 1.) b⌝
	THEN asm_rewrite_tac[open_interval_open_thm]);
a(ALL_FC_T rewrite_tac[space_t_open_thm]);
(* *** Goal "1.1.1.2.2" *** *)
a(DROP_NTH_ASM_T 15 ante_tac
	THEN MERGE_PCS_T1 ["'pair", "sets_ext1"] prove_tac[×_def]);
(* *** Goal "1.1.1.3" *** *)
a(swap_nth_asm_concl_tac 1);
a(DROP_NTH_ASM_T 3 ante_tac);
a(rewrite_tac[×_def, open_interval_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.1.2" *** *)
a(swap_nth_asm_concl_tac 4 THEN strip_tac);
a(∃_tac⌜X × OpenInterval b (Snd x + 1.)⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1.2.1" *** *)
a(PC_T1 "sets_ext1" asm_rewrite_tac[×_def, open_interval_def]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.1.2.2" *** *)
a(rewrite_tac[subspace_topology_def]);
a(∃_tac⌜Space⋎T ρ ×  OpenInterval b (Snd x + 1.)⌝
	THEN REPEAT strip_tac);
(* *** Goal "1.1.2.2.1" *** *)
a(rewrite_tac[product_topology_def, ×_def] THEN REPEAT strip_tac);
a(∃_tac⌜Space⋎T ρ⌝ THEN ∃_tac⌜OpenInterval b (Snd x + 1.)⌝
	THEN asm_rewrite_tac[open_interval_open_thm]);
a(ALL_FC_T rewrite_tac[space_t_open_thm]);
(* *** Goal "1.1.2.2.2" *** *)
a(DROP_NTH_ASM_T 15 ante_tac
	THEN MERGE_PCS_T1 ["'pair", "sets_ext1"] prove_tac[×_def]);
(* *** Goal "1.1.2.3" *** *)
a(swap_nth_asm_concl_tac 2);
a(DROP_NTH_ASM_T 1 ante_tac);
a(rewrite_tac[×_def, open_interval_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜Snd x ∈ ClosedInterval a b ∧ Snd x ∈ ClosedInterval b c⌝
	THEN1 (rewrite_tac[closed_interval_def]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LIST_DROP_NTH_ASM_T [11, 13] (ALL_FC_T (MAP_EVERY ante_tac)));
a(rewrite_tac[] THEN REPEAT (STRIP_T rewrite_thm_tac));
a(LEMMA_T⌜x = (Fst x, b)⌝ once_rewrite_thm_tac THEN1 asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 13 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[closed_interval_def]));
a(asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN asm_rewrite_tac[closed_interval_def]);
(* *** Goal "3" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[closed_interval_def]));
a(asm_rewrite_tac[]);
a(cases_tac⌜s = b⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "3.1" *** *)
a(LEMMA_T ⌜g(x, b) = f(x, b)⌝ rewrite_thm_tac
	THEN1 LIST_DROP_NTH_ASM_T [7] (ALL_FC_T rewrite_tac));
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN asm_rewrite_tac[closed_interval_def]);
(* *** Goal "3.2" *** *)
a(lemma_tac⌜¬s ≤ b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 9 bc_thm_tac THEN asm_rewrite_tac[closed_interval_def]);
pop_thm()
));


=TEX
\subsection{The Path Groupoid}

%%%%
%%%%

=SML

val ⦏paths_continuous_thm⦎ = save_thm ( "paths_continuous_thm", (
set_goal([], ⌜∀τ f⦁
	τ ∈ Topology
∧	f ∈ Paths τ
⇒	f ∈ (O⋎R, τ) Continuous
⌝);
a(prove_tac[paths_def]);
pop_thm()
));

val ⦏paths_representative_thm⦎ = save_thm ( "paths_representative_thm", (
set_goal([], ⌜∀τ f⦁
	τ ∈ Topology
∧	f ∈ (O⋎R, τ) Continuous
⇒	∃⋎1 g⦁ g ∈ Paths τ ∧ ∀s⦁ s ∈ ClosedInterval 0. 1. ⇒ g s = f s
⌝);
a(rewrite_tac[paths_def] THEN REPEAT strip_tac);
a(∃⋎1_tac ⌜λt⦁ if t ≤ 0. then f 0. else if t ≤ 1. then f t else f 1.⌝
	THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_rewrite_tac[]);
a(REPEAT strip_tac THEN_TRY ℝ_continuity_tac[] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a(bc_thm_tac continuous_∈_space_t_thm);
a(∃_tac⌜O⋎R⌝ THEN asm_rewrite_tac[space_t_ℝ_thm]);
(* *** Goal "1.2" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_rewrite_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY ℝ_continuity_tac[] THEN_TRY asm_rewrite_tac[]);
a(bc_thm_tac continuous_∈_space_t_thm);
a(∃_tac⌜O⋎R⌝ THEN asm_rewrite_tac[space_t_ℝ_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(LEMMA_T⌜¬ x ≤ 0.⌝ asm_rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜x = 1.⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜¬ x ≤ 1.⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[closed_interval_def]));
a(cases_tac⌜s = 0.⌝ THEN asm_rewrite_tac[]);
a(LEMMA_T⌜¬ s ≤ 0.⌝ asm_rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "5" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[closed_interval_def]));
a(cases_tac ⌜x ≤ 0.⌝ THEN ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "5.1" *** *)
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "5.2" *** *)
a(cases_tac⌜x ≤ 1.⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5.2.1" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "5.2.2" *** *)
a(lemma_tac⌜1. ≤ x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5] (ALL_FC_T rewrite_tac));
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX

%%%%
%%%%

=SML

val ⦏path_0_path_thm⦎ = save_thm ( "path_0_path_thm", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology
∧	x ∈ Space⋎T τ
⇒	0⋎P x ∈ Paths τ
⌝);
a(rewrite_tac[paths_def, path_0_def] THEN REPEAT strip_tac);
a(bc_thm_tac const_continuous_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_path_path_thm⦎ = save_thm ( "path_plus_path_path_thm", (
set_goal([], ⌜∀τ f g⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	g ∈ Paths τ
∧	g(ℕℝ 0) = f(ℕℝ 1)
⇒	f +⋎P g ∈ Paths τ
⌝);
a(rewrite_tac[paths_def, path_plus_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_rewrite_tac[]);
a(REPEAT strip_tac THEN_TRY SOLVED_T (ℝ_continuity_tac []));
a(all_var_elim_asm_tac1 THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜x ≤ 1 / 2⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 7 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(LEMMA_T ⌜¬x ≤ 1 / 2⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏minus_path_path_thm⦎ = save_thm ( "minus_path_path_thm", (
set_goal([], ⌜∀τ f⦁
	τ ∈ Topology
∧	f ∈ Paths τ
⇒	 ~⋎P f ∈ Paths τ
⌝);
a(rewrite_tac[path_minus_def, paths_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ℝ_continuity_tac []);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_assoc_lemma1⦎ = (* not saved *) snd ( "path_plus_assoc_lemma1", (
set_goal([], ⌜∀τ f g h k⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	g ∈ Paths τ
∧	h ∈ Paths τ
∧	(∀t⦁k t = if t ≤ 1/4 then ℕℝ 2*t else if t ≤ 1/2 then t + 1/4 else (1/2)*t + 1/2)
⇒	((f +⋎P g) +⋎P h) = λt⦁ (f +⋎P (g +⋎P h)) (k t)
⌝);
a(rewrite_tac[paths_def, path_plus_def] THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
a(cases_tac⌜x ≤ 1/4⌝ THEN cases_tac ⌜x ≤ 1/2⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(LEMMA_T⌜ℕℝ 2*x ≤ 1/2⌝  rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(LEMMA_T⌜¬ℕℝ 2*x ≤ 1/2 ∧ ¬x + 1/4 ≤ 1/2⌝  rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ℕℝ 2 * ((x + 1 / 4) + ~ (1 / 2)) ≤ 1 / 2⌝  rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN strip_tac);
(* *** Goal "4" *** *)
a(LEMMA_T⌜¬(1/2)*x ≤ ℕℝ 0⌝  rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜¬ℕℝ 2 * ((1 / 2 * x + 1 / 2) + ~ (1 / 2)) ≤ 1 / 2⌝  rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_assoc_lemma2⦎ = (* not saved *) snd ( "path_plus_assoc_lemma2", (
set_goal([], ⌜∀k⦁
	(∀t⦁k t = if t ≤ 1/4 then ℕℝ 2*t else if t ≤ 1/2 then t + 1/4 else (1/2)*t + 1/2)
⇒	k ∈ (O⋎R, O⋎R) Continuous
⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) (∀_elim⌜k⌝η_axiom)]);
a(POP_ASM_T pure_rewrite_thm_tac);
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(rewrite_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY SOLVED_T (ℝ_continuity_tac []));
(* *** Goal "1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(rewrite_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY SOLVED_T (ℝ_continuity_tac []));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_assoc_lemma3⦎ = (* not saved *) snd ( "path_plus_assoc_lemma3", (
set_goal([], ⌜∀k⦁
	(∀t⦁k t = if t ≤ 1/4 then ℕℝ 2*t else if t ≤ 1/2 then t + 1/4 else (1/2)*t + 1/2)
⇒	((O⋎R, {ℕℝ 0; ℕℝ 1},O⋎R) Homotopic) k (λx⦁x)
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac homotopic_⊆_thm);
a(strip_asm_tac open_ℝ_topology_thm THEN asm_rewrite_tac[]);
a(∃_tac⌜{x | (λx⦁ x) x = k x}⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac homotopic_ℝ_thm);
a(ALL_FC_T asm_rewrite_tac[id_continuous_thm, path_plus_assoc_lemma2]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_assoc_thm⦎ = save_thm ( "path_plus_assoc_thm", (
set_goal([], ⌜∀τ f g h⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	g ∈ Paths τ
∧	h ∈ Paths τ
∧	g(ℕℝ 0) = f(ℕℝ 1)
∧	h(ℕℝ 0) = g(ℕℝ 1)
⇒	PathHomotopic τ ((f +⋎P g) +⋎P h) (f +⋎P (g +⋎P h))
⌝);
a(rewrite_tac [path_homotopic_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∃k⦁∀t⦁k t = if t ≤ 1/4 then ℕℝ 2*t else if t ≤ 1/2 then t + 1/4 else (1/2)*t + 1/2⌝
	THEN1 prove_∃_tac);
a(strip_asm_tac open_ℝ_topology_thm);
a(all_fc_tac[path_plus_assoc_lemma2, path_plus_assoc_lemma3]);
a(pure_once_rewrite_tac[prove_rule[]⌜f +⋎P g +⋎P h = λt⦁(f +⋎P g +⋎P h)((λx⦁ x) t)⌝]);
a(PC_T1 "predicates" (ALL_FC_T pure_rewrite_tac)[path_plus_assoc_lemma1]);
a(bc_thm_tac homotopic_comp_left_thm);
a(∃_tac⌜O⋎R⌝ THEN REPEAT strip_tac);
a(bc_tac [path_plus_path_path_thm, paths_continuous_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_tac [path_plus_path_path_thm, paths_continuous_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[path_plus_def]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_0_lemma1⦎ = (* not saved *) snd ( "path_plus_0_lemma1", (
set_goal([], ⌜∀τ f k⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 2*t else ℕℝ 1)
⇒	(f +⋎P 0⋎P (f(ℕℝ 1))) = λt⦁ f (k t)
⌝);
a(rewrite_tac[paths_def, path_plus_def, path_0_def] THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
a(cases_tac⌜x ≤ 1/2⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_0_lemma2⦎ = (* not saved *) snd ( "path_plus_0_lemma2", (
set_goal([], ⌜∀k⦁
	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 2*t else ℕℝ 1)
⇒	k ∈ (O⋎R, O⋎R) Continuous
⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) (∀_elim⌜k⌝η_axiom)]);
a(POP_ASM_T pure_rewrite_thm_tac);
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(rewrite_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY (SOLVED_T (ℝ_continuity_tac[])));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_0_lemma3⦎ = (* not saved *) snd ( "path_plus_0_lemma3", (
set_goal([], ⌜∀k⦁
	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 2*t else ℕℝ 1)
⇒	((O⋎R, {ℕℝ 0; ℕℝ 1},O⋎R) Homotopic) k (λx⦁x)
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac homotopic_⊆_thm);
a(strip_asm_tac open_ℝ_topology_thm THEN asm_rewrite_tac[]);
a(∃_tac⌜{x |(λx⦁ x) x = k x}⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac homotopic_ℝ_thm);
a(ALL_FC_T asm_rewrite_tac[id_continuous_thm, path_plus_0_lemma2]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_0_thm⦎ = save_thm ( "path_plus_0_thm", (
set_goal([], ⌜∀τ f x⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	f 1. = x
⇒	PathHomotopic τ (f +⋎P 0⋎P x) f
⌝);
a(rewrite_tac[path_homotopic_def] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(lemma_tac⌜∃k⦁∀t⦁k t = if t ≤ 1/2 then ℕℝ 2*t else ℕℝ 1⌝
	THEN1 prove_∃_tac);
a(strip_asm_tac open_ℝ_topology_thm);
a(all_fc_tac[path_plus_0_lemma2, path_plus_0_lemma3]);
a(conv_tac (RAND_C (pure_once_rewrite_conv[prove_rule[]⌜f = λt⦁f ((λt⦁t)t)⌝])));
a(PC_T1 "predicates" (ALL_FC_T pure_rewrite_tac)[path_plus_0_lemma1]);
a(bc_thm_tac homotopic_comp_left_thm);
a(∃_tac⌜O⋎R⌝ THEN REPEAT strip_tac);
a(bc_tac [paths_continuous_thm] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_0_plus_lemma1⦎ = (* not saved *) snd ( "path_0_plus_lemma1", (
set_goal([], ⌜∀τ f k⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 0 else ℕℝ 2*t + ~(ℕℝ 1))
⇒	0⋎P (f(ℕℝ 0)) +⋎P f = λt⦁ f (k t)
⌝);
a(rewrite_tac[paths_def, path_plus_def, path_0_def] THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
a(cases_tac⌜x ≤ 1/2⌝ THEN  asm_rewrite_tac[]);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN  asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_0_plus_lemma2⦎ = (* not saved *) snd ( "path_0_plus_lemma2", (
set_goal([], ⌜∀k⦁
	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 0 else ℕℝ 2*t + ~(ℕℝ 1))
⇒	k ∈ (O⋎R, O⋎R) Continuous
⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) (∀_elim⌜k⌝η_axiom)]);
a(POP_ASM_T pure_rewrite_thm_tac);
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(rewrite_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY (SOLVED_T (ℝ_continuity_tac[])));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_0_plus_lemma3⦎ = (* not saved *) snd ( "path_0_plus_lemma3", (
set_goal([], ⌜∀k⦁
	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 0 else ℕℝ 2*t + ~(ℕℝ 1))
⇒	((O⋎R, {ℕℝ 0; ℕℝ 1},O⋎R) Homotopic) k (λx⦁x)
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac homotopic_⊆_thm);
a(strip_asm_tac open_ℝ_topology_thm THEN asm_rewrite_tac[]);
a(∃_tac⌜{x | (λx⦁ x) x = k x}⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac homotopic_ℝ_thm);
a(ALL_FC_T asm_rewrite_tac[id_continuous_thm, path_0_plus_lemma2]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_0_plus_thm⦎ = save_thm ( "path_0_plus_thm", (
set_goal([], ⌜∀τ f x⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	f 0. = x
⇒	PathHomotopic τ (0⋎P x +⋎P f) f
⌝);
a(rewrite_tac[path_homotopic_def] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(lemma_tac⌜∃k⦁	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 0 else ℕℝ 2*t + ~(ℕℝ 1))⌝
	THEN1 prove_∃_tac);
a(strip_asm_tac open_ℝ_topology_thm);
a(all_fc_tac[path_0_plus_lemma2, path_0_plus_lemma3]);
a(conv_tac (RAND_C (pure_once_rewrite_conv[prove_rule[]⌜f = λt⦁f ((λt⦁t)t)⌝])));
a(PC_T1 "predicates" (ALL_FC_T pure_rewrite_tac)[path_0_plus_lemma1]);
a(bc_thm_tac homotopic_comp_left_thm);
a(∃_tac⌜O⋎R⌝ THEN REPEAT strip_tac);
a(bc_tac [paths_continuous_thm] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_minus_lemma1⦎ = (* not saved *) snd ( "path_plus_minus_lemma1", (
set_goal([], ⌜∀τ f k⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 2*t else ℕℝ 2 + ~(ℕℝ 2*t) )
⇒	f +⋎P ~⋎P f= λt⦁ f (k t)
⌝);
a(rewrite_tac[paths_def, path_plus_def, path_minus_def] THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
a(cases_tac⌜x ≤ 1/2⌝ THEN  asm_rewrite_tac[]);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_minus_lemma2⦎ = (* not saved *) snd ( "path_plus_minus_lemma2", (
set_goal([], ⌜∀k⦁
	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 2*t else ℕℝ 2 + ~(ℕℝ 2*t) )
⇒	k ∈ (O⋎R, O⋎R) Continuous
⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) (∀_elim⌜k⌝η_axiom)]);
a(POP_ASM_T pure_rewrite_thm_tac);
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(rewrite_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY (SOLVED_T (ℝ_continuity_tac[])));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_minus_lemma3⦎ = (* not saved *) snd ( "path_plus_minus_lemma3", (
set_goal([], ⌜∀k⦁
	(∀t⦁k t = if t ≤ 1/2 then ℕℝ 2*t else ℕℝ 2 + ~(ℕℝ 2*t) )
⇒	((O⋎R, {ℕℝ 0; ℕℝ 1},O⋎R) Homotopic) k (λx⦁ℕℝ 0)
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac homotopic_⊆_thm);
a(strip_asm_tac open_ℝ_topology_thm THEN asm_rewrite_tac[]);
a(∃_tac⌜{x | (λx⦁ ℕℝ 0) x = k x}⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac homotopic_ℝ_thm);
a(lemma_tac⌜ℕℝ 0 ∈ Space⋎T O⋎R⌝ THEN1 rewrite_tac[space_t_ℝ_thm]);
a(ALL_FC_T asm_rewrite_tac[const_continuous_thm, path_plus_minus_lemma2]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_plus_minus_thm⦎ = save_thm ( "path_plus_minus_thm", (
set_goal([], ⌜∀τ f x⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	f 0. = x
⇒	PathHomotopic τ (f +⋎P ~⋎P f) (0⋎P x)
⌝);
a(rewrite_tac[path_homotopic_def] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(lemma_tac⌜∃k⦁ (∀t⦁k t = if t ≤ 1/2 then ℕℝ 2*t else ℕℝ 2 + ~(ℕℝ 2*t) )⌝
	THEN1 prove_∃_tac);
a(strip_asm_tac open_ℝ_topology_thm);
a(all_fc_tac[path_plus_minus_lemma2, path_plus_minus_lemma3]);
a(rewrite_tac[path_0_def]);
a(pure_once_rewrite_tac[prove_rule[]⌜(λt⦁f(ℕℝ 0)) =(λt⦁f((λt⦁ℕℝ 0)t))⌝]);
a(PC_T1 "predicates" (ALL_FC_T pure_rewrite_tac)[path_plus_minus_lemma1]);
a(bc_thm_tac homotopic_comp_left_thm);
a(∃_tac⌜O⋎R⌝ THEN REPEAT strip_tac);
a(bc_tac [paths_continuous_thm] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_minus_minus_thm⦎ = save_thm ( "path_minus_minus_thm", (
set_goal([], ⌜∀f⦁
	 ~⋎P (~⋎P f) = f
⌝);
a(rewrite_tac[path_minus_def] THEN conv_tac (ONCE_MAP_C ℝ_anf_conv));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_minus_plus_thm⦎ = save_thm ( "path_minus_plus_thm", (
set_goal([], ⌜∀τ f x⦁
	τ ∈ Topology
∧	f ∈ Paths τ
∧	f 1. = x
⇒	PathHomotopic τ (~⋎P f +⋎P f) (0⋎P x)
⌝);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(all_fc_tac[minus_path_path_thm]);
a(DROP_NTH_ASM_T 2 discard_tac);
a(lemma_tac⌜~⋎P f 0. = f 1.⌝ THEN1 rewrite_tac[path_minus_def]);
a(ALL_FC_T (MAP_EVERY ante_tac) [path_plus_minus_thm]);
a(rewrite_tac[path_minus_minus_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏paths_space_t_thm⦎ = save_thm ( "paths_space_t_thm", (
set_goal([], ⌜∀τ f x⦁
	f ∈ Paths τ ⇒ f x ∈ Space⋎T τ
⌝);
a(rewrite_tac[paths_def, continuous_def, space_t_ℝ_thm] THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_comp_continuous_path_thm⦎ = save_thm ( "path_comp_continuous_path_thm", (
set_goal([], ⌜∀σ τ f g⦁
	σ ∈ Topology ∧
	τ ∈ Topology ∧
	f ∈ Paths σ ∧
	g ∈ (σ, τ) Continuous
⇒ 	(λx⦁g(f x)) ∈ Paths τ
⌝);
a(rewrite_tac[paths_def, space_t_ℝ_thm]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ℝ_continuity_tac[]);
(* *** Goal "2" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "3" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_from_arc_thm⦎ = save_thm ( "path_from_arc_thm", (
set_goal([], ⌜∀τ f⦁
	τ ∈ Topology ∧
	f ∈ (O⋎R, τ) Continuous
⇒ 	(λt⦁ if t ≤ 0. then f 0. else if t ≤ 1.then f t else f 1.) ∈ Paths τ
⌝);
a(REPEAT strip_tac THEN rewrite_tac[paths_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(ℝ_continuity_tac[]);
a(bc_thm_tac continuous_∈_space_t_thm);
a(∃_tac⌜O⋎R⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(ℝ_continuity_tac[]);
(* *** Goal "1.2.2" *** *)
a(ℝ_continuity_tac[]);
a(bc_thm_tac continuous_∈_space_t_thm);
a(∃_tac⌜O⋎R⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.3" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜¬x ≤ 0.⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[]);
a(if_cases_tac THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜x = 1.⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏loop_from_arc_thm⦎ = save_thm ( "loop_from_arc_thm", (
set_goal([], ⌜∀τ f⦁
	τ ∈ Topology ∧
	f ∈ (O⋎R, τ) Continuous ∧
	f 1. = f 0.
⇒ 	(λt⦁ if t ≤ 0. ∨ 1. ≤ t then f 0. else f t) ∈ Loops(τ, f 0.)
⌝);
a(REPEAT strip_tac THEN rewrite_tac[loops_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[path_from_arc_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜(λt⦁ if t ≤ 0. ∨ 1. ≤ t then f 0. else f t) = 
	(λt⦁ if t ≤ 0. then f 0. else if t ≤ 1.then f t else f 1.)⌝ rewrite_thm_tac);
(* *** Goal "1.1" *** *)
a(rewrite_tac[] THEN REPEAT strip_tac THEN if_cases_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1.1" *** *)
a(LEMMA_T ⌜x = 1.⌝ asm_rewrite_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.1.2" *** *)
a(LEMMA_T ⌜x = 1.⌝ asm_rewrite_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(all_fc_tac[path_from_arc_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));


=TEX
\subsection{Local Path-connectedness}
Connectedness implies path-connectedness under suitable hypotheses, which we take to be that the surrounding space is locally path-connected and that the set in question is open.
%%%%
%%%%
=SML

val ⦏open_connected_path_connected_thm⦎ = save_thm ( "open_connected_path_connected_thm", (
set_goal([], ⌜∀τ A⦁
	τ ∈ Topology
∧	τ ∈ LocallyPathConnected
∧	A ∈ τ
∧	A ∈ τ Connected
⇒	A ∈ τ PathConnected
⌝);
a(rewrite_tac[path_connected_def, connected_def, locally_path_connected_def]
	THEN REPEAT strip_tac);
a(lemma_tac⌜{z | ∃ f⦁ f ∈ Paths τ ∧ (∀ t⦁ f t ∈ A) ∧ f (ℕℝ 0) = x ∧ f (ℕℝ 1) = z} ∈ τ⌝);
(* *** Goal "1" *** *)
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]
	THEN REPEAT strip_tac);
a(lemma_tac⌜x' ∈ A⌝ THEN1 (all_var_elim_asm_tac1 THEN asm_rewrite_tac[]));
a(list_spec_nth_asm_tac 11 [⌜x'⌝, ⌜A⌝]);
a(∃_tac⌜B⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(list_spec_nth_asm_tac 2 [⌜x'⌝, ⌜x''⌝]);
a(∃_tac⌜f +⋎P f'⌝ THEN REPEAT strip_tac THEN_TRY SOLVED_T (asm_rewrite_tac[path_plus_def]));
(* *** Goal "1.1" *** *)
a(bc_thm_tac path_plus_path_path_thm THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(rewrite_tac[path_plus_def]);
a(if_cases_tac THEN asm_rewrite_tac[]);
a(LEMMA_T⌜f' (ℕℝ 2 * (t + ~ (1 / 2))) ∈ B⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 9 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜{z | z ∈ A ∧ ¬ ∃ f⦁ f ∈ Paths τ ∧ (∀ t⦁ f t ∈ A) ∧ f (ℕℝ 0) = x ∧ f (ℕℝ 1) = z} ∈ τ⌝);
(* *** Goal "2.1" *** *)
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[open_open_neighbourhood_thm]
	THEN REPEAT strip_tac);
a(list_spec_nth_asm_tac 9 [⌜x'⌝, ⌜A⌝]);
a(∃_tac⌜B⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(LIST_DROP_NTH_ASM_T [1, 4] (MAP_EVERY ante_tac) THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(swap_nth_asm_concl_tac 10 THEN REPEAT strip_tac);
a(list_spec_nth_asm_tac 6 [⌜x''⌝, ⌜x'⌝]);
a(∃_tac⌜f +⋎P f'⌝ THEN REPEAT strip_tac THEN_TRY SOLVED_T (asm_rewrite_tac[path_plus_def]));
(* *** Goal "2.1.2.1" *** *)
a(bc_thm_tac path_plus_path_path_thm THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2.2" *** *)
a(rewrite_tac[path_plus_def]);
a(if_cases_tac THEN asm_rewrite_tac[]);
a(LEMMA_T⌜f' (ℕℝ 2 * (t + ~ (1 / 2))) ∈ B⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 13 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜
	A ⊆ {z | ∃ f⦁ f ∈ Paths τ ∧ (∀ t⦁ f t ∈ A) ∧ f (ℕℝ 0) = x ∧ f (ℕℝ 1) = z}
	∪ {z | z ∈ A ∧ ¬ ∃ f⦁ f ∈ Paths τ ∧ (∀ t⦁ f t ∈ A) ∧ f (ℕℝ 0) = x ∧ f (ℕℝ 1) = z}⌝
	THEN1 PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(spec_nth_asm_tac 4 ⌜f⌝);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜
	A ∩ {z | ∃ f⦁ f ∈ Paths τ ∧ (∀ t⦁ f t ∈ A) ∧ f (ℕℝ 0) = x ∧ f (ℕℝ 1) = z}
	∩ {z | z ∈ A ∧ ¬ ∃ f⦁ f ∈ Paths τ ∧ (∀ t⦁ f t ∈ A) ∧ f (ℕℝ 0) = x ∧ f (ℕℝ 1) = z} = {}⌝
	THEN1 PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a(spec_nth_asm_tac 1 ⌜f⌝);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(DROP_NTH_ASM_T 7 (ante_tac o list_∀_elim
	[⌜{z | ∃ f⦁ f ∈ Paths τ ∧ (∀ t⦁ f t ∈ A) ∧ f (ℕℝ 0) = x ∧ f (ℕℝ 1) = z}⌝,
	⌜{z | z ∈ A ∧ ¬ ∃ f⦁ f ∈ Paths τ ∧ (∀ t⦁ f t ∈ A) ∧ f (ℕℝ 0) = x ∧ f (ℕℝ 1) = z}⌝]));
a(asm_rewrite_tac[]);
a(REPEAT_N 4 (POP_ASM_T discard_tac) THEN PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(spec_nth_asm_tac 1 ⌜y⌝);
a(∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2" *** *)
a(i_contr_tac THEN spec_nth_asm_tac 1 ⌜x⌝);
a(swap_nth_asm_concl_tac 1 THEN REPEAT strip_tac);
a(∃_tac⌜λt:ℝ⦁ x⌝ THEN asm_rewrite_tac[paths_def]);
a(bc_thm_tac const_continuous_thm THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3, 4] (MAP_EVERY ante_tac) THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏open_interval_path_connected_thm⦎ = save_thm ( "open_interval_path_connected_thm", (
set_goal([], ⌜∀x y⦁OpenInterval x y ∈ O⋎R PathConnected⌝);
a(rewrite_tac[path_connected_def, open_interval_def, paths_def, space_t_ℝ_thm]
	THEN REPEAT strip_tac);
a(∃_tac⌜λt⦁if t ≤ ℕℝ 0 then x' else if t ≤ ℕℝ 1 then x' + (y' + ~x') * t else y'⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(rewrite_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY SOLVED_T (ℝ_continuity_tac[]));
(* *** Goal "1.1" *** *)
a(ho_bc_thm_tac cond_continuous_ℝ_thm);
a(rewrite_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY SOLVED_T (ℝ_continuity_tac[]));
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(cases_tac⌜x'' = 1.⌝ THEN1 (asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LEMMA_T ⌜¬x'' ≤ 0. ∧ ¬x'' ≤ 1.⌝ rewrite_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(cases_tac ⌜t ≤ 0.⌝ THEN cases_tac ⌜t ≤ 1.⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜x' ≤ y'⌝);
(* *** Goal "4.1" *** *)
a(bc_thm_tac ℝ_less_≤_trans_thm THEN ∃_tac⌜x'⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4.2" *** *)
a(bc_thm_tac ℝ_less_≤_trans_thm THEN ∃_tac⌜y'⌝ THEN REPEAT strip_tac);
a(bc_thm_tac (pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜ℕℝ 0 ≤ (x' + ~y') *(ℕℝ 1 + ~t) ⇒ y' ≤ x' + (y' + ~ x') * t⌝));
a(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "5" *** *)
a(cases_tac ⌜t ≤ 0.⌝ THEN cases_tac ⌜t ≤ 1.⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜x' ≤ y'⌝);
(* *** Goal "5.1" *** *)
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜y'⌝ THEN REPEAT strip_tac);
a(bc_thm_tac (pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜ℕℝ 0 ≤ (y' + ~x') *(ℕℝ 1 + ~t) ⇒ x' + (y' + ~ x') * t ≤ y'⌝));
a(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "5.2" *** *)
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜x'⌝ THEN REPEAT strip_tac);
a(bc_thm_tac (pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜ℕℝ 0 ≤ (x' + ~y') *t ⇒ (y' + ~ x') * t ≤ ℕℝ 0⌝));
a(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "6" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ℝ_locally_path_connected_thm⦎ = save_thm ( "ℝ_locally_path_connected_thm", (
set_goal([], ⌜O⋎R ∈ LocallyPathConnected⌝);
a(rewrite_tac[locally_path_connected_def] THEN REPEAT strip_tac);
a(POP_ASM_T  (fn th => all_fc_tac[rewrite_rule[open_ℝ_def]th]));
a(∃_tac⌜OpenInterval x' y⌝ THEN
	asm_rewrite_tac[open_interval_open_thm, open_interval_path_connected_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏product_locally_path_connected_thm⦎ = save_thm ( "product_locally_path_connected_thm", (
set_goal([], ⌜∀σ τ f a b c⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	σ ∈ LocallyPathConnected
∧	τ ∈ LocallyPathConnected
⇒	(σ ×⋎T τ) ∈ LocallyPathConnected
⌝);
a(rewrite_tac[locally_path_connected_def] THEN REPEAT strip_tac);
a(POP_ASM_T
	(ante_tac o list_∀_elim[⌜Fst x⌝, ⌜Snd x⌝] o rewrite_rule[product_topology_def]));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [8, 7] all_fc_tac);
a(∃_tac⌜B'' × B'⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[product_topology_def] THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[×_def]));
a(∃_tac⌜B''⌝ THEN ∃_tac⌜B'⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[×_def]);
(* *** Goal "3" *** *)
a(LIST_DROP_NTH_ASM_T [2, 6, 9] (MAP_EVERY ante_tac));
a(DROP_ASMS_T discard_tac);
a(MERGE_PCS_T1 ["'bin_rel", "sets_ext1"] REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac);
a(MERGE_PCS_T1 ["'bin_rel", "sets_ext1"] REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "4" *** *)
a(bc_thm_tac product_path_connected_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
\aubsection{Loops}
=TEX
%%%%
%%%%

=SML

val ⦏∈_loops_thm⦎ = save_thm ( "∈_loops_thm", (
set_goal([], ⌜∀τ f x⦁
	f ∈ Loops(τ, x) ⇔ x = f 0. ∧ f ∈ Loops(τ, f 0.)
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T⌜f 0. = x⌝ rewrite_thm_tac THEN POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(ALL_ASM_FC_T rewrite_tac[] THEN POP_ASM_T discard_tac);
a(LEMMA_T⌜f 0. = x⌝ rewrite_thm_tac THEN POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(ALL_ASM_FC_T rewrite_tac[] THEN POP_ASM_T discard_tac);
a(LEMMA_T⌜f 0. = x⌝ rewrite_thm_tac THEN POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "4" *** *)
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
(* *** Goal "5" *** *)
a(all_var_elim_asm_tac1 THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏path_0_loop_thm⦎ = save_thm ( "path_0_loop_thm", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology
∧	x ∈ Space⋎T τ
⇒	0⋎P x ∈ Loops(τ, x)
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[path_0_path_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[path_0_def]);
(* *** Goal "3" *** *)
a(rewrite_tac[path_0_def]);
pop_thm()
));


=TEX
%%%%
%%%%
=SML

val ⦏loop_plus_loop_loop_thm⦎ = save_thm ( "loop_plus_loop_loop_thm", (
set_goal([], ⌜∀τ x f g⦁
	τ ∈ Topology
∧	f ∈ Loops(τ, x)
∧	g ∈ Loops(τ, x)
⇒	f +⋎P g ∈ Loops(τ, x)
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac path_plus_path_path_thm THEN REPEAT strip_tac);
a(∧_THEN asm_tac (prove_rule[] ⌜0. ≤ 0. ∧ 1. ≤ 1.⌝) THEN ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac ⌜t ≤ 1/2 ∧ 2. * t ≤ 0. ⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[path_plus_def] THEN ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac ⌜¬t ≤ 1/2 ∧ 1. ≤ 2. * (t + ~(1/2)) ⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[path_plus_def] THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏minus_loop_loop_thm⦎ = save_thm ( "minus_loop_loop_thm", (
set_goal([], ⌜∀τ x f g⦁
	τ ∈ Topology
∧	f ∈ Loops(τ, x)
⇒	~⋎P f ∈ Loops(τ, x)
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac minus_path_path_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(rewrite_tac[path_minus_def]);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(rewrite_tac[path_minus_def]);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏loop_plus_assoc_thm⦎ = save_thm ( "loop_plus_assoc_thm", (
set_goal([], ⌜∀τ x f g h⦁
	τ ∈ Topology
∧	f ∈ Loops(τ, x)
∧	g ∈ Loops(τ, x)
∧	h ∈ Loops(τ, x)
⇒	PathHomotopic τ ((f +⋎P g) +⋎P h) (f +⋎P (g +⋎P h))
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac THEN
	bc_tac [path_plus_assoc_thm] THEN REPEAT strip_tac
	THEN ∧_THEN asm_tac (prove_rule[] ⌜0. ≤ 0. ∧ 1. ≤ 1.⌝) THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏loop_plus_0_thm⦎ = save_thm ( "loop_plus_0_thm", (
set_goal([], ⌜∀τ x f⦁
	τ ∈ Topology
∧	f ∈ Loops(τ, x)
⇒	PathHomotopic τ (f +⋎P 0⋎P x) f
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac
	THEN bc_tac [path_plus_0_thm] THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏loop_0_plus_thm⦎ = save_thm ( "loop_0_plus_thm", (
set_goal([], ⌜∀τ f x⦁
	τ ∈ Topology
∧	f ∈ Loops(τ, x)
⇒	PathHomotopic τ (0⋎P x +⋎P f) f
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac
	THEN bc_tac [path_0_plus_thm] THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏loop_minus_minus_thm⦎ = save_thm ( "loop_minus_minus_thm", (
set_goal([], ⌜∀f⦁
	 ~⋎P (~⋎P f) = f
⌝);
a(accept_tac path_minus_minus_thm);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏loop_plus_minus_thm⦎ = save_thm ( "loop_plus_minus_thm", (
set_goal([], ⌜∀τ f x⦁
	τ ∈ Topology
∧	f ∈ Loops(τ, x)
⇒	PathHomotopic τ (f +⋎P ~⋎P f) (0⋎P x)
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac
	THEN bc_tac [path_plus_minus_thm] THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏loop_minus_plus_thm⦎ = save_thm ( "loop_minus_plus_thm", (
set_goal([], ⌜∀τ f x⦁
	τ ∈ Topology
∧	f ∈ Loops(τ, x)
⇒	PathHomotopic τ (~⋎P f +⋎P f) (0⋎P x)
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac
	THEN bc_tac [path_minus_plus_thm] THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));



=TEX
%%%%
%%%%

=SML
val ⦏fun_grp_class_def⦎ = get_spec ⌜FunGrpClass⌝;

=TEX
%%%%
%%%%

=SML

val ⦏loops_homotopic_equiv_thm⦎ = save_thm ( "loops_homotopic_equiv_thm", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ
⇒	Equiv(Loops(τ, x), PathHomotopic τ)
⌝);
a(REPEAT strip_tac THEN bc_thm_tac equiv_mono_thm);
a(∃_tac⌜ (O⋎R, τ) Continuous ⌝);
a(rewrite_tac[path_homotopic_def]);
a(asm_tac open_ℝ_topology_thm THEN ALL_FC_T rewrite_tac[homotopic_equiv_thm]);
a(rewrite_tac[loops_def, paths_def] THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏loops_homotopic_refl_thm⦎ = save_thm ( "loops_homotopic_refl_thm", (
set_goal([], ⌜∀τ x p q⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	f ∈ Loops(τ, x)
⇒	PathHomotopic τ f f
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[rewrite_rule[equiv_def, refl_def] loops_homotopic_equiv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏loops_homotopic_sym_thm⦎ = save_thm ( "loops_homotopic_sym_thm", (
set_goal([], ⌜∀τ x p q⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	f ∈ Loops(τ, x) ∧ g ∈ Loops(τ, x) ∧
	PathHomotopic τ f g
⇒	PathHomotopic τ g f
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[rewrite_rule[equiv_def, sym_def] loops_homotopic_equiv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏loops_homotopic_trans_thm⦎ = save_thm ( "loops_homotopic_trans_thm", (
set_goal([], ⌜∀τ x p q⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	f ∈ Loops(τ, x) ∧ g ∈ Loops(τ, x) ∧ h ∈ Loops(τ, x) ∧
	PathHomotopic τ f g ∧ PathHomotopic τ g h
⇒	PathHomotopic τ f h
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[rewrite_rule[equiv_def, trans_def] loops_homotopic_equiv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏loop_plus_respects_lemma1⦎ = save_thm ( "loop_plus_respects_lemma1", (
set_goal([], ⌜∀τ x f g h⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	f ∈ Loops(τ, x) ∧ g ∈ Loops(τ, x) ∧ h ∈ Loops(τ, x) ∧
	PathHomotopic τ f g
⇒	PathHomotopic τ (f +⋎P h) (g +⋎P h)
⌝);
a(rewrite_tac[path_plus_def, path_homotopic_def, homotopic_def, homotopy_def,
	loops_def, paths_def] THEN REPEAT strip_tac);
a(∃_tac⌜λxt⦁
	if Fst xt ≤ 1/2
	then (λxt⦁ H(2. * Fst xt, Snd xt)) xt
	else (λxt⦁ h (2. * (Fst xt - 1/2))) xt⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac cond_continuous_ℝ_thm THEN asm_rewrite_tac[]);
a(lemma_tac ⌜O⋎R ×⋎T O⋎R ∈ Topology⌝ THEN1 basic_topology_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY ℝ_continuity_tac[]);
a(pair_tac ⌜x' = (y, t)⌝ THEN all_asm_ante_tac THEN rewrite_tac[] THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv));
a(DROP_NTH_ASM_T 5 (ante_tac o ∀_elim ⌜1.⌝) THEN rewrite_tac[]
	THEN strip_tac);
a(LEMMA_T ⌜H(1., t) = H(1., 0.)⌝ rewrite_thm_tac
	THEN1 POP_ASM_T rewrite_thm_tac);
a(asm_rewrite_tac[]);
a(spec_nth_asm_tac 15 ⌜1.⌝);
a(spec_nth_asm_tac 8 ⌜0.⌝);
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN rewrite_tac[]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
(* *** Goal "4" *** *)
a(if_cases_tac THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a(if_cases_tac THEN asm_rewrite_tac[]);
pop_thm()
));



=TEX
%%%%
%%%%

=SML

val ⦏loop_plus_respects_lemma2⦎ = save_thm ( "loop_plus_respects_lemma2", (
set_goal([], ⌜∀τ x f g h⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	f ∈ Loops(τ, x) ∧ g ∈ Loops(τ, x) ∧ h ∈ Loops(τ, x) ∧
	PathHomotopic τ g h
⇒	PathHomotopic τ (f +⋎P g) (f +⋎P h)
⌝);
a(rewrite_tac[path_plus_def, path_homotopic_def, homotopic_def, homotopy_def,
	loops_def, paths_def] THEN REPEAT strip_tac);
a(∃_tac⌜λxt⦁
	if Fst xt ≤ 1/2
	then (λxt⦁ f(2. * Fst xt)) xt
	else (λxt⦁ H(2. * (Fst xt - 1/2), Snd xt)) xt⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac cond_continuous_ℝ_thm THEN asm_rewrite_tac[]);
a(lemma_tac ⌜O⋎R ×⋎T O⋎R ∈ Topology⌝ THEN1 basic_topology_tac[open_ℝ_topology_thm]);
a(REPEAT strip_tac THEN_TRY ℝ_continuity_tac[]);
a(pair_tac ⌜x' = (y, t)⌝ THEN all_asm_ante_tac THEN rewrite_tac[] THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv));
a(DROP_NTH_ASM_T 5 (ante_tac o ∀_elim ⌜0.⌝) THEN rewrite_tac[]
	THEN strip_tac);
a(LEMMA_T ⌜H(0., t) = H(0., 0.)⌝ rewrite_thm_tac
	THEN1 POP_ASM_T rewrite_thm_tac);
a(asm_rewrite_tac[]);
a(spec_nth_asm_tac 15 ⌜1.⌝);
a(spec_nth_asm_tac 12 ⌜0.⌝);
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN rewrite_tac[]);
(* *** Goal "4" *** *)
a(if_cases_tac THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a(if_cases_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏loop_plus_respects_thm1⦎ = save_thm ( "loop_minus_respects_thm1", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ
⇒	∀g⦁ g ∈ Loops(τ, x) ⇒
		((λf⦁ FunGrpClass(τ, x) (f +⋎P g)) Respects PathHomotopic τ) (Loops(τ, x))
⌝);
a(rewrite_tac[respects_def, fun_grp_class_def] THEN REPEAT strip_tac);
a(ante_tac (list_∀_elim[⌜Loops(τ, x)⌝, ⌜PathHomotopic τ⌝, ⌜x' +⋎P g⌝, ⌜y +⋎P g⌝] equiv_class_eq_thm));
a(ALL_FC_T asm_rewrite_tac[loops_homotopic_equiv_thm, loop_plus_loop_loop_thm]);
a(STRIP_T rewrite_thm_tac);
a(bc_thm_tac loop_plus_respects_lemma1);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
pop_thm()
));
=TEX
%%%%
%%%%

=SML

val ⦏loop_plus_respects_thm2⦎ = save_thm ( "loop_minus_respects_thm2", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ
⇒	∀f⦁ f ∈ Loops(τ, x) ⇒
		((λg⦁ FunGrpClass(τ, x) (f +⋎P g)) Respects PathHomotopic τ) (Loops(τ, x))
⌝);
a(rewrite_tac[respects_def, fun_grp_class_def] THEN REPEAT strip_tac);
a(ante_tac (list_∀_elim[⌜Loops(τ, x)⌝, ⌜PathHomotopic τ⌝, ⌜f +⋎P x'⌝, ⌜f +⋎P y⌝] equiv_class_eq_thm));
a(ALL_FC_T asm_rewrite_tac[loops_homotopic_equiv_thm, loop_plus_loop_loop_thm]);
a(STRIP_T rewrite_thm_tac);
a(bc_thm_tac loop_plus_respects_lemma2);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

(*
drop_main_goal();
*)

val _ = save_consistency_thm ⌜FunGrpTimes⌝ (
push_consistency_goal ⌜FunGrpTimes⌝;
a(prove_∃_tac THEN REPEAT strip_tac);
a(pair_tac ⌜x' = (τ, x)⌝);
a(cases_tac ⌜τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	 p' ∈ Loops (τ, x) / PathHomotopic τ∧  q' ∈ Loops (τ, x) / PathHomotopic τ⌝
	THEN asm_rewrite_tac[]);
a(all_fc_tac[loops_homotopic_equiv_thm]);
a((strip_asm_tac o list_∀_elim[⌜τ⌝, ⌜x⌝]) loop_plus_respects_thm1);
a((strip_asm_tac o list_∀_elim[⌜τ⌝, ⌜x⌝]) loop_plus_respects_thm2);
a((ante_tac o list_∀_elim[⌜Loops(τ, x)⌝, ⌜PathHomotopic τ⌝,
	⌜Loops(τ, x)⌝, ⌜PathHomotopic τ⌝, ⌜(λ f g⦁ FunGrpClass (τ, x) (f +⋎P g))⌝])
		dyadic_induced_fun_∃_thm);
a(asm_rewrite_tac[] THEN strip_tac);
a(∃_tac⌜g p' q'⌝ THEN REPEAT strip_tac);
a(ALL_ASM_FC_T rewrite_tac[]);
pop_thm());

val ⦏fun_grp_times_def⦎ = get_spec ⌜FunGrpTimes⌝;

(*
dyadic_induced_fun_∃_thm;

*)

=TEX
%%%%
%%%%

=SML

val ⦏loop_minus_respects_lemma⦎ = save_thm ( "loop_minus_respects_lemma", (
set_goal([], ⌜∀τ x f g⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧ f ∈ Loops(τ, x) ∧ g ∈ Loops(τ, x) ∧
	PathHomotopic τ f g
⇒	PathHomotopic τ (~⋎P f) (~⋎P g)
⌝);
a(rewrite_tac[path_minus_def, path_homotopic_def, homotopic_def, homotopy_def,
	loops_def, paths_def] THEN REPEAT strip_tac);
a(∃_tac⌜λ(x, t)⦁ H(1. - x, t)⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ℝ_continuity_tac[]);
(* *** Goal "2" *** *)
a(GET_NTH_ASM_T 4 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(GET_NTH_ASM_T 4 bc_thm_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏loop_minus_respects_thm⦎ = save_thm ( "loop_minus_respects_thm", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ
⇒	((λf⦁ FunGrpClass(τ, x) (~⋎P f)) Respects PathHomotopic τ) (Loops(τ, x))
⌝);
a(rewrite_tac[respects_def, fun_grp_class_def] THEN REPEAT strip_tac);
a(ante_tac (list_∀_elim[⌜Loops(τ, x)⌝, ⌜PathHomotopic τ⌝, ⌜~⋎P x'⌝, ⌜~⋎P y⌝] equiv_class_eq_thm));
a(ALL_FC_T asm_rewrite_tac[loops_homotopic_equiv_thm, minus_loop_loop_thm]);
a(STRIP_T rewrite_thm_tac);
a(bc_thm_tac loop_minus_respects_lemma);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

(*
drop_main_goal();
*)

val _ = save_consistency_thm ⌜FunGrpInverse⌝ (
push_consistency_goal ⌜FunGrpInverse⌝;
a(prove_∃_tac THEN REPEAT strip_tac);
a(pair_tac ⌜x' = (τ, x)⌝);
a(cases_tac ⌜τ ∈ Topology ∧ x ∈ Space⋎T τ ∧ p' ∈ Loops (τ, x) / PathHomotopic τ⌝
	THEN asm_rewrite_tac[]);
a(all_fc_tac[loop_minus_respects_thm, loops_homotopic_equiv_thm]);
a(all_fc_tac[induced_fun_∃_thm]);
a(∃_tac⌜g p'⌝ THEN REPEAT strip_tac);
a(ALL_ASM_FC_T rewrite_tac[]);
pop_thm());

val ⦏fun_grp_inverse_def⦎ = get_spec ⌜FunGrpInverse⌝;
val ⦏fun_grp_unit_def⦎ = get_spec ⌜FunGrpUnit⌝;
val ⦏fun_grp_def⦎ = get_spec ⌜FunGrp⌝;

=TEX
%%%%
%%%%

=SML

val ⦏fun_grp_rep_∃_thm⦎ = save_thm ( "fun_grp_rep_∃_thm", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	p ∈ Loops (τ, x) / PathHomotopic τ
⇒	∃f⦁ f ∈ Loops (τ, x) ∧ f ∈ p
⌝);
a(REPEAT strip_tac THEN bc_thm_tac quotient_rep_∃_thm);
a(∃_tac⌜PathHomotopic τ⌝ THEN REPEAT strip_tac);
a(bc_thm_tac loops_homotopic_equiv_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏fun_grp_class_eq_thm⦎ = save_thm ( "fun_grp_class_eq_thm", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧ f ∈ Loops (τ, x) ∧ g ∈ Loops (τ, x)
⇒	(FunGrpClass (τ, x) f = FunGrpClass (τ, x) g ⇔ PathHomotopic τ f g)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN rewrite_tac[fun_grp_class_def]);
a(bc_thm_tac equiv_class_eq_thm THEN REPEAT strip_tac);
a(bc_thm_tac loops_homotopic_equiv_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏fun_grp_times_∈_car_thm⦎ = save_thm ( "fun_grp_times_∈_car_thm", (
set_goal([], ⌜∀τ x p q⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	p ∈ Loops (τ, x) / PathHomotopic τ ∧ q ∈ Loops (τ, x) / PathHomotopic τ
⇒	FunGrpTimes (τ, x) p q ∈ Loops (τ, x) / PathHomotopic τ

⌝);
a(REPEAT strip_tac);
a(all_fc_tac[fun_grp_rep_∃_thm]);
a(ALL_FC_T rewrite_tac [fun_grp_times_def]);
a(rewrite_tac[quotient_set_def]);
a(∃_tac⌜f' +⋎P f⌝ THEN rewrite_tac[fun_grp_class_def]);
a(bc_thm_tac loop_plus_loop_loop_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏fun_grp_unit_∈_car_thm⦎ = save_thm ( "fun_grp_unit_∈_car_thm", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ
⇒	FunGrpUnit (τ, x) ∈ Loops (τ, x) / PathHomotopic τ
⌝);
a(REPEAT strip_tac);
a(rewrite_tac[fun_grp_unit_def, fun_grp_class_def, quotient_set_def]);
a(∃_tac⌜0⋎P x⌝ THEN REPEAT strip_tac);
a(all_fc_tac[path_0_loop_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏fun_grp_inverse_∈_car_thm⦎ = save_thm ( "fun_grp_inverse_∈_car_thm", (
set_goal([], ⌜∀τ x p⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	p ∈ Loops (τ, x) / PathHomotopic τ
⇒	FunGrpInverse (τ, x) p ∈ Loops (τ, x) / PathHomotopic τ

⌝);
a(REPEAT strip_tac);
a(all_fc_tac[fun_grp_rep_∃_thm]);
a(ALL_FC_T rewrite_tac [fun_grp_inverse_def]);
a(rewrite_tac[quotient_set_def]);
a(∃_tac⌜~⋎P f⌝ THEN rewrite_tac[fun_grp_class_def]);
a(bc_thm_tac minus_loop_loop_thm THEN REPEAT strip_tac);
pop_thm()
));


=TEX
%%%%
%%%%
The following utility theorem says that an element of the fundamental group
is equal to the equivalence class of any of its representatives.
=SML

val ⦏fun_grp_eq_rep_thm⦎ = save_thm ( "fun_grp_eq_rep_thm", (
set_goal([], ⌜∀τ x p f⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ ∧
	p ∈ Loops (τ, x) / PathHomotopic τ ∧ f ∈ p
⇒	p = FunGrpClass(τ, x) f
⌝);
a(rewrite_tac[fun_grp_class_def, quotient_set_def] THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[equiv_class_def]));
a(all_fc_tac[loops_homotopic_equiv_thm]);
a(ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[equiv_class_eq_thm]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏fun_grp_group_thm⦎ = save_thm ( "fun_grp_group_thm", (
set_goal([], ⌜∀τ x⦁
	τ ∈ Topology ∧ x ∈ Space⋎T τ
⇒	FunGrp(τ, x) ∈ Group
⌝);
a(REPEAT strip_tac THEN rewrite_tac[group_def, group_ops_def, fun_grp_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[fun_grp_times_∈_car_thm]);
(* *** Goal "2" *** *)
a(rename_tac[(⌜x'⌝, "p"), (⌜y⌝, "q"), (⌜z⌝, "r")]
	THEN lemma_tac⌜FunGrpTimes (τ, x) p q  ∈ Loops (τ, x) / PathHomotopic τ ∧
	(FunGrpTimes (τ, x) q r) ∈ Loops (τ, x) / PathHomotopic τ⌝
	THEN1 ALL_FC_T rewrite_tac[fun_grp_times_∈_car_thm]);
a(all_fc_tac[fun_grp_rep_∃_thm]);
a(rename_tac[(⌜f⌝, "gh"), (⌜f'⌝, "fg"), (⌜f''⌝, "h"), (⌜f'''⌝, "g"), (⌜f''''⌝, "f")]
	THEN ALL_FC_T rewrite_tac [fun_grp_times_def]);
a(lemma_tac ⌜fg +⋎P h  ∈ Loops (τ, x) ∧ f +⋎P gh ∈ Loops (τ, x)⌝
	THEN1 ALL_FC_T rewrite_tac[loop_plus_loop_loop_thm]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[fun_grp_class_eq_thm]);
a(DROP_ASM_T ⌜fg ∈ FunGrpTimes (τ, x) p q⌝ ante_tac);
a(DROP_ASM_T ⌜gh ∈ FunGrpTimes (τ, x) q r⌝ ante_tac);
a(ALL_FC_T rewrite_tac[fun_grp_times_def]);
a(rewrite_tac[fun_grp_class_def, equiv_class_def] THEN REPEAT strip_tac);
a(bc_thm_tac loops_homotopic_trans_thm);
a(∃_tac⌜(f +⋎P g) +⋎P h⌝ THEN ∃_tac ⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(REPEAT (bc_thm_tac loop_plus_loop_loop_thm THEN REPEAT strip_tac));
(* *** Goal "2.2" *** *)
a(bc_thm_tac loop_plus_respects_lemma1 THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac
	THEN1 (bc_thm_tac loop_plus_loop_loop_thm THEN REPEAT strip_tac));
a(bc_thm_tac loops_homotopic_sym_thm THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(all_fc_tac[loop_plus_loop_loop_thm]);
(* *** Goal "2.3" *** *)
a(bc_thm_tac loops_homotopic_trans_thm);
a(∃_tac⌜f +⋎P (g +⋎P h)⌝ THEN ∃_tac ⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.3.1" *** *)
a(REPEAT (bc_thm_tac loop_plus_loop_loop_thm THEN REPEAT strip_tac));
(* *** Goal "2.3.2" *** *)
a(REPEAT (bc_thm_tac loop_plus_loop_loop_thm THEN REPEAT strip_tac));
(* *** Goal "2.3.3" *** *)
a(bc_thm_tac loop_plus_assoc_thm THEN ∃_tac ⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.3.4" *** *)
a(bc_thm_tac loop_plus_respects_lemma2 THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac
	THEN1 (bc_thm_tac loop_plus_loop_loop_thm THEN REPEAT strip_tac));
(* *** Goal "3" *** *)
a(all_fc_tac[fun_grp_unit_∈_car_thm]);
(* *** Goal "4" *** *)
a(rename_tac[(⌜x'⌝, "p")] THEN all_fc_tac[fun_grp_unit_∈_car_thm]);
a(all_fc_tac[fun_grp_rep_∃_thm]);
a(rename_tac[(⌜f⌝, "z"), (⌜f'⌝, "f")]
	THEN ALL_FC_T rewrite_tac [fun_grp_times_def]);
a(ALL_FC_T rewrite_tac[fun_grp_eq_rep_thm]);
a(lemma_tac⌜f +⋎P z ∈ Loops(τ, x)⌝ THEN1 all_fc_tac[loop_plus_loop_loop_thm]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[fun_grp_class_eq_thm]);
a(all_fc_tac [path_0_loop_thm]);
a(bc_thm_tac loops_homotopic_trans_thm THEN ∃_tac⌜f +⋎P 0⋎P x⌝ THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "4.1" *** *)
a(all_fc_tac[loop_plus_loop_loop_thm]);
(* *** Goal "4.2" *** *)
a(bc_thm_tac loop_plus_respects_lemma2 THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(DROP_ASM_T ⌜z ∈ FunGrpUnit (τ, x)⌝ ante_tac THEN
	rewrite_tac[fun_grp_unit_def, fun_grp_class_def, equiv_class_def]);
a(REPEAT strip_tac THEN bc_thm_tac loops_homotopic_sym_thm);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "4.3" *** *)
a(bc_thm_tac loop_plus_0_thm THEN REPEAT strip_tac);
(* *** Goal "5" *** *)
a(rename_tac[(⌜x'⌝, "p")] THEN all_fc_tac[fun_grp_unit_∈_car_thm]);
a(all_fc_tac[fun_grp_rep_∃_thm]);
a(rename_tac[(⌜f⌝, "z"), (⌜f'⌝, "f")]
	THEN ALL_FC_T rewrite_tac [fun_grp_times_def]);
a(ALL_FC_T rewrite_tac[fun_grp_eq_rep_thm]);
a(lemma_tac⌜z +⋎P f ∈ Loops(τ, x)⌝ THEN1 all_fc_tac[loop_plus_loop_loop_thm]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[fun_grp_class_eq_thm]);
a(all_fc_tac [path_0_loop_thm]);
a(bc_thm_tac loops_homotopic_trans_thm THEN ∃_tac⌜0⋎P x +⋎P f⌝ THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "5.1" *** *)
a(all_fc_tac[loop_plus_loop_loop_thm]);
(* *** Goal "5.2" *** *)
a(bc_thm_tac loop_plus_respects_lemma1 THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(DROP_ASM_T ⌜z ∈ FunGrpUnit (τ, x)⌝ ante_tac THEN
	rewrite_tac[fun_grp_unit_def, fun_grp_class_def, equiv_class_def]);
a(REPEAT strip_tac THEN bc_thm_tac loops_homotopic_sym_thm);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "5.3" *** *)
a(bc_thm_tac loop_0_plus_thm THEN REPEAT strip_tac);
(* *** Goal "6" *** *)
a(all_fc_tac[fun_grp_inverse_∈_car_thm]);
(* *** Goal "7" *** *)
a(rename_tac[(⌜x'⌝, "p")] THEN all_fc_tac[fun_grp_inverse_∈_car_thm]);
a(all_fc_tac[fun_grp_rep_∃_thm]);
a(rename_tac[(⌜f⌝, "fi"), (⌜f'⌝, "f")]
	THEN ALL_FC_T rewrite_tac [fun_grp_times_def]);
a(rewrite_tac[fun_grp_unit_def]);
a(all_fc_tac [path_0_loop_thm]);
a(lemma_tac ⌜f +⋎P fi ∈ Loops(τ, x)⌝ THEN1 all_fc_tac[loop_plus_loop_loop_thm]);
a(lemma_tac ⌜~⋎P f ∈ Loops(τ, x)⌝ THEN1 all_fc_tac[minus_loop_loop_thm]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[fun_grp_class_eq_thm]);
a(bc_thm_tac loops_homotopic_trans_thm THEN ∃_tac⌜f +⋎P ~⋎P f⌝ THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac
	THEN1 all_fc_tac[loop_plus_loop_loop_thm]);
(* *** Goal "7.1" *** *)
a(DROP_ASM_T ⌜fi ∈ FunGrpInverse (τ, x) p⌝ ante_tac);
a(ALL_FC_T rewrite_tac[fun_grp_inverse_def]);
a(rewrite_tac[fun_grp_class_def, equiv_class_def] THEN REPEAT strip_tac);
a(bc_thm_tac loop_plus_respects_lemma2 THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(bc_thm_tac loops_homotopic_sym_thm THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "7.2" *** *)
a(bc_thm_tac loop_plus_minus_thm THEN REPEAT strip_tac);
(* *** Goal "8" *** *)
a(rename_tac[(⌜x'⌝, "p")] THEN all_fc_tac[fun_grp_inverse_∈_car_thm]);
a(all_fc_tac[fun_grp_rep_∃_thm]);
a(rename_tac[(⌜f⌝, "fi"), (⌜f'⌝, "f")]
	THEN ALL_FC_T rewrite_tac [fun_grp_times_def]);
a(rewrite_tac[fun_grp_unit_def]);
a(all_fc_tac [path_0_loop_thm]);
a(lemma_tac ⌜fi +⋎P f ∈ Loops(τ, x)⌝ THEN1 all_fc_tac[loop_plus_loop_loop_thm]);
a(lemma_tac ⌜~⋎P f ∈ Loops(τ, x)⌝ THEN1 all_fc_tac[minus_loop_loop_thm]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[fun_grp_class_eq_thm]);
a(bc_thm_tac loops_homotopic_trans_thm THEN ∃_tac⌜~⋎P f +⋎P f⌝ THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac
	THEN1 all_fc_tac[loop_plus_loop_loop_thm]);
(* *** Goal "8.1" *** *)
a(DROP_ASM_T ⌜fi ∈ FunGrpInverse (τ, x) p⌝ ante_tac);
a(ALL_FC_T rewrite_tac[fun_grp_inverse_def]);
a(rewrite_tac[fun_grp_class_def, equiv_class_def] THEN REPEAT strip_tac);
a(bc_thm_tac loop_plus_respects_lemma1 THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(bc_thm_tac loops_homotopic_sym_thm THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "8.2" *** *)
a(bc_thm_tac loop_minus_plus_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏loop_comp_continuous_loop_thm⦎ = save_thm ( "loop_comp_continuous_loop_thm", (
set_goal([], ⌜∀σ τ x f g⦁
	σ ∈ Topology ∧
	τ ∈ Topology ∧
	f ∈ Loops(σ, x) ∧
	g ∈ (σ, τ) Continuous
⇒ 	(λx⦁g(f x)) ∈ Loops(τ, g x)
⌝);
a(rewrite_tac[loops_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[path_comp_continuous_path_thm]);
(* *** Goal "2" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "3" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏iota_i_continuous_thm⦎ = save_thm ( "iota_i_continuous_thm", (
set_goal([], ⌜
	IotaI ∈ (O⋎R, O⋎R) Continuous
⌝);
a(rewrite_tac[iota_i_def]);
a(ho_bc_thm_tac cond_continuous_ℝ_thm THEN rewrite_tac[] THEN
	REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a(ho_bc_thm_tac cond_continuous_ℝ_thm THEN rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML

val ⦏comp_iota_i_path_thm⦎ = save_thm ( "comp_iota_i_path_thm", (
set_goal([], ⌜∀σ f⦁
	σ ∈ Topology ∧
	f ∈ (O⋎R, σ) Continuous
⇒	(λx⦁ f(IotaI x)) ∈ Paths σ
⌝);
a(REPEAT strip_tac THEN rewrite_tac[paths_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ℝ_continuity_tac[iota_i_continuous_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[iota_i_def]);
(* *** Goal "3" *** *)
a(lemma_tac⌜¬(x ≤ 0.) ∧ (x = 1. ∨ ¬x ≤ 1.)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN asm_rewrite_tac[iota_i_def]);
pop_thm()
));

=TEX
\subsection{Covering Projections are Fibrations}

=TEX
%%%%
%%%%
We will prove that covering projections are fibrations, i.e., they have the following homotopy lifting property:
let $p : S → T$ be a covering projection,
let $h : R  \times [0, 1] → S$ be any continuous mapping
and let $f : R → T$ be such that $p(f x) = h(x, 0)$
for every $x \in R$, then there is a continuous $L: R \times [0, 1] → T$
such that $L(x, 0) = f(x)$ and $p(L(x, s)) = h(x, s)$ for any $x \in R$ and $s \in [0, 1]$.
This is done in a sequence of lemmas.


For historical reasons, we revert to working without the proof context associated with
the theory {\it topology\_ℝ}.
=SML
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];


=TEX
%%%%
%%%%

We first look at the case where $h$ and $f$ are restricted to an open subset $N$ of $R$ such that  $h(N \times [a, b])$ is contained in an evenly covered open subset $C$ of $T$ and $f(N)$ lies in a single sheet $S$ over $C$.
=SML

val ⦏covering_projection_fibration_lemma1⦎ = (* not saved *) snd ( "covering_projection_fibration_lemma1", (
set_goal([], ⌜∀ρ; σ; τ;
	p : 'b → 'c;
	f : 'a → 'b;
	h : 'a × ℝ → 'c;
	N : 'a SET;
	S : 'b SET;
	a b : ℝ;
	C : 'c SET;
	U : 'b SET SET ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	h ∈ ((N × ClosedInterval a b) ◁⋎T ρ ×⋎T O⋎R, τ) Continuous
∧	N ∈ ρ
∧	(∀x⦁ x ∈ N ⇒ f x ∈ S)
∧	(∀x⦁ x ∈ N ⇒ h(x, a) = p(f x))
∧	S ∈ U
∧	a < b
∧	(∀x t⦁ x ∈ N ∧ t ∈ ClosedInterval a b ⇒ h (x, t) ∈ C)
∧	C ∈ τ
∧	U ⊆ σ
∧	(∀ A⦁ A ∈ U ⇒ p ∈ (A ◁⋎T σ, C ◁⋎T τ) Homeomorphism)
⇒	∃L : 'a × ℝ → 'b⦁
	L ∈ ((N × ClosedInterval a b) ◁⋎T (ρ ×⋎T O⋎R), σ) Continuous
∧	(∀x⦁	x ∈ N
	⇒	L(x, a) = f x)
∧	(∀x s⦁	x ∈ N
	∧	s ∈ ClosedInterval a b
	⇒	L(x, s) ∈ S)
∧	(∀x s⦁	x ∈ N
	∧	s ∈ ClosedInterval a b
	⇒	p(L(x, s)) = h(x, s))
⌝);
a(REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T[1] all_fc_tac);
a(POP_ASM_T (ante_tac o rewrite_rule[homeomorphism_def]));
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a u s⦁ a ∈ u ∧ u ⊆ s ⇒ a ∈ s⌝]); 
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm2]
	THEN REPEAT strip_tac);
a(∃_tac⌜λxt⦁g(h xt)⌝ THEN rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac comp_continuous_thm);
a(asm_tac open_ℝ_topology_thm);
a(∃_tac⌜C ◁⋎T τ⌝ THEN
	ALL_FC_T asm_rewrite_tac[
subspace_topology_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(all_fc_tac[open_⊆_space_t_thm]);
a(lemma_tac⌜(N × ClosedInterval a b) ⊆ Space⋎T (ρ ×⋎T O⋎R)⌝
	THEN1 (ALL_FC_T rewrite_tac[product_topology_space_t_thm]
		THEN rewrite_tac[space_t_ℝ_thm]
		THEN POP_ASM_T ante_tac
		THEN PC_T1 "sets_ext1" prove_tac[×_def]));
a(bc_thm_tac subspace_range_continuous_bc_thm
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN1 (bc_tac [product_topology_thm, subspace_topology_thm]
		THEN REPEAT strip_tac));
a(lemma_tac⌜ρ ×⋎T O⋎R ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(∀_tac THEN ALL_FC_T rewrite_tac[subspace_topology_space_t_thm1,
	product_topology_space_t_thm]);
a(rewrite_tac[×_def]);
a(pair_tac⌜x = (v, s)⌝ THEN rewrite_tac[]);
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a(bc_thm_tac subspace_range_continuous_thm);
a(∃_tac⌜S⌝ THEN REPEAT strip_tac);
a(bc_thm_tac subspace_topology_thm THEN REPEAT strip_tac);
(* *** Goal "1.3" *** *)
a(bc_tac[product_topology_thm, subspace_topology_thm] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [14] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [4, 14] (ALL_FC_T rewrite_tac));
(* *** Goal "3" *** *)
a(LIST_DROP_NTH_ASM_T [11] all_fc_tac);
a(lemma_tac⌜h(x, s) ∈ Space⋎T (C ◁⋎T τ)⌝
	THEN1 ALL_FC_T asm_rewrite_tac[subspace_topology_space_t_thm2]);
a(ALL_FC_T (MAP_EVERY ante_tac) [continuous_∈_space_t_thm]);
a(ALL_FC_T asm_rewrite_tac[subspace_topology_space_t_thm2]);
(* *** Goal "4" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

We now do the case where $h$ and $f$ are still restricted to an open subset $N$ of $R$ such that $h(N \times [a, b])$ is contained in an evenly covered open subset $C$ of $T$ but $f(N)$ may be spread over many sheets over $C$.


=SML

val ⦏covering_projection_fibration_lemma2⦎ = (* not saved *) snd ( "covering_projection_fibration_lemma2", (
set_goal([], ⌜∀ρ; σ; τ;
	p : 'b → 'c;
	f : 'a → 'b;
	h : 'a × ℝ → 'c;
	N : 'a SET;
	a b : ℝ;
	C : 'c SET;
	U : 'b SET SET ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	f ∈ (N ◁⋎T ρ, σ) Continuous
∧	h ∈ ((N × ClosedInterval a b) ◁⋎T ρ ×⋎T O⋎R, τ) Continuous
∧	N ∈ ρ
∧	a < b
∧	(∀x⦁ x ∈ N ⇒ h(x, a) = p(f x))
∧	(∀x s⦁ x ∈ N ∧ s ∈ ClosedInterval a b ⇒ h (x, s) ∈ C)
∧	C ∈ τ
∧	U ⊆ σ
∧	(∀x⦁ x ∈ Space⋎T σ ∧ p x ∈ C ⇒ ∃A⦁ x ∈ A ∧ A ∈ U)
∧	(∀ A B⦁ A ∈ U ∧ B ∈ U ∧ ¬ A ∩ B = {} ⇒ A = B)
∧	(∀ A⦁ A ∈ U ⇒ p ∈ (A ◁⋎T σ, C ◁⋎T τ) Homeomorphism)
⇒	∃L : 'a × ℝ → 'b⦁
	L ∈ ((N × ClosedInterval a b) ◁⋎T (ρ ×⋎T O⋎R), σ) Continuous
∧	(∀x⦁	x ∈ N
	⇒	L(x, a) = f x)
∧	(∀x s⦁	x ∈ N
	∧	s ∈ ClosedInterval a b
	⇒	p(L(x, s)) = h(x, s))
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃W⦁∀v: 'a; r : ℝ⦁
	W (v, r) = {w | w ∈ N ∧ ∃A⦁ f v ∈ A ∧ f w ∈ A ∧ A ∈ U}⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∃V⦁∀w r⦁
	V (w, r) = (W (w, r) × ClosedInterval a b)⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∃S⦁∀w : 'a; r : ℝ⦁
	S (w, r) = {y | ∃A⦁ y ∈ A ∧ f w ∈ A ∧ A ∈ U}⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∃G⦁∀v r⦁ v ∈ N ∧ r ∈ ClosedInterval a b ⇒
	G (v, r) ∈ (V (v, r) ◁⋎T (ρ ×⋎T O⋎R), σ) Continuous
∧	(∀w⦁	w ∈ W (v, r)
	⇒	G(v, r)(w, a) = f w)
∧	(∀w s⦁	w ∈ W (v, r)
	∧	s ∈ ClosedInterval a b
	⇒	G (v, r) (w, s) ∈ S (v, r))
∧	(∀w s⦁	w ∈ W (v, r)
	∧	s ∈ ClosedInterval a b
	⇒	p(G (v, r) (w, s)) = h(w, s))⌝);
(* *** Goal "1" *** *)
a(lemma_tac⌜∃H⦁∀vr⦁ Fst vr ∈ N ∧ Snd vr ∈ ClosedInterval a b ⇒
	H vr ∈ (V vr ◁⋎T (ρ ×⋎T O⋎R), σ) Continuous
∧	(∀w⦁	w ∈ W vr
	⇒	H vr (w, a) = f w)
∧	(∀w s⦁	w ∈ W vr
	∧	s ∈ ClosedInterval a b
	⇒	H vr (w, s) ∈ S vr)
∧	(∀w s⦁	w ∈ W vr
	∧	s ∈ ClosedInterval a b
	⇒	p(H vr (w, s)) = h(w, s))⌝
	THEN1 (prove_∃_tac THEN strip_tac));
(* *** Goal "1.1" *** *)
a(pair_tac⌜vr' = (v, r)⌝);
a(GET_NTH_ASM_T 2 rewrite_thm_tac);
a(cases_tac⌜¬v ∈ N⌝ THEN1 asm_rewrite_tac[]);
a(cases_tac⌜¬r ∈ ClosedInterval a b⌝ THEN1 asm_rewrite_tac[]);
a(LIST_GET_NTH_ASM_T [1, 2] rewrite_tac);
a(LEMMA_T⌜h(v, a) ∈ C⌝ ante_tac
	THEN1 (DROP_NTH_ASM_T 11 bc_thm_tac THEN asm_rewrite_tac[closed_interval_def, ℝ_≤_def]));
a(LIST_GET_NTH_ASM_T [12] (ALL_FC_T rewrite_tac) THEN strip_tac);
a(lemma_tac⌜f v ∈ Space⋎T σ⌝
	THEN1 (bc_thm_tac continuous_∈_space_t_thm
		THEN ∃_tac⌜N ◁⋎T ρ⌝
		THEN ALL_FC_T asm_rewrite_tac[∈_space_t_thm, subspace_topology_space_t_thm2]));
a(LIST_GET_NTH_ASM_T [10] all_fc_tac);
a(DROP_NTH_ASM_T 3 discard_tac);
a(bc_thm_tac covering_projection_fibration_lemma1);
a(MAP_EVERY ∃_tac[⌜C⌝, ⌜U⌝, ⌜τ⌝]);
a(LIST_DROP_NTH_ASM_T [6, 7, 8] asm_rewrite_tac THEN REPEAT strip_tac);
(* *** Goal "1.1.1" *** *)
a(LEMMA_T ⌜
	({w|w ∈ N ∧ (∃ A⦁ f v ∈ A ∧ f w ∈ A ∧ A ∈ U)} × ClosedInterval a b)
		◁⋎T ρ ×⋎T O⋎R =
	({w|w ∈ N ∧ (∃ A⦁ f v ∈ A ∧ f w ∈ A ∧ A ∈ U)} × ClosedInterval a b)
		◁⋎T (N × ClosedInterval a b) ◁⋎T ρ ×⋎T O⋎R⌝
	rewrite_thm_tac
	THEN1 (conv_tac eq_sym_conv THEN bc_thm_tac ⊆_subspace_topology_thm
		THEN1 PC_T1 "sets_ext1" prove_tac[×_def]));
a(bc_thm_tac subspace_domain_continuous_thm THEN REPEAT strip_tac);
a(bc_tac[product_topology_thm, subspace_topology_thm] THEN REPEAT strip_tac);
a(rewrite_tac[open_ℝ_topology_thm]);
(* *** Goal "1.1.2" *** *)
a(DROP_NTH_ASM_T 10 discard_tac);
a(LIST_GET_NTH_ASM_T [9] (PC_T1 "sets_ext1" all_fc_tac));
a(all_fc_tac [continuous_open_thm]);
a(POP_ASM_T ante_tac THEN ALL_FC_T rewrite_tac[subspace_topology_space_t_thm2]);
a(rewrite_tac[subspace_topology_def] THEN strip_tac);
a(lemma_tac⌜B ∩ N ∈ ρ⌝ THEN1 all_fc_tac[∩_open_thm]); 
a(LEMMA_T ⌜∀z⦁ (∃ A⦁ f v ∈ A ∧ z ∈ A ∧ A ∈ U) ⇔ z ∈ A⌝ asm_rewrite_thm_tac);
a(REPEAT strip_tac);
(* *** Goal "1.1.2.1" *** *)
a(LEMMA_T ⌜A = A'⌝ asm_rewrite_thm_tac);
a(DROP_NTH_ASM_T 14 bc_thm_tac THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3, 9] (MAP_EVERY ante_tac));
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.1.2.2" *** *)
a(∃_tac⌜A⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1.3" *** *)
a(∃_tac⌜A'⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1.4" *** *)
a(DROP_NTH_ASM_T 16 bc_thm_tac THEN strip_tac);
(* *** Goal "1.1.5" *** *)
a(LEMMA_T⌜{y|∃ A⦁ y ∈ A ∧ f v ∈ A ∧ A ∈ U} = A⌝ asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1.1.5.1" *** *)
a(LEMMA_T⌜A = A'⌝ asm_rewrite_thm_tac);
a(DROP_NTH_ASM_T 10 bc_thm_tac THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2, 5] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.1.5.2" *** *)
a(∃_tac⌜A⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1.6" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜H⌝ THEN REPEAT ∀_tac THEN ⇒_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜λ(v, r)⦁ G (v, r) (v, r)⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac compatible_family_continuous_thm1);
a(∃_tac⌜V⌝ THEN POP_ASM_T ante_tac
	THEN LIST_DROP_NTH_ASM_T [1, 2, 3] rewrite_tac);
a(rewrite_tac[×_def] THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(bc_thm_tac product_topology_thm THEN asm_rewrite_tac[open_ℝ_topology_thm]);
(* *** Goal "2.1.2" *** *)
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.3" *** *)
a(rewrite_tac[taut_rule⌜∀p q⦁p ∧ p ∧ q ⇔ p ∧ q⌝]);
a(GET_NTH_ASM_T 6 bc_thm_tac);
a(LEMMA_T⌜f v ∈ Space⋎T σ⌝ rewrite_thm_tac
	THEN1 (bc_thm_tac continuous_∈_space_t_thm
		THEN ∃_tac⌜N ◁⋎T ρ⌝
		THEN ALL_FC_T asm_rewrite_tac[∈_space_t_thm, subspace_topology_space_t_thm2]));
a(LEMMA_T⌜h(v, a) ∈ C⌝ ante_tac
	THEN1 (DROP_NTH_ASM_T 9 bc_thm_tac THEN asm_rewrite_tac[closed_interval_def, ℝ_≤_def]));
a(LIST_DROP_NTH_ASM_T [10] (ALL_FC_T rewrite_tac));
(* *** Goal "2.1.4" *** *)
a(LEMMA_T⌜h(v, a) ∈ C⌝ ante_tac
	THEN1 (DROP_NTH_ASM_T 9 bc_thm_tac THEN asm_rewrite_tac[closed_interval_def, ℝ_≤_def]));
a(LIST_GET_NTH_ASM_T [10] (ALL_FC_T rewrite_tac) THEN strip_tac);
a(lemma_tac⌜f v ∈ Space⋎T σ⌝
	THEN1 (bc_thm_tac continuous_∈_space_t_thm
		THEN ∃_tac⌜N ◁⋎T ρ⌝
		THEN ALL_FC_T asm_rewrite_tac[∈_space_t_thm, subspace_topology_space_t_thm2]));
a(LIST_GET_NTH_ASM_T [8] all_fc_tac);
a(rewrite_tac[subspace_topology_def]);
a(∃_tac⌜{v|v ∈ N ∧ f v ∈ A} × Universe⌝ THEN rewrite_tac[×_def] THEN REPEAT strip_tac);
(* *** Goal "2.1.4.1" *** *)
a(LIST_GET_NTH_ASM_T [11] (PC_T1 "sets_ext1" all_fc_tac));
a(all_fc_tac [continuous_open_thm]);
a(POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm2]);
a(rewrite_tac[subspace_topology_def] THEN strip_tac);
a(POP_ASM_T (strip_asm_tac o eq_sym_rule));
a(LEMMA_T⌜B ∩ N ∈ ρ⌝ ante_tac THEN1 all_fc_tac[∩_open_thm]);
a(asm_rewrite_tac[product_topology_def] THEN REPEAT strip_tac);
a(∃_tac⌜{x|x ∈ N ∧ f x ∈ A}⌝ THEN ∃_tac⌜Universe⌝);
a(asm_rewrite_tac[empty_universe_open_closed_thm]);
a(PC_T1 "sets_ext1" prove_tac[×_def]);
(* *** Goal "2.1.4.2" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.1.4.2.1" *** *)
a(lemma_tac⌜f v ∈ A ∧ f v ∈ A' ⇒ ¬A' ∩ A = {}⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(LIST_DROP_NTH_ASM_T [15] all_fc_tac THEN all_var_elim_asm_tac);
(* *** Goal "2.1.4.2.2" *** *)
a(∃_tac⌜A⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1.5" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
(* *** Goal "2.1.6" *** *)
a(GET_NTH_ASM_T 8 (strip_asm_tac o list_∀_elim[⌜v⌝, ⌜r⌝]));
a(DROP_NTH_ASM_T 12 (strip_asm_tac o list_∀_elim[⌜w⌝, ⌜s⌝]));
a(LIST_DROP_NTH_ASM_T [3, 4, 7, 8] discard_tac);
a(lemma_tac⌜p(G(v, r)(w, s)) = h(w, s)⌝
	THEN1 (DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac
		THEN ∃_tac⌜A⌝ THEN REPEAT strip_tac));
a(lemma_tac⌜p(G(w, s)(w, s)) = h(w, s)⌝
	THEN1 (DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac
		THEN ∃_tac⌜A⌝ THEN REPEAT strip_tac));
a(LIST_DROP_NTH_ASM_T [3, 5] discard_tac);
a(DROP_NTH_ASM_T 4 (strip_asm_tac o list_∀_elim[⌜w⌝, ⌜s⌝])
	THEN1 all_asm_fc_tac[]);
a(DROP_NTH_ASM_T 6 (strip_asm_tac o list_∀_elim[⌜w⌝, ⌜s⌝])
	THEN1 all_asm_fc_tac[]);
a(lemma_tac⌜A' = A⌝);
(* *** Goal "2.1.6.1" *** *)
a(DROP_NTH_ASM_T 17 bc_thm_tac THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [5, 12] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.6.2" *** *)
a(all_var_elim_asm_tac);
a(lemma_tac⌜A'' = A⌝);
(* *** Goal "2.1.6.2.1" *** *)
a(DROP_NTH_ASM_T 15 bc_thm_tac THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2, 9] (MAP_EVERY ante_tac)
	THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.6.2.2" *** *)
a(all_var_elim_asm_tac);
a(LIST_DROP_NTH_ASM_T [12] all_fc_tac);
a(POP_ASM_T (ante_tac o rewrite_rule[homeomorphism_def]));
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a u s⦁ a ∈ u ∧ u ⊆ s ⇒ a ∈ s⌝]); 
a(ALL_FC_T rewrite_tac[subspace_topology_space_t_thm2]
	THEN REPEAT strip_tac);
a(LEMMA_T ⌜g(p(G(w, s)(w, s))) = g(p(G(v, r)(w, s)))⌝ ante_tac
	THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [2] (ALL_FC_T rewrite_tac));
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 2 (ante_tac o list_∀_elim[⌜x⌝, ⌜a⌝]));
a(asm_rewrite_tac[closed_interval_def, ℝ_≤_def] THEN strip_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
a(rewrite_tac[taut_rule⌜∀p q⦁p ∧ p ∧ q ⇔ p ∧ q⌝]);
a(GET_NTH_ASM_T 10 bc_thm_tac);
a(LEMMA_T⌜f x ∈ Space⋎T σ⌝ rewrite_thm_tac
	THEN1 (bc_thm_tac continuous_∈_space_t_thm
		THEN ∃_tac⌜N ◁⋎T ρ⌝
		THEN ALL_FC_T asm_rewrite_tac[∈_space_t_thm, subspace_topology_space_t_thm2]));
a(LEMMA_T ⌜p(f x) = h(x, a)⌝ rewrite_thm_tac
	THEN1 LIST_DROP_NTH_ASM_T [14] (ALL_FC_T rewrite_tac));
a(DROP_NTH_ASM_T 13 bc_thm_tac);
a(asm_rewrite_tac[closed_interval_def, ℝ_≤_def]);
(* *** Goal "2.3" *** *)
a(DROP_NTH_ASM_T 3 (ante_tac o list_∀_elim[⌜x⌝, ⌜s⌝]));
a(LIST_DROP_NTH_ASM_T[3, 4, 5] rewrite_tac
	THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN asm_rewrite_tac[]);
a(rewrite_tac[taut_rule⌜∀p q⦁p ∧ p ∧ q ⇔ p ∧ q⌝]);
a(LEMMA_T⌜h(x, a) ∈ C⌝ ante_tac
	THEN1 (DROP_NTH_ASM_T 11 bc_thm_tac THEN asm_rewrite_tac[closed_interval_def, ℝ_≤_def]));
a(LIST_DROP_NTH_ASM_T [12] (ALL_FC_T rewrite_tac)
	THEN strip_tac);
a(lemma_tac⌜f x ∈ Space⋎T σ⌝
	THEN1 (bc_thm_tac continuous_∈_space_t_thm
		THEN ∃_tac⌜N ◁⋎T ρ⌝
		THEN ALL_FC_T asm_rewrite_tac[∈_space_t_thm, subspace_topology_space_t_thm2]));
a(DROP_NTH_ASM_T 10 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
Next comes the case where $h$ and $f$ are restricted to an open subset $N$ of $R$ such that $[0, 1]$
can be divided into finitely many subintervals
$[t_i, t_{i+1}]$ such that each 
$h(N \times [t_i, t_{i+1}])$ is contained in an evenly covered open subset $C$ of $T$.

%%%%
%%%%

=SML

val ⦏covering_projection_fibration_lemma3⦎ = (* not saved *) snd ( "covering_projection_fibration_lemma3", (
set_goal([], ⌜∀ρ; σ; τ;
	p : 'b → 'c;
	f : 'a → 'b;
	h : 'a × ℝ → 'c;
	N : 'a SET;
	t : ℕ → ℝ;
	n : ℕ ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	f ∈ (N ◁⋎T ρ, σ) Continuous
∧	h ∈ ((N × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R, τ) Continuous
∧	N ∈ ρ
∧	(∀x⦁ x ∈ N ⇒ h(x, 0.) = p(f x))
∧	t 0 = 0. ∧ t n = 1.
∧	(∀i j⦁ i < j ⇒ t i < t j)
∧	(∀i⦁ i < n ⇒ ∃C⦁
			(∀x s⦁ x ∈ N ∧ s ∈ ClosedInterval (t i) (t(i+1)) ⇒ h(x, s) ∈ C)
		∧	C ∈ τ
		∧	∃U⦁
			U ⊆ σ
		∧	(∀x⦁ x ∈ Space⋎T σ ∧ p x ∈ C ⇒ ∃A⦁ x ∈ A ∧ A ∈ U)
		∧	(∀ A B⦁ A ∈ U ∧ B ∈ U ∧ ¬ A ∩ B = {} ⇒ A = B)
		∧	(∀ A⦁ A ∈ U ⇒ p ∈ (A ◁⋎T σ, C ◁⋎T τ) Homeomorphism))
⇒	∃L : 'a × ℝ → 'b⦁
	L ∈ ((N × ClosedInterval 0. 1.) ◁⋎T (ρ ×⋎T O⋎R), σ) Continuous
∧	(∀x⦁	x ∈ N
	⇒	L(x, 0.) = f x)
∧	(∀x s⦁	x ∈ N
	∧	s ∈ ClosedInterval 0. 1.
	⇒	p(L(x, s)) = h(x, s))
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀k⦁k < n ⇒
	∃L : 'a × ℝ → 'b⦁
	L ∈ ((N × ClosedInterval 0. (t(k+1))) ◁⋎T (ρ ×⋎T O⋎R), σ) Continuous
∧	(∀x⦁	x ∈ N
	⇒	L(x, 0.) = f x)
∧	(∀x s⦁	x ∈ N
	∧	s ∈ ClosedInterval 0. (t(k+1))
	⇒	p(L(x, s)) = h(x, s))⌝);
a(strip_tac THEN induction_tac⌜k:ℕ⌝ THEN REPEAT strip_tac
	THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]
	THEN rewrite_tac[plus_assoc_thm]);
(* *** Goal "1.1" *** *)
a(bc_thm_tac covering_projection_fibration_lemma2);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(GET_NTH_ASM_T 8 (strip_asm_tac o list_∀_elim [⌜0⌝, ⌜1⌝]));
a(LIST_DROP_NTH_ASM_T [1, 7] (MAP_EVERY ante_tac)
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(MAP_EVERY ∃_tac[⌜U⌝, ⌜C⌝, ⌜τ⌝] THEN asm_rewrite_tac[]);
a(cases_tac⌜n = 1⌝ THEN1 (all_var_elim_asm_tac1 THEN asm_rewrite_tac[]));
a(lemma_tac⌜1 < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(GET_NTH_ASM_T 11 (strip_asm_tac o list_∀_elim [⌜1⌝, ⌜n⌝]));
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a(LEMMA_T ⌜
	(N × ClosedInterval 0. (t 1)) ◁⋎T ρ ×⋎T O⋎R =
	(N × ClosedInterval 0. (t 1))
		◁⋎T (N × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R⌝
	rewrite_thm_tac
	THEN1 (conv_tac eq_sym_conv THEN bc_thm_tac ⊆_subspace_topology_thm
		THEN PC_T1 "sets_ext1" asm_rewrite_tac[closed_interval_def, ×_def]
		THEN REPEAT strip_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(bc_thm_tac subspace_domain_continuous_thm THEN REPEAT strip_tac);
a(bc_tac[subspace_topology_thm, product_topology_thm] THEN REPEAT strip_tac);
a(rewrite_tac[open_ℝ_topology_thm]);
(* *** Goal "1.2" *** *)
a(lemma_tac ⌜∃M⦁
	M ∈ ((N × ClosedInterval (t(k+1)) (t(k+2))) ◁⋎T ρ ×⋎T O⋎R, σ) Continuous 
∧	(∀ x⦁ x ∈ N ⇒ M(x, t(k+1)) = (λx⦁ L(x, t(k+1))) x)
∧	(∀ x s⦁ x ∈ N ∧ s ∈ ClosedInterval (t(k+1)) (t(k+2))
	⇒	p (M(x, s)) = h (x, s))⌝);
(* *** Goal "1.2.1" *** *)
a(bc_thm_tac covering_projection_fibration_lemma2);
a(DROP_NTH_ASM_T 3 discard_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(GET_NTH_ASM_T 10 (ante_tac o list_∀_elim [⌜k+1⌝, ⌜(k+1)+1⌝])
	THEN rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [6] (MAP_EVERY ante_tac)
	THEN asm_rewrite_tac[plus_assoc_thm] THEN REPEAT strip_tac);
a(MAP_EVERY ∃_tac[⌜U⌝, ⌜C⌝, ⌜τ⌝] THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.2.1.1" *** *)
a(lemma_tac⌜(N × ClosedInterval 0. (t (k + 1))) ◁⋎T ρ ×⋎T O⋎R ∈ Topology⌝
	THEN1 basic_topology_tac[open_ℝ_topology_thm]);
a(lemma_tac⌜N ◁⋎T ρ ∈ Topology⌝
	THEN1 basic_topology_tac[]);
a(ℝ_continuity_tac[subspace_range_continuous_bc_thm]);
(* *** Goal "1.2.1.1.1" *** *)
a(strip_asm_tac open_ℝ_topology_thm);
a(ALL_FC_T rewrite_tac[product_topology_space_t_thm]);
a(PC_T1 "sets_ext1" rewrite_tac[space_t_ℝ_thm, ×_def]);
a(LEMMA_T ⌜N ⊆ Space⋎T ρ⌝ ante_tac THEN1 all_fc_tac [open_⊆_space_t_thm]);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.2.1.1.2" *** *)
a(rewrite_tac[comb_i_def, comb_k_def, ×_def]);
a(POP_ASM_T ante_tac THEN ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]
	THEN REPEAT strip_tac);
a(rewrite_tac[closed_interval_def]);
a(GET_NTH_ASM_T 15 (ante_tac o list_∀_elim [⌜0⌝, ⌜k+1⌝])
	THEN rewrite_tac[]);
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.2.1.1.3" *** *)
a(bc_thm_tac subspace_domain_continuous_thm THEN REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[i_continuous_thm]);
(* *** Goal "1.2.1.2" *** *)
a(LEMMA_T ⌜
	(N × ClosedInterval (t (k + 1)) (t (k + 2))) ◁⋎T ρ ×⋎T O⋎R =
	(N × ClosedInterval (t (k + 1)) (t (k + 2)))
		◁⋎T (N × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R⌝
	rewrite_thm_tac);
(* *** Goal "1.2.1.2.1" *** *)
a(conv_tac eq_sym_conv THEN bc_thm_tac ⊆_subspace_topology_thm);
a(GET_NTH_ASM_T 11 (ante_tac o list_∀_elim [⌜0⌝, ⌜k+1⌝])
	THEN rewrite_tac[]);
a(PC_T1 "sets_ext1" asm_rewrite_tac[closed_interval_def, ×_def]
	THEN REPEAT strip_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜(k+2) = n⌝
	THEN1 (all_var_elim_asm_tac1
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜k+2 < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 17 (ante_tac o list_∀_elim [⌜k+2⌝, ⌜n⌝])
	THEN asm_rewrite_tac[]
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac subspace_domain_continuous_thm THEN REPEAT strip_tac);
a(bc_tac[subspace_topology_thm, product_topology_thm]
	THEN asm_rewrite_tac[open_ℝ_topology_thm]);
(* *** Goal "1.2.1.3" *** *)
a(conv_tac eq_sym_conv THEN DROP_NTH_ASM_T 10 bc_thm_tac);
a(asm_rewrite_tac[closed_interval_def]);
a(DROP_NTH_ASM_T 11 (ante_tac o list_∀_elim [⌜0⌝, ⌜k+1⌝])
	THEN asm_rewrite_tac[]
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(lemma_tac⌜∀x⦁ x ∈ N ⇒ L(x, t(k+1)) = M(x, t(k+1))⌝
	THEN1 (REPEAT strip_tac THEN ALL_ASM_FC_T rewrite_tac[]));
a(lemma_tac⌜0. ≤ t(k+1)⌝
	THEN1(DROP_NTH_ASM_T 10 (ante_tac o list_∀_elim [⌜0⌝, ⌜k+1⌝])
		THEN asm_rewrite_tac[]
		THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜t(k+1) ≤ t(k+2)⌝
	THEN1(DROP_NTH_ASM_T 11 (ante_tac o list_∀_elim [⌜k+1⌝, ⌜(k+1)+1⌝])
		THEN rewrite_tac[] THEN rewrite_tac[plus_assoc_thm]
		THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[open_⊆_space_t_thm]);
a(all_fc_tac[×_interval_glueing_thm]);
a(∃_tac⌜h'⌝ THEN rename_tac[(⌜h'⌝, "K")] THEN REPEAT strip_tac);
(* *** Goal "1.2.2.1" *** *)
a(LIST_DROP_NTH_ASM_T [14] all_fc_tac);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(asm_rewrite_tac[closed_interval_def]);
(* *** Goal "1.2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [1, 3, 4, 10, 14] (MAP_EVERY ante_tac));
a(rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
a(strip_asm_tac (list_∀_elim[⌜s⌝, ⌜t(k+1)⌝] ℝ_≤_cases_thm)
	THEN ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜¬n = 0⌝
	THEN1 (contr_tac THEN all_var_elim_asm_tac1
			THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(strip_asm_tac (∀_elim ⌜n⌝ ℕ_cases_thm));
a(DROP_NTH_ASM_T 2 discard_tac THEN all_var_elim_asm_tac1);
a(POP_ASM_T (ante_tac o ∀_elim⌜i⌝));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
Next we show that every $y$ in $R$ has a neigbourhood $N$ for which the conditions of the previous lemma hold.

=SML

val ⦏covering_projection_fibration_lemma4⦎ = (* not saved *) snd ( "covering_projection_fibration_lemma4", (
set_goal([], ⌜∀ρ; σ; τ;
	p : 'b → 'c;
	f : 'a → 'b;
	h : 'a × ℝ → 'c;
	y : 'a ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
∧	f ∈ (ρ, σ) Continuous
∧	h ∈ (ρ ×⋎T O⋎R, τ) Continuous
∧	y ∈ Space⋎T ρ
⇒	∃n t N⦁
		y ∈ N
	∧	N ∈ ρ
	∧	t 0 = 0.
	∧	t n = 1.
	∧	(∀i j⦁ i < j ⇒ t i < t j)
	∧	∀i⦁	i < n ⇒
		∃C⦁	(∀ x s⦁ x ∈ N ∧ s ∈ ClosedInterval (t i) (t (i + 1)) ⇒ h (x, s) ∈ C)
		∧	C ∈ τ
		∧	∃U⦁	U ⊆ σ
			∧	(∀ x⦁ x ∈ Space⋎T σ ∧ p x ∈ C ⇒ (∃ A⦁ x ∈ A ∧ A ∈ U))
			∧	(∀ A B⦁ A ∈ U ∧ B ∈ U ∧ ¬ A ∩ B = {} ⇒ A = B)
			∧	(∀ A⦁ A ∈ U ⇒ p ∈ (A ◁⋎T σ, C ◁⋎T τ) Homeomorphism)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃U⦁
U = {A | ∃C⦁ C ∈ τ ∧ A = {vr | vr ∈ Space⋎T (ρ ×⋎T O⋎R) ∧ h vr ∈ C} ∧
	∃U⦁	U ⊆ σ
	∧	(∀ x⦁ x ∈ Space⋎T σ ∧ p x ∈ C ⇒ (∃ A⦁ x ∈ A ∧ A ∈ U))
	∧	(∀ A B⦁ A ∈ U ∧ B ∈ U ∧ ¬ A ∩ B = {} ⇒ A = B)
	∧	(∀ A⦁ A ∈ U ⇒ p ∈ (A ◁⋎T σ, C ◁⋎T τ) Homeomorphism)}⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∃n t N⦁ t 0 = 0. ∧ t n = 1. ∧ (∀ i j⦁ i < j ⇒ t i < t j)
	∧	y ∈ N
	∧	N ∈ ρ
	∧	∀i⦁ i < n ⇒ ∃B⦁ B ∈ U ∧ (N × ClosedInterval (t i) (t (i+1))) ⊆ B⌝);
(* *** Goal "1" *** *)
a(bc_thm_tac product_interval_cover_thm);
a(all_var_elim_asm_tac1 THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(all_fc_tac[continuous_open_thm]);
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[covering_projection_def]));
a(strip_asm_tac open_ℝ_topology_thm);
a(lemma_tac⌜(y, s) ∈ Space⋎T (ρ ×⋎T O⋎R)⌝
	THEN1 (ALL_FC_T rewrite_tac[product_topology_space_t_thm]
		THEN asm_rewrite_tac[×_def, space_t_ℝ_thm]));
a(all_fc_tac[continuous_∈_space_t_thm]);
a(LIST_DROP_NTH_ASM_T [5] fc_tac);
a(∃_tac⌜{vr|vr ∈ Space⋎T (ρ ×⋎T O⋎R) ∧ h vr ∈ C}⌝
	THEN asm_rewrite_tac[]);
a(∃_tac⌜C⌝ THEN asm_rewrite_tac[]);
a(∃_tac⌜U⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(MAP_EVERY ∃_tac [⌜n⌝, ⌜t⌝, ⌜N⌝] THEN all_var_elim_asm_tac1
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac THEN all_var_elim_asm_tac1);
a(∃_tac⌜C⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 3 (fn th => all_fc_tac[pc_rule1 "sets_ext1"rewrite_rule[×_def]th]));
(* *** Goal "2.2" *** *)
a(∃_tac⌜U⌝ THEN asm_rewrite_tac[]);
pop_thm()
));





=TEX
%%%%
%%%%

Putting the last two lemmas together, we have that every point has an open neigbourhood over which the homotopy can be lifted.

=SML

val ⦏covering_projection_fibration_lemma5⦎ = (* not saved *) snd ( "covering_projection_fibration_lemma5", (
set_goal([], ⌜∀ρ; σ; τ;
	p : 'b → 'c;
	f : 'a → 'b;
	h : 'a × ℝ → 'c ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
∧	f ∈ (ρ, σ) Continuous
∧	h ∈ (ρ ×⋎T O⋎R, τ) Continuous
∧	(∀x⦁ x ∈ Space⋎T ρ ⇒  h (x, 0.) = p (f x))
∧	y ∈ Space⋎T ρ
⇒	∃N : 'a SET⦁
	y ∈ N ∧ N ∈ ρ ∧
	∃L : 'a × ℝ → 'b⦁
	L ∈ ((N × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R, σ) Continuous
∧	(∀x⦁	x ∈ N
	⇒	L(x, 0.) = f x)
∧	(∀x s⦁	x ∈ N
	∧	s ∈ ClosedInterval 0. 1.
	⇒	p(L(x, s)) = h(x, s))
⌝);
a(REPEAT strip_tac THEN all_fc_tac[covering_projection_fibration_lemma4]);
a(∃_tac⌜N⌝ THEN REPEAT strip_tac);
a(bc_thm_tac covering_projection_fibration_lemma3);
a(MAP_EVERY ∃_tac[⌜n⌝, ⌜t⌝, ⌜τ⌝]
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac subspace_domain_continuous_thm
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(bc_thm_tac subspace_domain_continuous_thm
	THEN REPEAT strip_tac);
a(bc_thm_tac product_topology_thm THEN REPEAT strip_tac);
a(accept_tac open_ℝ_topology_thm);
(* *** Goal "3" *** *)
a(ALL_FC_T (PC_T1 "sets_ext1" all_fc_tac)[open_⊆_space_t_thm]);
a(DROP_NTH_ASM_T 10 bc_thm_tac THEN strip_tac);
pop_thm()
));



=TEX
%%%%
%%%%

Putting this altogether and using the unique lifting property to show that the local liftings agree where they overlap we have the main result (in its first form, with the lifting continuous on $R \times [0, 1]$ rather than $R \times ℝ$).
=SML

val ⦏covering_projection_fibration_lemma6⦎ = (* not saved *) snd
 ( "covering_projection_fibration_lemma6", (
set_goal([], ⌜∀ρ; σ; τ;
	p : 'b → 'c;
	f : 'a → 'b;
	h : 'a × ℝ → 'c ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
∧	f ∈ (ρ, σ) Continuous
∧	h ∈ (ρ ×⋎T O⋎R, τ) Continuous
∧	(∀x⦁ x ∈ Space⋎T ρ ⇒  h (x, 0.) = p (f x))
⇒	∃L : 'a × ℝ → 'b⦁
	L ∈ ((Space⋎T ρ × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R, σ) Continuous
∧	(∀x⦁	x ∈ Space⋎T ρ
	⇒	L(x, 0.) = f x)
∧	(∀x s⦁	x ∈ Space⋎T ρ
	∧	s ∈ ClosedInterval 0. 1.
	⇒	p(L(x, s)) = h(x, s))
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃N : 'a → 'a SET; K : 'a → 'a × ℝ → 'b⦁
	∀y⦁ y ∈ Space⋎T ρ ⇒
	y ∈ N y ∧ N y ∈ ρ ∧
	K y ∈ ((N y × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R, σ) Continuous
∧	(∀x⦁	x ∈ N y
	⇒	K y (x, 0.) = f x)
∧	(∀x s⦁	x ∈ N y
	∧	s ∈ ClosedInterval 0. 1.
	⇒	p(K y (x, s)) = h(x, s))⌝
	THEN1 (prove_∃_tac THEN strip_tac));
a(cases_tac⌜y'' ∈ Space⋎T ρ⌝ THEN asm_rewrite_tac[]);
a(all_fc_tac[covering_projection_fibration_lemma5]);
a(∃_tac⌜L⌝ THEN ∃_tac⌜N⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜λ(y, s)⦁ K y (y, s)⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LEMMA_T⌜(λ (y, s)⦁ K y (y, s)) = 
(λ (y, s)⦁ (λ(y, s)⦁K y) (y, s) (y, s))⌝
	pure_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac compatible_family_continuous_thm1);
a(∃_tac⌜λ(y, r)⦁(N y × ClosedInterval 0. 1.)⌝ THEN asm_rewrite_tac[×_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(bc_thm_tac product_topology_thm THEN
	asm_rewrite_tac[open_ℝ_topology_thm]);
(* *** Goal "2.1.2" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(all_fc_tac[open_⊆_space_t_thm]);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.1.3" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
(* *** Goal "2.1.4" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(rewrite_tac[subspace_topology_def]);
a(∃_tac⌜N v × Universe⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1.4.1" *** *)
a(rewrite_tac[product_topology_def, ×_def]
	THEN REPEAT strip_tac);
a(∃_tac⌜N v⌝ THEN ∃_tac⌜Universe⌝ THEN asm_rewrite_tac[empty_universe_open_closed_thm]);
(* *** Goal "2.1.4.2" *** *)
a(all_fc_tac[open_⊆_space_t_thm]);
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[×_def]);
(* *** Goal "2.1.5" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(LEMMA_T ⌜{(v', w)|v' ∈ N v ∧ w ∈ ClosedInterval 0. 1.} =
	(N v × ClosedInterval 0. 1.)⌝ asm_rewrite_thm_tac);
a(PC_T1 "sets_ext1" prove_tac[×_def]);
(* *** Goal "2.1.6" *** *)
a(LEMMA_T⌜∀r⦁r ∈ ClosedInterval 0. 1. ⇒
	(λr⦁K w (w, r)) r = (λr⦁K v (w, r)) r⌝
	(fn th => ALL_FC_T rewrite_tac[rewrite_rule[]th]));
a(strip_asm_tac open_ℝ_topology_thm);
a(LEMMA_T ⌜ClosedInterval 0. 1. = Space⋎T(ClosedInterval 0. 1. ◁⋎T O⋎R)⌝
	pure_once_rewrite_thm_tac
	THEN1 (ALL_FC_T rewrite_tac[subspace_topology_space_t_thm]
		THEN rewrite_tac[space_t_ℝ_thm]));
a(lemma_tac⌜ClosedInterval 0. 1. ◁⋎T O⋎R ∈ Topology⌝
	THEN1 basic_topology_tac[]);
a(bc_thm_tac unique_lifting_bc_thm);
a(MAP_EVERY ∃_tac[⌜0.⌝, ⌜p⌝, ⌜τ⌝, ⌜σ⌝]
	THEN ALL_FC_T asm_rewrite_tac[subspace_topology_space_t_thm]
	THEN rewrite_tac[space_t_ℝ_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.1.6.1" *** *)
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[
	conv_rule(ONCE_MAP_C eq_sym_conv)connected_topological_thm]);
a(bc_tac[closed_interval_connected_thm] THEN REPEAT strip_tac);
(* *** Goal "2.1.6.2" *** *)
a(bc_thm_tac comp_continuous_thm);
a(lemma_tac⌜ρ ×⋎T O⋎R ∈ Topology⌝
	THEN1 ALL_FC_T rewrite_tac[product_topology_thm]);
a(lemma_tac⌜(N v × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R ∈ Topology⌝
	THEN1 ALL_FC_T rewrite_tac[subspace_topology_thm]);
a(∃_tac⌜(N v × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.1.6.2.1" *** *)
a(LEMMA_T⌜$, w = λr:ℝ⦁(w, r)⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac subspace_continuous_thm THEN REPEAT strip_tac);
(* *** Goal "2.1.6.2.1.1" *** *)
a(bc_thm_tac right_product_inj_continuous_thm
	THEN REPEAT strip_tac);
a(lemma_tac⌜N v ∈ ρ⌝ THEN1 LIST_DROP_NTH_ASM_T[9] all_fc_tac);
a(ALL_FC_T (PC_T1 "sets_ext1" all_fc_tac)[open_⊆_space_t_thm]);
(* *** Goal "2.1.6.2.1.2" *** *)
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" rewrite_tac[×_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.1.6.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [9] fc_tac);
(* *** Goal "2.1.6.3" *** *)
a(bc_thm_tac comp_continuous_thm);
a(lemma_tac⌜ρ ×⋎T O⋎R ∈ Topology⌝
	THEN1 ALL_FC_T rewrite_tac[product_topology_thm]);
a(lemma_tac⌜N v ∈ ρ⌝ THEN1 LIST_DROP_NTH_ASM_T[8] all_fc_tac);
a(ALL_FC_T (PC_T1 "sets_ext1" all_fc_tac)[open_⊆_space_t_thm]);
a(lemma_tac⌜(N w × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R ∈ Topology⌝
	THEN1 ALL_FC_T rewrite_tac[subspace_topology_thm]);
a(∃_tac⌜(N w × ClosedInterval 0. 1.) ◁⋎T ρ ×⋎T O⋎R⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.1.6.3.1" *** *)
a(LEMMA_T⌜$, w = λr:ℝ⦁(w, r)⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac subspace_continuous_thm THEN REPEAT strip_tac);
(* *** Goal "2.1.6.3.1.1" *** *)
a(bc_thm_tac right_product_inj_continuous_thm
	THEN REPEAT strip_tac);
(* *** Goal "2.1.6.3.1.2" *** *)
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" rewrite_tac[×_def]
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T[12] all_fc_tac);
(* *** Goal "2.1.6.3.2" *** *)
a(LIST_DROP_NTH_ASM_T [11] fc_tac);
(* *** Goal "2.1.6.4" *** *)
a(lemma_tac⌜N v ∈ ρ⌝ THEN1 LIST_DROP_NTH_ASM_T[8] all_fc_tac);
a(ALL_FC_T (PC_T1 "sets_ext1" all_fc_tac)[open_⊆_space_t_thm]);
a(LIST_DROP_NTH_ASM_T [10] fc_tac);
(* It is unclear why so much hand-instantiation is needed here. *)
a(list_spec_nth_asm_tac 5 [⌜w⌝, ⌜x⌝]);
a(list_spec_nth_asm_tac 10 [⌜w⌝, ⌜x⌝]);
a(asm_rewrite_tac[]);
(* *** Goal "2.1.6.5" *** *)
a(rewrite_tac[closed_interval_def]);
(* *** Goal "2.1.6.6" *** *)
a(lemma_tac⌜N v ∈ ρ⌝ THEN1 LIST_DROP_NTH_ASM_T[7] all_fc_tac);
a(ALL_FC_T (PC_T1 "sets_ext1" all_fc_tac)[open_⊆_space_t_thm]);
a(LIST_DROP_NTH_ASM_T [9] fc_tac);
a(spec_nth_asm_tac 4 ⌜w⌝);
a(spec_nth_asm_tac 9 ⌜w⌝);
a(asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2.3" *** *)
a(LIST_DROP_NTH_ASM_T [3] fc_tac);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
pop_thm()
));


=TEX
This leads to the second form, with the lifting continuous on $R \times ℝ$.
=SML

val ⦏covering_projection_fibration_thm⦎ = save_thm ( "covering_projection_fibration_thm", (
set_goal([], ⌜∀ρ; σ; τ;
	p : 'b → 'c ⦁
	ρ ∈ Topology
∧	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
⇒	(ρ, (p, σ, τ)) ∈ HomotopyLiftingProperty
⌝);
a(rewrite_tac [homotopy_lifting_property_def] THEN REPEAT strip_tac
	THEN1 all_fc_tac[covering_projection_continuous_thm]);
a(all_fc_tac[covering_projection_fibration_lemma6]);
a(LEMMA_T ⌜Space⋎T ρ ⊆ Space⋎T ρ⌝ asm_tac THEN1 rewrite_tac[]);
a(LEMMA_T ⌜0. ≤ 1.⌝ asm_tac THEN1 rewrite_tac[]);
a(all_fc_tac [closed_interval_extension_thm]);
a(∃_tac⌜g⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 2 ante_tac);
a(strip_asm_tac open_ℝ_topology_thm);
a(lemma_tac⌜ρ ×⋎T O⋎R ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(LEMMA_T ⌜(Space⋎T ρ × Universe) = Space⋎T(ρ ×⋎T O⋎R)⌝
	(fn th => rewrite_tac[th]
		THEN ALL_FC_T rewrite_tac[trivial_subspace_topology_thm]));
a(ALL_FC_T rewrite_tac[product_topology_space_t_thm]);
a(rewrite_tac[space_t_ℝ_thm]);
(* *** Goal "2" *** *)
a(lemma_tac⌜0. ∈ ClosedInterval 0. 1.⌝ THEN1 rewrite_tac[closed_interval_def]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(ALL_ASM_FC_T asm_rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

Path lifting property.

=SML
val ⦏covering_projection_path_lifting_thm⦎ = save_thm ( "covering_projection_path_lifting_thm", (
set_goal([], ⌜∀σ; τ;
	p : 'a → 'b;
	y : 'a;
	f : ℝ → 'b ⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
⇒	(p, σ, τ) ∈ PathLiftingProperty
⌝);
a(rewrite_tac[path_lifting_property_def] THEN REPEAT strip_tac
	THEN1 all_fc_tac[covering_projection_continuous_thm]);
a(DROP_NTH_ASM_T 4 (strip_asm_tac o rewrite_rule[paths_def]));
a(lemma_tac⌜∃h: ℝ → 'a⦁
	h ∈ (O⋎R, σ) Continuous
∧	h 0. = y
∧	(∀s⦁ s ∈ ClosedInterval 0. 1. ⇒ p(h s) = f s)⌝);
(* *** Goal "1" *** *)
a((ante_tac o list_∀_elim[ ⌜1⋎T⌝, ⌜σ⌝, ⌜τ⌝, ⌜p⌝])
	covering_projection_fibration_thm);
a(asm_rewrite_tac [homotopy_lifting_property_def,
	one_def, unit_topology_thm, space_t_unit_topology_thm]);
a(STRIP_T (ante_tac o list_∀_elim[ ⌜λx:ONE⦁y⌝, ⌜λ(x:ONE, t)⦁f t⌝]));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(i_contr_tac THEN POP_ASM_T ante_tac THEN ℝ_continuity_tac[unit_topology_thm]);
(* *** Goal "1.2" *** *)
a(i_contr_tac THEN POP_ASM_T ante_tac THEN ℝ_continuity_tac[unit_topology_thm]);
(* *** Goal "1.3" *** *)
a(∃_tac⌜λt⦁ L(One, t)⌝ THEN asm_rewrite_tac[]);
a(lemma_tac⌜1⋎T ×⋎T O⋎R ∈ Topology⌝ THEN1 basic_topology_tac[open_ℝ_topology_thm]);
a(ℝ_continuity_tac[unit_topology_thm, space_t_unit_topology_thm]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 6 (fn th => all_fc_tac[paths_representative_thm]
	THEN asm_tac th));
a(∃_tac⌜g⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 6 (rewrite_thm_tac o eq_sym_rule));
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN rewrite_tac[closed_interval_def]);
(* *** Goal "2.2" *** *)
a(cases_tac⌜s ∈ ClosedInterval 0. 1.⌝ THEN1 ALL_ASM_FC_T rewrite_tac[]);
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[paths_def]));
a(DROP_NTH_ASM_T 4 (strip_asm_tac o rewrite_rule[closed_interval_def]));
(* *** Goal "2.2.1" *** *)
a(lemma_tac⌜s ≤ 0.⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_ASM_FC_T rewrite_tac[]);
a(LEMMA_T ⌜g 0. = h 0.⌝ rewrite_thm_tac THEN1
	(DROP_NTH_ASM_T 8 bc_thm_tac THEN rewrite_tac[closed_interval_def]));
a(DROP_NTH_ASM_T 9 bc_thm_tac THEN rewrite_tac[closed_interval_def]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜1. ≤ s⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_ASM_FC_T rewrite_tac[]);
a(LEMMA_T ⌜g 1. = h 1.⌝ rewrite_thm_tac THEN1
	(DROP_NTH_ASM_T 8 bc_thm_tac THEN rewrite_tac[closed_interval_def]));
a(DROP_NTH_ASM_T 9 bc_thm_tac THEN rewrite_tac[closed_interval_def]);
pop_thm()
));


=TEX
The above reformulated to be be more convenient for back-chaining etc.
=SML


val ⦏covering_projection_path_lifting_bc_thm⦎ = save_thm ( "covering_projection_path_lifting_bc_thm", (
set_goal([], ⌜∀σ; τ;
	p : 'a → 'b;
	y : 'a;
	f : ℝ → 'b ⦁
	σ ∈ Topology
∧	τ ∈ Topology
∧	p ∈ (σ, τ) CoveringProjection
∧	f ∈ Paths τ
∧	y ∈ Space⋎T σ
∧	p y = f 0.
⇒	∃g: ℝ → 'a⦁
	g ∈ Paths σ
∧	g 0. = y
∧	(∀s⦁ p(g s) = f s)
⌝);
a(REPEAT strip_tac THEN ALL_FC_T (MAP_EVERY ante_tac) [covering_projection_path_lifting_thm]);
a(rewrite_tac[path_lifting_property_def] THEN REPEAT strip_tac);
a(contr_tac THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]);
pop_thm()
));
=SML
val _ = set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'topology_ℝ", "'ℝ"];

=TEX
\subsection{Epilogue}
=TEX
=SML
output_theory{out_file="wrk0671.th.pp", theory="topology"};
output_theory{out_file="wrk0672.th.doc", theory="metric_spaces"};
output_theory{out_file="wrk0673.th.doc", theory="topology_ℝ"};
output_theory{out_file="wrk0674.th.doc", theory="homotopy"};
=TEX
\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}
\end{document}



