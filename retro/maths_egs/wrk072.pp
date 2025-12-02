=IGN
********************************************************************************
wrk072.doc: this file is supplementary material for the ProofPower system

Copyright (c) 2004 Lemma 1 Ltd.

This file is supplied under the GNU General Public Licence (GPL) version 2.

See the file LICENSE supplied with ProofPower source for the terms of the GPL
or visit the OpenSource web site at http://www.opensource.org/

Contact: Rob Arthan < rda@lemma-one.com >
********************************************************************************
wrk072.doc,v 1.15 2010/11/14 11:55:24 rda Exp
********************************************************************************
% wrk072.doc 1.15 wrk072.doc,v 2010/11/14 11:55:24
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\usepackage{A4}
\usepackage{url}
\def\Hide#1{\relax}
\def\N{\mathbb{N}}
\def\D{\mathbb{D}}
\def\B{\mathbb{B}}
\def\C{\mathbb{C}}
\def\R{\mathbb{R}}
\def\Z{\mathbb{Z}}
\def\Q{\mathbb{Q}}
\title{Mathematical Case Studies: the Complex Numbers\thanks{
First posted 17 September 2005;
for full changes history see: \protect\url{https://github.com/RobArthan/pp-contrib}.
}}
\author{Rob Arthan\\{\tt rda@lemma-one.com}}
\date{\FormatDate{\VCDate}}
\makeindex
\begin{document}
\vfill
\begin{titlepage}
\maketitle
\begin{abstract}

Definitions of the complex numbers and their arithmetic operators in {\ProductHOL} with proofs of some of their elementary algebraic properties.

\end{abstract}
\vfill
\begin{centering}

\bf Copyright \copyright\ : Lemma 1 Ltd 2005--\number\year \\
Reference: LEMMA1/HOL/WRK072; Current git revision: \VCVersion%


\end{centering}
\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
\tableofcontents
\newpage
\section{INTRODUCTION}
This document contains the beginnings of a theory of complex arithmetic in {\ProductHOL}.

After some preliminaries, section~\ref{sec:algebra} introduces the field operations and the embedddings of the real numbers and of conjugation (which help to abbreviate the definition of reciprocals).
We then define the derived operations of binary subtraction and division and the embedding of the natural numbers.

In section~\ref{sec:topology} we introduce the topology on the complex numbers and define the exponential mapping of the real line onto the unit circle.

A proof script contained in the source of this document but hidden from the printed document proves several theorems about the complex numbers.
A listing of the theorems proved is given in appendix~\ref{listing}.

We prove that the complex numbers form a field and prove some elementary algebraic properties of complex conjugation and of the embeddings of the natural numbers and the real numbers in the complex numbers.
The proofs of these basic algebraic properties generally comprise little more than simplifying using definitions and standard theorems and then application of the decision procedure for linear arithmetic to prove the resulting problem of real algebra.
One exception is proving that $zz^{-1} = 1$, which requires a few lines of reasoning about real squares.

The proof scripts then go on to develop basic facts about the exponential mapping of the real line onto the unit circle, leading up to the important fact that it is a covering projection.



\section{THE ALGEBRA ℂ}\label{sec:algebra}

\subsection{Preliminaries}
The following commands set up a theory to hold the definitions, theorems, etc.
The theory has the theory of analysis defined in ~\cite{LEMMA1/HOL/WRK066} for its parent, although the elementary algebraic theory only needs one or two little theorems about squares.
=SML
force_delete_theory "ℂ" handle Fail _ => ();
open_theory "analysis";
new_theory "ℂ";
new_parent "homotopy";
new_parent "group_egs";
=IGN
open_theory"ℂ";
=TEX
Now set up a convenient proof context:
=SML
set_merge_pcs["basic_hol1", "'ℤ", "'ℝ", "'sets_alg"];
=TEX
\subsection{The Type ℂ}
The type ℂ comprises pairs of real numbers.
We capture this in a type abbreviation:
=SML
declare_type_abbrev("ℂ", [], ⓣℝ × ℝ⌝);
=TEX
We declare aliases for the instances of the projection functions
that give the real and imaginary part of a complex number:
=SML
app declare_alias [
	("Re", ⌜Fst : ℂ → ℝ⌝),
	("Im", ⌜Snd : ℂ → ℝ⌝)];
=TEX

\subsection{Algebraic Operators}
\subsubsection{Addition}

=SML
declare_infix(300, "+⋎C");
=TEX

ⓈHOLCONST
│ $⦏+⋎C⦎ : ℂ → ℂ → ℂ
├──────
│∀ z w : ℂ⦁ z +⋎C w = (Re z + Re w, Im z + Im w)
■

=SML
declare_alias("+", ⌜$+⋎C⌝);
=TEX
\subsubsection{Negation}

ⓈHOLCONST
│ ⦏~⋎C⦎ : ℂ → ℂ
├──────
│∀ z : ℂ⦁ ~⋎C z = (~(Re z), ~(Im z))
■
=SML
declare_alias("~", ⌜~⋎C⌝);
=TEX

=TEX
\subsubsection{Multiplication}
=SML
declare_infix(310, "*⋎C");
=TEX

ⓈHOLCONST
│ $⦏*⋎C⦎ : ℂ → ℂ → ℂ
├──────
│∀ z w : ℂ⦁
│	z *⋎C w = (Re z * Re w - Im z * Im w, Re z * Im w + Im z * Re w)
■

=SML
declare_alias("*", ⌜$*⋎C⌝);
=TEX
\subsubsection{Embedding of the Real Numbers}


ⓈHOLCONST
│ ⦏ℝℂ⦎ : ℝ → ℂ
├──────
│∀x⦁ ℝℂ x = (x, ℕℝ 0)
■

ⓈHOLCONST
│ ⦏ℝι⦎ : ℝ → ℂ
├──────
│∀x⦁ ℝι x = (ℕℝ 0, x)
■
\subsubsection{The Imaginary Unit}

ⓈHOLCONST
│ ⦏I⋎C⦎ : ℂ
├──────
│ I⋎C =ℝι 1.0
■
\subsubsection{Conjugation}
=SML
declare_postfix(320, "⋏_");
=TEX
ⓈHOLCONST
│ ⦏$⋏_⦎ : ℂ → ℂ
├──────
│∀ z : ℂ⦁ z ⋏_ = (Re z, ~(Im z))
■
\subsubsection{Reciprocal}
=SML
declare_postfix(320, "⋏-⋏1⋏C");
=TEX

ⓈHOLCONST
│ $⦏⋏-⋏1⋏C⦎ : ℂ → ℂ
├──────
│∀ z : ℂ⦁ z ⋏-⋏1⋏C = z ⋏_ * ℝℂ(Re (z * z ⋏_) ⋏-⋏1)
■

=SML
declare_alias("⋏-⋏1", ⌜$⋏-⋏1⋏C⌝);
=TEX


\subsubsection{Subtraction}
=SML
declare_infix(300, "-⋎C");
=TEX

ⓈHOLCONST
│ $⦏-⋎C⦎ : ℂ → ℂ → ℂ
├──────
│∀ z w : ℂ⦁ z -⋎C w = z + ~w
■



\subsubsection{Division}
=SML
declare_infix(315, "/⋎C");
=TEX

ⓈHOLCONST
│ $⦏/⋎C⦎ : ℂ → ℂ → ℂ
├──────
│∀ z w : ℂ⦁ z /⋎C w = z * (w ⋏-⋏1)
■


=SML
declare_alias("/", ⌜$/⋎C⌝);
=TEX
\subsubsection{Embedding of the Natural Numbers}


ⓈHOLCONST
│ ⦏ℕℂ⦎ : ℕ → ℂ
├──────
│∀m⦁ ℕℂ m = ℝℂ(ℕℝ m)
■


ⓈHOLCONST
│ ⦏ℕι⦎ : ℕ → ℂ
├──────
│∀m⦁ ℕι m = (0., ℕℝ m)
■

\subsubsection{Exponentiation with Natural Number Exponents}

=SML
declare_infix(320, "^⋎C");
=TEX
ⓈHOLCONST
│ $⦏^⋎C⦎ : ℂ → ℕ → ℂ
├──────
│	(∀ z: ℂ⦁ z ^⋎C 0 = ℕℂ 1)
│ ∧	(∀ z: ℂ; m⦁ z ^⋎C (m+1) = z * z ^⋎C m)
■

=SML
declare_alias("^", ⌜$^⋎C⌝);
=TEX
\subsection{ℂ {\it qua} Real Normed Space}
=SML
declare_infix(310, "*⋎RC");
=TEX

ⓈHOLCONST
│ $⦏*⋎RC⦎ : ℝ → ℂ → ℂ
├──────
│∀ x: ℝ; v : ℂ⦁
│	x *⋎RC v = ℝℂ x *⋎C v
■

ⓈHOLCONST
│ ⦏Abs⋎C⦎ : ℂ → ℝ
├──────
│∀ v : ℂ⦁
│	Abs⋎C v = Sqrt(Re (v * v ⋏_))
■

\subsection{Transcendental Functions}
\subsubsection{Exponential}
ⓈHOLCONST
│ ⦏Exp⋎C⦎ : ℂ → ℂ
├──────
│ ∀z⦁ Exp⋎C z = ℝℂ (Exp(Re z)) * (Cos (Im z), Sin (Im z))
■

=SML
declare_alias("Exp", ⌜$Exp⋎C⌝);
=TEX
\subsubsection{Group Structures}

We now define the additive and multiplicative groups of complex numbers.

ⓈHOLCONST
│ ⦏ℂ⋎+⦎ :  ℂ GROUP;
│ ⦏ℂ⋎*⦎ :  ℂ GROUP
├──────
│	ℂ⋎+ = MkGROUP Universe $+ (ℕℂ 0) ~
│ ∧	ℂ⋎* = MkGROUP {x | ¬x = ℕℂ 0} $* (ℕℂ 1) $⋏-⋏1
■


\section{POLYNOMIALS}\label{sec:polynomials}
As we did for the real numbers in \cite{LEMMA1/HOL/WRK066},
we define the set of polynomial function on the complex
numbers to be the smallest set of functions
that contains all constant functions and the identity function and that
is closed under pointwise addition and multiplication of functions.
ⓈHOLCONST
│ ⦏PolyFunc⋎C⦎ : (ℂ → ℂ) SET
├──────
│ PolyFunc⋎C = ⋂
│	{	A
│	|	(∀c⦁ (λx⦁c) ∈ A)
│	∧	(λx⦁x) ∈ A
│	∧	(∀f g⦁f ∈ A ∧ g ∈ A ⇒ (λx⦁f x + g x) ∈ A)
│	∧	(∀f g⦁f ∈ A ∧ g ∈ A ⇒ (λx⦁f x * g x) ∈ A) }
■

The following function gives the $n$-th partial sum of a series.

ⓈHOLCONST
│ ⦏Series⋎C⦎ : (ℕ → ℂ) → (ℕ → ℂ)
├──────
│	(∀s⦁ Series⋎C s 0 = ℕℂ 0)
│ ∧	(∀s n⦁ Series⋎C s (n+1) = Series⋎C s n + s n)
■

We represent a complex polynomial as a pair $(s, n)$ where $s$ is a sequence of coefficients and $n$ is a bound on the degree.
The following function maps such a pair to the polynomial function it represents.

ⓈHOLCONST
│ ⦏PolyEval⋎C⦎ : (ℕ → ℂ) × ℕ → ℂ → ℂ
├──────
│	∀s n z⦁ PolyEval⋎C (s, n) z = Series⋎C (λi⦁ s i * z^i) (n+1)
■
We now give the operations on coefficients that correspond to addition of polynomial functions \ldots

ⓈHOLCONST
│ ⦏PlusCoeffs⋎C⦎ : ((ℕ → ℂ) × ℕ) → ((ℕ → ℂ) × ℕ) → ((ℕ → ℂ) × ℕ)
├──────
│ ∀s m t n⦁
│	PlusCoeffs⋎C (s, m) (t, n) =
│	((λi⦁	(if i ≤ m then s i else ℕℂ 0) +
│		(if i ≤ n then t i else ℕℂ 0)), m+n)
■

\ldots and to multiplication of one polynomial function by another.

ⓈHOLCONST
│ ⦏TimesCoeffs⋎C⦎ : ((ℕ → ℂ) × ℕ) → ((ℕ → ℂ) × ℕ) → ((ℕ → ℂ) × ℕ)
├──────
│ 	(∀s t n⦁ TimesCoeffs⋎C (s, 0) (t, n) = ((λi⦁ s 0 * t i), n))
│∧	(∀s m t n⦁
│	TimesCoeffs⋎C (s, m+1) (t, n) =
│	PlusCoeffs⋎C
│	(TimesCoeffs⋎C (s, m) (t, n))
│	((λi⦁ if i ≤ m then ℕℂ 0 else s (m+1) * t (i-(m+1))), m+n+1))
■

\section{TOPOLOGICAL ASPECTS}\label{sec:topology}
The standard topology on ℂ is just the product topology:
ⓈHOLCONST
│ ⦏Open⋎C⦎ : ℂ SET SET
├──────
│ Open⋎C = O⋎R ×⋎T O⋎R
■
As with 
=INLINEFT
Open⋎R
=TEX
\ it is convenient to have a short name for the topology:
=SML
declare_alias("O⋎C", ⌜Open⋎C⌝);
=TEX
The unit circle $S^1$:
ⓈHOLCONST
│ ⦏S1⦎ : ℂ SET
├──────
│ S1 = {z | Abs⋎C z = 1.}
■
=TEX
The topology on the unit circle:
ⓈHOLCONST
│ ⦏Open⋎S1⦎ : ℂ SET SET
├──────
│ Open⋎S1 = S1 ◁⋎T O⋎C
■
Again it is convenient to have a short name for the topology:
=SML
declare_alias("O⋎S1", ⌜Open⋎S1⌝);
=TEX
and the exponential mapping of the real line onto the unit circle:
ⓈHOLCONST
│ ⦏ExpS1⦎ : ℝ → ℂ
├──────
│ ∀t⦁ ExpS1 t = (Cos t, Sin t)
■

The length of a lift of a path in $S^1$ to the universal cover:
ⓈHOLCONST
│ ⦏PathS1LiftLength⦎ : (ℝ → ℂ) → ℝ
├──────
│ ∀f g⦁
│	f ∈ Paths O⋎S1 ∧ g ∈ Paths O⋎R ∧ (∀s⦁ ExpS1(g s) = f s)
│ ⇒	g 1. - g 0. = PathS1LiftLength f
■

The degree of a loop in the unit circle:
ⓈHOLCONST
│ ⦏LoopS1Degree⦎ : (ℝ → ℂ) → ℤ
├──────
│ ∀x f g⦁
│	f ∈ Loops(O⋎S1, x) ∧ g ∈ Paths O⋎R ∧ (∀s⦁ ExpS1(g s) = f s)
│ ⇒	g 1. - g 0. = 2. * ℤℝ (LoopS1Degree f) * π
■
The generator of the fundamental group of the circle.
ⓈHOLCONST
│ ⦏IotaS1⦎ : ℝ → ℂ
├──────
│ IotaS1 = (λt⦁ if t ≤ 0. ∨ 1. ≤ t then ℕℂ 1 else ExpS1(2. * π * t))
■
The function that converts a self-mapping of the unit circle into a loop.
ⓈHOLCONST
│ ⦏S1S1Loop⦎ : (ℂ → ℂ) → (ℝ → ℂ)
├──────
│ ∀f⦁	S1S1Loop f = (λt⦁ f (IotaS1 t))
■

The degree of a self-mapping of the unit circle:
ⓈHOLCONST
│ ⦏S1S1Degree⦎ : (ℂ → ℂ) → ℤ
├──────
│ ∀f⦁	S1S1Degree f = LoopS1Degree (S1S1Loop f)
■

The degree of an element of the fundamental group of the unit circle:
ⓈHOLCONST
│ ⦏ClassS1Degree⦎ : (ℝ → ℂ) ℙ → ℤ
├──────
│ ∀x p f⦁
│	p ∈ Loops(O⋎S1, x) / PathHomotopic O⋎S1 ∧ f ∈ p
│ ⇒	ClassS1Degree p = LoopS1Degree f
■

=TEX
%\twocolumn[\section{INDEX}\label{INDEX}]
%{\printindex}

\bibliographystyle{fmu}
\bibliography{fmu}

\appendix
{\let\Section\section
\let\subsection\Hide
\def\section#1{\Section{#1}\label{listing}}
\let\subsection\Hide
\include{wrk072.th}}


\twocolumn[\section*{INDEX}\label{INDEX}]
\addcontentsline{toc}{section}{INDEX}
{\small\printindex}

=TEX
\end{document} %% COMMENT THIS LINE OUT TO TYPESET THE PROOF SCRIPTS
\ftlinepenalty=9999
\section{PROOFS}

\subsection{Preamble}

=TEX
Set context for proofs in case of future expansion.
=SML
open_theory"ℂ";
set_merge_pcs["basic_hol1", "'ℤ", "'ℝ", "'sets_alg"];
=TEX
Give ML bindings for the defining properties:
%%%%
%%%%
=SML

val ⦏ℂ_plus_def⦎ = get_spec ⌜$+⋎C⌝;
val ⦏ℂ_minus_def⦎ = get_spec ⌜~⋎C⌝;
val ⦏ℂ_conj_def⦎ = get_spec ⌜$⋏_⌝;
val ⦏ℂ_times_def⦎ = get_spec ⌜$*⋎C⌝;
val ⦏ℂ_recip_def⦎ = get_spec ⌜$⋏-⋏1⋏C⌝;
val ⦏ℂ_subtract_def⦎ = get_spec ⌜$-⋎C⌝;
val ⦏ℕℂ_def⦎ = get_spec ⌜ℕℂ⌝;
val ⦏ℝℂ_def⦎ = get_spec ⌜ℝℂ⌝;
val ⦏ℕι_def⦎ = get_spec ⌜ℕι⌝;
val ⦏ℝι_def⦎ = get_spec ⌜ℝι⌝;
val ⦏ℂ_i_def⦎ = get_spec ⌜I⋎C⌝;
val ⦏ℝ_ℂ_times_def⦎ = get_spec ⌜$*⋎RC⌝;
val ⦏ℂ_ℕ_exp_def⦎ = get_spec ⌜$^⋎C⌝;
val ⦏ℂ_abs_def⦎ = get_spec ⌜Abs⋎C⌝;
val ⦏ℂ_ops_defs⦎ = [ℂ_plus_def, ℂ_minus_def, ℂ_conj_def, ℂ_times_def,
	ℂ_recip_def, ℂ_subtract_def, ℕℂ_def, ℝℂ_def, ℂ_ℕ_exp_def];
val ⦏ℂ_additive_def⦎ = get_spec⌜ℂ⋎+⌝;
val ⦏ℂ_multiplicative_def⦎ = get_spec⌜ℂ⋎*⌝;
val ⦏ℂ_poly_func_def⦎ = get_spec ⌜PolyFunc⋎C⌝;
val ⦏ℂ_series_def⦎ = get_spec ⌜Series⋎C⌝;
val ⦏ℂ_poly_eval_def⦎ = get_spec ⌜PolyEval⋎C⌝;
val ⦏ℂ_plus_coeffs_def⦎ = get_spec ⌜PlusCoeffs⋎C⌝;
val ⦏ℂ_times_coeffs_def⦎ = get_spec ⌜TimesCoeffs⋎C⌝;
val ⦏open_ℂ_def⦎ = get_spec ⌜O⋎C⌝;
val ⦏s1_def⦎ = get_spec ⌜S1⌝;
val ⦏open_s1_def⦎ = get_spec ⌜O⋎S1⌝;
val ⦏ℂ_exp_def⦎ = get_spec ⌜Exp⋎C⌝;
val ⦏exp_s1_def⦎ = get_spec ⌜ExpS1⌝;
val ⦏exp_s1_def1⦎ = ⇔_t_elim (rewrite_conv[exp_s1_def]
	⌜ExpS1 = (λ x⦁ (Cos x, Sin x))⌝);
val ⦏iota_s1_def⦎ = get_spec ⌜IotaS1⌝;
val ⦏s1_s1_loop_def⦎ = get_spec ⌜S1S1Loop⌝;
val ⦏s1_s1_degree_def⦎ = get_spec ⌜S1S1Degree⌝;

=TEX

\subsection{Tools}
The following could usefully go elsewhere:


=SML
val ⦏un_η_conv⦎ : CONV =
	simple_eq_match_conv
		(conv_rule(ONCE_MAP_C eq_sym_conv) η_axiom);

=TEX
=TEX
\subsection{Basic Algebraic Properties}

%%%%
%%%%
=SML

val ⦏ℂ_plus_comm_thm⦎ = save_thm( "ℂ_plus_comm_thm", (
set_goal([], ⌜∀ x y:ℂ⦁ x + y = y + x⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_plus_assoc_thm⦎ = save_thm( "ℂ_plus_assoc_thm", (
set_goal([], ⌜∀ x y z:ℂ⦁ (x + y) + z = x + y + z⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

val ⦏ℂ_plus_assoc_thm1⦎ = save_thm ("ℂ_plus_assoc_thm1",
	conv_rule(ONCE_MAP_C eq_sym_conv) ℂ_plus_assoc_thm);
=SML

val ⦏ℂ_plus_0_thm⦎ = save_thm( "ℂ_plus_0_thm", (
set_goal([], ⌜∀ x:ℂ⦁ x + ℕℂ 0 = x ∧ ℕℂ0 + x = x⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=SML

val ⦏ℂ_plus_minus_thm⦎ = save_thm( "ℂ_plus_minus_thm", (
set_goal([], ⌜∀ x:ℂ⦁ x + ~x = ℕℂ 0 ∧ ~x + x = ℕℂ 0⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_conj_thm⦎ = save_thm( "ℂ_times_conj_thm", (
set_goal([], ⌜∀ x:ℂ⦁
	x * (x ⋏_) = ℝℂ(Re x ^ 2 + Im x ^ 2)
⌝);
a(rewrite_tac (ℝ_ℕ_exp_square_thm::ℂ_ops_defs) THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_comm_thm⦎ = save_thm( "ℂ_times_comm_thm", (
set_goal([], ⌜∀ x y:ℂ⦁ x * y = y * x⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_assoc_thm⦎ = save_thm( "ℂ_times_assoc_thm", (
set_goal([], ⌜∀ x y z:ℂ⦁ (x * y) * z = x * y * z⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

val ⦏ℂ_times_assoc_thm1⦎ = save_thm ("ℂ_times_assoc_thm1",
	conv_rule(ONCE_MAP_C eq_sym_conv) ℂ_times_assoc_thm);

=SML

val ⦏ℂ_times_1_thm⦎ = save_thm( "ℂ_times_1_thm", (
set_goal([], ⌜∀ x:ℂ⦁ x * ℕℂ 1 = x ∧ ℕℂ 1 * x = x⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));



=SML

val ⦏ℂ_times_recip_thm⦎ = save_thm( "ℂ_times_recip_thm", (
set_goal([], ⌜∀ x:ℂ⦁ ¬x = ℕℂ 0 ⇒ x * x ⋏-⋏1 = ℕℂ 1⌝);
a(rewrite_tac [ℂ_recip_def, ℂ_times_conj_thm]);
a(rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv) ℂ_times_assoc_thm, ℂ_times_conj_thm]);
a(rewrite_tac ℂ_ops_defs);
a(∀_tac THEN STRIP_T asm_tac);
a(bc_thm_tac (rewrite_rule[](nth 2 (fc_canon(∧_left_elim ℝ_recip_clauses)))));
a(strip_asm_tac(∀_elim⌜Re x⌝ ℝ_0_≤_square_thm));
a(strip_asm_tac(∀_elim⌜Im x⌝ ℝ_0_≤_square_thm));
a(swap_nth_asm_concl_tac 3);
a(LEMMA_T ⌜Re x ^ 2 = ℕℝ 0 ∧ Im x ^ 2  = ℕℝ 0⌝ ante_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_square_eq_0_thm]);
pop_thm()
));

val ⦏ℂ_times_recip_thm1⦎ = save_thm ("ℂ_times_recip_thm1",
	conv_rule(once_rewrite_conv[ℂ_times_comm_thm]) ℂ_times_recip_thm);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_eq_1_thm⦎ = save_thm( "ℂ_times_eq_1_thm", (
set_goal([], ⌜∀ z w:ℂ⦁ ¬z = ℕℂ 0 ∧ z*w = ℕℂ 1 ⇒ w = z ⋏-⋏1⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜z ⋏-⋏1 * z * w = z ⋏-⋏1⌝ ante_tac
	THEN1 asm_rewrite_tac[ℂ_times_1_thm]);
a(rewrite_tac[ℂ_times_assoc_thm1]);
a(conv_tac(LEFT_C(LEFT_C(once_rewrite_conv[ℂ_times_comm_thm]))));
a(ALL_FC_T rewrite_tac[ℂ_times_recip_thm1]);
a(rewrite_tac[ℂ_times_1_thm]);
pop_thm()
));




=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_plus_distrib_thm⦎ = save_thm( "ℂ_times_plus_distrib_thm", (
set_goal([], ⌜∀ x y z:ℂ⦁
	x * (y + z) = x * y + x * z
∧	(x + y) * z = x * z + y * z⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_conj_plus_homomorphism_thm⦎ = save_thm( "ℂ_conj_plus_homomorphism_thm", (
set_goal([], ⌜∀ x y:ℂ⦁ (x + y) ⋏_  = x ⋏_ + y ⋏_⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_conj_times_homomorphism_thm⦎ = save_thm( "ℂ_conj_times_homomorphism_thm", (
set_goal([], ⌜∀ x y:ℂ⦁ (x * y) ⋏_  = x ⋏_ * y ⋏_⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝℂ_plus_homomorphism_thm⦎ = save_thm( "ℝℂ_plus_homomorphism_thm", (
set_goal([], ⌜∀ x y:ℝ⦁ ℝℂ(x + y) = ℝℂ x + ℝℂ y⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝℂ_times_homomorphism_thm⦎ = save_thm( "ℝℂ_times_homomorphism_thm", (
set_goal([], ⌜∀ x y:ℝ⦁ ℝℂ(x * y) = ℝℂ x * ℝℂ y⌝);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℕℂ_plus_homomorphism_thm⦎ = save_thm( "ℕℂ_plus_homomorphism_thm", (
set_goal([], ⌜∀ x y:ℕ⦁ ℕℂ(x + y) = ℕℂ x + ℕℂ y⌝);
a(rewrite_tac (ℕℝ_plus_homomorphism_thm::ℂ_ops_defs));
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℕℂ_one_one_thm⦎ = save_thm( "ℕℂ_one_one_thm", (
set_goal([], ⌜∀ m n:ℕ⦁ ℕℂ m = ℕℂ n ⇔ m = n⌝);
a(rewrite_tac (ℕℝ_one_one_thm::ℂ_ops_defs));
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℕℂ_times_homomorphism_thm⦎ = save_thm( "ℕℂ_times_homomorphism_thm", (
set_goal([], ⌜∀ x y:ℕ⦁ ℕℂ(x * y) = ℕℂ x * ℕℂ y⌝);
a(rewrite_tac (ℕℝ_times_homomorphism_thm::ℂ_ops_defs));
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_plus_order_thm⦎ = (
set_goal([], ⌜∀x y z:ℂ⦁
	y + x = x + y
∧	(x + y) + z = x + y + z
∧	y + x + z = x + y + z	⌝);
a(REPEAT ∀_tac THEN rewrite_tac[ℂ_plus_assoc_thm]);
a(rewrite_tac[∀_elim⌜y⌝ ℂ_plus_comm_thm, ℂ_plus_assoc_thm]);
save_pop_thm"ℂ_plus_order_thm"
);

=TEX

%%%%
%%%%
=SML
val ⦏ℂ_eq_thm⦎ = (
set_goal([], ⌜∀ x y : ℂ ⦁ x = y ⇔ x + ~y = ℕℂ 0⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[ℂ_plus_minus_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜(x + ~ y) + y = ℕℂ 0 + y⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(rewrite_tac[ℂ_plus_assoc_thm, ℂ_plus_minus_thm, ℂ_plus_0_thm]);
save_pop_thm"ℝ_eq_thm"
);
=TEX

%%%%
%%%%
=SML

val ⦏ℂ_minus_clauses⦎ = (
set_goal([], ⌜∀x y : ℂ⦁
		~ (~ x) = x
	∧	x + ~ x = ℕℂ 0
	∧	~ x + x = ℕℂ 0
	∧	~ (x + y) = ~ x + ~ y
	∧ 	~(ℕℂ 0) = (ℕℂ 0)⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[ℂ_plus_minus_thm]);
a(lemma_tac⌜∀x:ℂ⦁~(~ x) = x⌝);
(* *** Goal "1" *** *)
a(strip_tac THEN once_rewrite_tac[ℂ_eq_thm]);
a(rewrite_tac[ℂ_plus_minus_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[] THEN strip_tac);
(* *** Goal "2.1" *** *)
a(conv_tac eq_sym_conv THEN once_rewrite_tac[ℂ_eq_thm]);
a(asm_rewrite_tac[∀_elim⌜~ y⌝ℂ_plus_order_thm]);
a(rewrite_tac[∀_elim⌜y⌝ℂ_plus_order_thm, ℂ_plus_minus_thm, ℂ_plus_0_thm]);
(* *** Goal "2.2" *** *)
a(conv_tac eq_sym_conv THEN once_rewrite_tac[ℂ_eq_thm]);
a(asm_rewrite_tac[ℂ_plus_0_thm]);
save_pop_thm"ℂ_minus_clauses"
);

=TEX

%%%%
%%%%
=SML


val ⦏ℂ_plus_clauses⦎ = (
set_goal([], ⌜
	∀ x y z:ℂ⦁
	(x + z = y + z ⇔ x = y)
∧	(z + x = y + z ⇔ x = y)
∧	(x + z = z + y ⇔ x = y)
∧	(z + x = z + y ⇔ x = y)
∧	(x + z = z ⇔ x = ℕℂ 0)
∧	(z + x = z ⇔ x = ℕℂ 0)
∧	(z = z + y ⇔ y = ℕℂ 0)
∧	(z = y + z ⇔ y = ℕℂ 0)
∧	x + ℕℂ 0 = x
∧	ℕℂ 0 + x = x
∧	¬ ℕℂ 1 = ℕℂ 0
∧	¬ ℕℂ 0 = ℕℂ 1
⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[ℂ_plus_0_thm, ℕℂ_one_one_thm, plus_clauses,
	∀_elim⌜z⌝ ℂ_plus_order_thm]);
a(once_rewrite_tac[∀_elim⌜z + x⌝ ℂ_eq_thm]);
a(once_rewrite_tac[∀_elim⌜z⌝ ℂ_eq_thm]);
a(rewrite_tac[ℂ_minus_clauses, ∀_elim⌜~ z⌝ ℂ_plus_order_thm]);
a(rewrite_tac[ℂ_plus_assoc_thm1, ℂ_minus_clauses, ℂ_plus_0_thm]);
a(once_rewrite_tac[∀_elim⌜x⌝ ℂ_eq_thm]);
a(rewrite_tac[]);
a(conv_tac(LEFT_C eq_sym_conv));
a(once_rewrite_tac[∀_elim⌜ℕℂ 0⌝ ℂ_eq_thm]);
a(rewrite_tac[ℂ_minus_clauses, ℂ_plus_0_thm]);
save_pop_thm"ℂ_plus_clauses"
);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_order_thm⦎ = (
set_goal([], ⌜∀ x : ℂ ⦁ ∀ y z ⦁
		y * x = x * y
	∧	(x * y) * z = x * y * z
	∧	y * x * z = x * y * z⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [list_∀_elim [⌜y⌝,⌜x⌝] ℂ_times_comm_thm]);
(* *** Goal "2" *** *)
a (rewrite_tac [all_∀_elim ℂ_times_assoc_thm]);
(* *** Goal "3" *** *)
a (rewrite_tac [list_∀_elim [⌜y⌝,⌜x⌝,⌜z⌝] ℂ_times_assoc_thm1]);
a (once_rewrite_tac [list_∀_elim [⌜y⌝,⌜x⌝] ℂ_times_comm_thm]);
a (rewrite_tac [ℂ_times_assoc_thm]);
save_pop_thm "ℂ_times_order_thm"
);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_0_thm1⦎ = (
set_goal([], ⌜∀x:ℂ⦁ x * ℕℂ 0 = ℕℂ 0⌝);
a(accept_tac(
	all_∀_intro
	(rewrite_rule[ℂ_plus_clauses, ℂ_plus_0_thm](prove_rule[ℂ_times_plus_distrib_thm]
	⌜x*(ℕℂ 0 + ℕℂ 0) = x * ℕℂ 0 + x * ℕℂ 0⌝))));
pop_thm()
);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_0_thm⦎ = (
set_goal([], ⌜∀x:ℂ⦁ x * ℕℂ 0 = ℕℂ 0 ∧ ℕℂ 0 * x = ℕℂ 0⌝);
a(rewrite_tac[∀_elim⌜x:ℂ⌝ℂ_times_order_thm, ℂ_times_0_thm1]);
save_pop_thm "ℂ_times_0_thm"
);

=TEX
=SML
val ⦏ℂ_times_eq_0_thm⦎ = save_thm( "ℂ_times_eq_0_thm", (
set_goal([], ⌜
	∀x y:ℂ⦁ x*y = ℕℂ 0 ⇒ x = ℕℂ 0 ∨ y = ℕℂ 0
⌝);
a(contr_tac THEN all_fc_tac[ℂ_times_recip_thm1]);
a(LEMMA_T⌜y = (x ⋏-⋏1 * x) * y⌝ ante_tac THEN1 asm_rewrite_tac[]
	THEN rewrite_tac[ℂ_times_assoc_thm, ℂ_times_1_thm]
	THEN asm_rewrite_tac[ℂ_times_0_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_clauses⦎ = (
set_goal ([], ⌜∀ x ⦁ ℕℂ 0 * x = ℕℂ 0 ∧ x * ℕℂ 0 = ℕℂ 0 ∧ x * ℕℂ 1 = x ∧ ℕℂ 1 * x = x⌝);
a(rewrite_tac[ℂ_times_0_thm, ℂ_times_1_thm]);
save_pop_thm "ℂ_times_clauses"
);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_minus_thm1⦎ = (
set_goal([], ⌜∀x y:ℂ⦁ x * ~ y = ~(x * y)⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜x * ~ y + x * y = ℕℂ 0⌝);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜x * ~ y + x * y = x * (~y + y)⌝ rewrite_thm_tac
	THEN1 rewrite_tac[ℂ_times_plus_distrib_thm]);
a(rewrite_tac[ℂ_minus_clauses, ℂ_times_0_thm1]);
(* *** Goal "2" *** *)
a(once_rewrite_tac[ℂ_eq_thm]);
a(asm_rewrite_tac[ℂ_minus_clauses]);
pop_thm()
);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_minus_thm⦎ = (
set_goal([], ⌜∀x y:ℂ⦁ ~x * y = ~(x * y) ∧ x * ~ y = ~(x * y) ∧ ~x * ~y = x * y⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[∀_elim⌜y⌝ℂ_times_order_thm]);
a(rewrite_tac[ℂ_times_minus_thm1]);
a(rewrite_tac[∀_elim⌜y⌝ℂ_times_order_thm]);
a(rewrite_tac[ℂ_times_minus_thm1, ℂ_minus_clauses]);
save_pop_thm"ℂ_times_minus_thm"
);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_ℕ_exp_1_thm⦎ = (
set_goal ([], ⌜∀ n : ℕ ⦁ ℕℂ 1^n = ℕℂ 1⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝
	THEN asm_rewrite_tac[ℂ_ℕ_exp_def, ℂ_times_clauses]);
save_pop_thm "ℂ_ℕ_exp_1_thm"
);

=TEX

Note the following is primarily intended for the case when the exponent is a numeric literal (and will loop unless used with care).

%%%%
%%%%
=SML

val ⦏ℂ_ℕ_exp_rw_thm⦎ = (
set_goal ([], ⌜∀ z :ℂ; n : ℕ⦁ z^n = if n = 0 then ℕℂ 1 else z * z^(n-1)⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝
	THEN asm_rewrite_tac[ℂ_ℕ_exp_def]);
save_pop_thm "ℂ_ℕ_exp_rw_thm"
);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_ℕ_exp_plus_thm⦎ = (
set_goal ([], ⌜∀ z :ℂ; m n : ℕ⦁ z^(m+n) = z^m * z^n⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝
	THEN asm_rewrite_tac[ℂ_ℕ_exp_def, plus_assoc_thm1, ℂ_times_clauses]);
a(rewrite_tac[∀_elim⌜z⌝ ℂ_times_order_thm]);
save_pop_thm "ℂ_ℕ_exp_plus_thm"
);

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_ℕ_exp_clauses⦎ = (
set_goal ([], ⌜∀ z :ℂ; n : ℕ ⦁ z^0 = ℕℂ 1 ∧ z^1 = z ∧ ℕℂ 1^n = ℕℂ 1⌝);
a(rewrite_tac[ℂ_ℕ_exp_1_thm]);
a(once_rewrite_tac[ℂ_ℕ_exp_rw_thm] THEN rewrite_tac[]);
a(once_rewrite_tac[ℂ_ℕ_exp_rw_thm] THEN rewrite_tac[ℂ_times_clauses]);
save_pop_thm "ℂ_ℕ_exp_clauses"
);

=TEX
\subsection{A Proof Context}
\section{PROOF CONTEXT}

=TEX

=SML
fun ⦏thms_to_eqn_cxt⦎ (thms:THM list) : EQN_CXT = (
	flat(map (cthm_eqn_cxt (current_ad_rw_canon())) thms)
);
=TEX
=SML
val _ = delete_pc "'ℂ" handle Fail _ => ();
val _ = new_pc "'ℂ";
(*
val _ = set_rw_eqn_cxt
		[	(⌜x +⋎R y⌝, ℝ_plus_conv),
			(⌜x *⋎R y⌝, ℝ_times_conv),
			(⌜x -⋎R y⌝, ℝ_subtract_conv),
			(⌜Abs⋎R x⌝, ℝ_abs_conv),
			(⌜x /⋎R y⌝, ℝ_over_conv),
			(⌜x ⋏-⋏1⌝, ℝ_recip_conv),
			(⌜x ^⋎N m⌝, ℝ_ℕ_exp_conv),
			(⌜x ^⋎Z i⌝, ℝ_ℤ_exp_conv),
			(⌜(x:ℝ) = y⌝, ℝ_eq_conv),
			(⌜x ≤⋎R y⌝, ℝ_≤_conv),
			(⌜x <⋎R y⌝, ℝ_less_conv),
			(⌜x ≥⋎R y⌝, ℝ_≥_conv),
			(⌜x >⋎R y⌝, ℝ_greater_conv),
			(⌜m /⋎N m⌝, ℝ_frac_norm_conv),
			(⌜Float x p (ℕℤ 0)⌝, float_conv),
			(⌜Max⋎R [x]⌝, ℝ_max_conv),
			(⌜Max⋎R (Cons x (Cons y z))⌝, ℝ_max_conv),
			(⌜Min⋎R [x]⌝, ℝ_min_conv),
			(⌜Min⋎R (Cons x (Cons y z))⌝, ℝ_min_conv)
		] "'ℂ";
*)
val _ = add_rw_thms [ℂ_plus_clauses, ℂ_minus_clauses, ℂ_times_clauses, ℂ_ℕ_exp_clauses]
	"'ℂ";
(*
val ⦏pos⦎ = (thms_to_eqn_cxt [ℝ_minus_clauses, ℝ_≤_clauses, ℝ_less_clauses]) @
		[	(⌜(x:ℝ) = y⌝, ℝ_eq_conv),
			(⌜x ≥⋎R y⌝, ℝ_≥_conv),
			(⌜x >⋎R y⌝, ℝ_greater_conv)];
val ⦏neg⦎ = mapfilter (mk_¬ ** RAND_C) pos;
val ⦏neutral⦎ = [(⌜x ≤⋎R y⌝, ℝ_≤_conv), (⌜x <⋎R y⌝, ℝ_less_conv)];
val ⦏strip_eqn_cxt⦎ = neutral @ pos @ neg;
val _ = set_st_eqn_cxt strip_eqn_cxt "'ℂ";
val _ = set_sc_eqn_cxt strip_eqn_cxt "'ℂ";
*)

val _ = set_pr_tac basic_prove_tac "'ℂ";
val _ = set_pr_conv basic_prove_conv "'ℂ";

(*
val _ = commit_pc "'ℂ";
*)

val _ = set_merge_pcs["basic_hol1", "'ℤ", "'ℝ", "'sets_alg", "'ℂ"];
=TEX
\subsection{Additive and Multiplicative Group Properties}
=TEX
=SML
set_goal([], ⌜
	ℂ⋎+ ∈ Group
⌝);
a(rewrite_tac[ℂ_additive_def, group_def, group_ops_def, ℂ_plus_assoc_thm]);
val ⦏ℂ_additive_group_thm⦎ = save_pop_thm "ℂ_additive_group_thm";



=TEX
=SML
set_goal([], ⌜
	ℂ⋎* ∈ Group
⌝);
a(rewrite_tac[ℂ_multiplicative_def, group_def, group_ops_def, ℂ_times_assoc_thm]);
a(contr_tac THEN fc_tac[ℂ_times_eq_0_thm, ℂ_times_recip_thm1, ℂ_times_recip_thm]);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val ⦏ℂ_multiplicative_group_thm⦎ = save_pop_thm "ℂ_multiplicative_group_thm";

=TEX
=SML
set_goal([], ⌜
	Car ℂ⋎+ = Universe
∧	(∀x y:ℂ⦁ (x . y) ℂ⋎+ = x + y)
∧	Unit ℂ⋎+ = ℕℂ 0
∧	(∀x:ℂ⦁ (x ⋏~) ℂ⋎+ = ~x)
⌝);
a(rewrite_tac[ℂ_additive_def, group_ops_def]);
val ⦏ℂ_additive_ops_thm⦎ = save_pop_thm "ℂ_additive_ops_thm";
=TEX
=SML
set_goal([], ⌜
	Car ℂ⋎* = {x | ¬x = ℕℂ 0}
∧	(∀x y:ℂ⦁ (x . y) ℂ⋎* = x * y)
∧	Unit ℂ⋎* = ℕℂ 1
∧	(∀x:ℂ⦁ (x ⋏~) ℂ⋎* = x ⋏-⋏1)
⌝);
a(rewrite_tac[ℂ_multiplicative_def, group_ops_def]);
val ⦏ℂ_multiplicative_ops_thm⦎ = save_pop_thm "ℂ_multiplicative_ops_thm";

=TEX
=SML
set_goal([], ⌜ℂ⋎+ = ℝ⋎+ ×⋎G ℝ⋎+⌝);
a(rewrite_tac[group_eq_group_thm]);
a(rewrite_tac[ℂ_additive_def, group_ops_def, ×_group_def, ℝ_additive_ops_thm]);
a(rewrite_tac[ℂ_plus_def, ℂ_minus_def, ℕℂ_def, ℝℂ_def, ×_def]);
a(PC_T1"sets_ext1" rewrite_tac[]);
val ⦏ℂ_eq_ℝ_×_ℝ_thm⦎ = save_pop_thm "ℂ_eq_ℝ_×_ℝ_thm";

=TEX
=SML
val ⦏ℂ_additive_ℂ_multiplicative_homomorphism_def⦎ =
	save_thm("ℂ_additive_ℂ_multiplicative_homomorphism_def",
		rewrite_rule[ℂ_multiplicative_ops_thm, ℂ_additive_ops_thm]
			 (list_∀_elim[⌜ℂ⋎+⌝, ⌜ℂ⋎*⌝] homomorphism_def));

=TEX
=SML
set_goal([], ⌜
	Exp ∈ Homomorphism(ℂ⋎+, ℂ⋎*)
⌝);
a(rewrite_tac[ ℂ_additive_ℂ_multiplicative_homomorphism_def]);
a(conv_tac (TOP_MAP_C λ_pair_conv));
a(rewrite_tac[ℂ_exp_def, exp_clauses, ℂ_plus_def, ℂ_times_def, ℝℂ_def, ℕℂ_def,
	sin_cos_plus_thm]);
a(conv_tac (MAP_C ℝ_anf_conv));
a(contr_tac);
a(lemma_tac⌜¬Exp x1 = 0.⌝ THEN1 rewrite_tac[exp_¬_eq_0_thm]);
a(fc_tac[ℝ_times_eq_0_thm]);
a(ante_tac(∀_elim⌜x2⌝ cos_squared_plus_sin_squared_thm));
a(asm_rewrite_tac[]);
val ⦏ℂ_exp_homomorphism_thm⦎ = save_pop_thm "ℂ_exp_homomorphism_thm";

=TEX
=SML
set_goal([], ⌜∀c⦁
	(λx⦁c * x) ∈ Homomorphism(ℂ⋎+, ℂ⋎+)
⌝);
a(rewrite_tac[ℂ_additive_def, group_ops_def, homomorphism_def, ℂ_times_plus_distrib_thm]);
val ⦏ℂ_linear_homomorphism_thm⦎ = save_pop_thm "ℂ_linear_homomorphism_thm";


=TEX
\subsection{de Moivre's Theorem}

%%%%
%%%%
=SML

val ⦏de_moivre_thm⦎ = save_thm( "de_moivre_thm", (
set_goal([], ⌜∀ x m⦁
	(Cos x, Sin x) ^ m =
	(Cos (ℕℝ m * x), Sin (ℕℝ m * x))
⌝);
a(REPEAT ∀_tac THEN induction_tac⌜m:ℕ⌝
	THEN asm_rewrite_tac 
	(sin_def::ℕℝ_plus_homomorphism_thm::
		ℝ_times_plus_distrib_thm::
		sin_cos_plus_thm::ℂ_ops_defs));
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
\subsection{Polynomials}

The following is useful for evaluaating partial sums of series of specific known length:
%%%%
%%%%
=SML

val ⦏ℂ_series_rw_thm⦎ = save_thm ("ℂ_series_rw_thm", (
set_goal([], ⌜∀s n⦁ Series⋎C s n = if n = 0 then ℕℂ 0 else s (n-1) + Series⋎C s (n-1)⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝
	THEN asm_rewrite_tac[ℂ_series_def]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML
val ⦏ℂ_poly_eval_rec_thm⦎ = save_thm( "ℂ_poly_eval_rec_thm", (
set_goal([], ⌜
	(∀s z⦁ PolyEval⋎C (s, 0) z = s 0)
∧	(∀s n z⦁ PolyEval⋎C (s, (n+1)) z = PolyEval⋎C (s, n) z + s(n+1) * z^(n+1))
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[ℂ_poly_eval_def]);
a(REPEAT (once_rewrite_tac[ℂ_series_rw_thm] THEN rewrite_tac[]));
(* *** Goal "2" *** *)
a(rewrite_tac[ℂ_poly_eval_def]);
a(conv_tac (LEFT_C (once_rewrite_conv[ℂ_series_def])));
a(rewrite_tac[]);
pop_thm()
));


=TEX


%%%%
%%%%
=SML


val ⦏ℂ_poly_eval_eq_thm1⦎ = save_thm( "ℂ_poly_eval_eq_thm1", (
set_goal([], ⌜∀s t m z⦁
	(∀i⦁ i ≤ m ⇒ s i = t i)
⇒	PolyEval⋎C (s, m) z = PolyEval⋎C (t, m) z
⌝);
a(REPEAT ∀_tac THEN induction_tac⌜m:ℕ⌝
	THEN asm_rewrite_tac[ℂ_poly_eval_rec_thm]);
(* *** Goal "1" *** *)
a(STRIP_T bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(STRIP_T (strip_asm_tac o ∀_elim⌜i⌝)
	THEN i_contr_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(STRIP_T (strip_asm_tac o ∀_elim⌜m+1⌝) THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX


%%%%
%%%%
=SML


val ⦏ℂ_poly_eval_eq_thm2⦎ = save_thm( "ℂ_poly_eval_eq_thm2", (
set_goal([], ⌜∀s m n z⦁
	(∀i⦁ m < i ⇒ s i = ℕℂ 0)
∧	m ≤ n
⇒	PolyEval⋎C (s, m) z = PolyEval⋎C (s, n) z
⌝);
a(REPEAT ∀_tac THEN induction_tac⌜n:ℕ⌝
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[ℂ_poly_eval_rec_thm]);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜m = n + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℂ_poly_eval_rec_thm]);
(* *** Goal "3" *** *)
a(cases_tac⌜m < n + 1⌝ THEN1 ALL_ASM_FC_T rewrite_tac[]);
a(lemma_tac⌜m = n + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 5 ante_tac THEN all_var_elim_asm_tac1);
a(rewrite_tac[ℂ_poly_eval_rec_thm]);
pop_thm()
));


=TEX


%%%%
%%%%
=SML

val ⦏ℂ_poly_eval_eq_thm⦎ = save_thm( "ℂ_poly_eval_eq_thm", (
set_goal([], ⌜∀s t m n z⦁
	(∀i⦁ i ≤ m ⇒ s i = t i)
∧	(∀i⦁ m < i ⇒ t i = ℕℂ 0)
∧	m ≤ n
⇒	PolyEval⋎C (s, m) z = PolyEval⋎C (t, n) z
⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜PolyEval⋎C (t, n) z = PolyEval⋎C (t, m) z⌝ rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[ℂ_poly_eval_eq_thm2]);
a(bc_thm_tac ℂ_poly_eval_eq_thm1 THEN asm_rewrite_tac[]);
pop_thm()
));


=TEX


%%%%
%%%%
=SML


val ⦏ℂ_poly_eval_0_thm⦎ = save_thm( "ℂ_poly_eval_0_thm", (
set_goal([], ⌜∀n z⦁
	PolyEval⋎C ((λi⦁ℕℂ 0), n) z = ℕℂ 0
⌝);
a(REPEAT ∀_tac THEN induction_tac⌜n:ℕ⌝
	THEN asm_rewrite_tac[ℂ_poly_eval_rec_thm]);
pop_thm()
));


=TEX


%%%%
%%%%
=SML


val ⦏ℂ_poly_eval_minus_thm⦎ = save_thm( "ℂ_poly_eval_minus_thm", (
set_goal([], ⌜∀s n z⦁
	PolyEval⋎C ((λi⦁~(s i)), n) z = ~(PolyEval⋎C (s, n) z)
⌝);
a(REPEAT ∀_tac THEN induction_tac⌜n:ℕ⌝
	THEN asm_rewrite_tac[ℂ_poly_eval_rec_thm]);
a(rewrite_tac[ℂ_times_minus_thm]);
pop_thm()
));


=TEX


%%%%
%%%%
=SML


val ⦏ℂ_poly_eval_plus_thm⦎ = save_thm( "ℂ_poly_eval_plus_thm", (
set_goal([], ⌜∀s t n z⦁
	PolyEval⋎C ((λi⦁s i + t i), n) z =
	PolyEval⋎C (s, n) z + PolyEval⋎C (t, n) z
⌝);
a(REPEAT ∀_tac THEN induction_tac⌜n:ℕ⌝
	THEN asm_rewrite_tac[ℂ_poly_eval_rec_thm]);
a(rewrite_tac[ℂ_plus_assoc_thm,
	∀_elim⌜PolyEval⋎C (s, n) z⌝ ℂ_plus_order_thm,
	ℂ_times_plus_distrib_thm]);
a(rewrite_tac[∀_elim⌜PolyEval⋎C (t, n) z⌝ ℂ_plus_order_thm]);
pop_thm()
));

=TEX


%%%%
Now we will show that any polynomial function can be represented by a finite power series.

Constants \ldots
%%%%
%%%%
=SML

val ⦏ℂ_const_eval_thm⦎ = save_thm( "ℂ_const_eval_thm", (
set_goal([], ⌜∀c⦁(λx⦁c) = PolyEval⋎C ((λi⦁c), 0)⌝);
a(rewrite_tac[] THEN pure_rewrite_tac[ℂ_poly_eval_def, ℂ_series_def]);
a(rewrite_tac ℂ_ops_defs);
pop_thm()
));

=TEX
\ldots identity function \ldots
%%%%
%%%%
=SML

val ⦏ℂ_id_eval_thm⦎ = save_thm( "ℂ_id_eval_thm", (
set_goal([], ⌜(λx⦁x) = PolyEval⋎C ((λi⦁if i = 1 then ℕℂ 1 else ℕℂ 0), 1)⌝);
a(rewrite_tac[ℂ_poly_eval_def]);
a(REPEAT (once_rewrite_tac[ℂ_series_rw_thm] THEN rewrite_tac[]));
pop_thm()
));

=TEX
\ldots sums \ldots
%%%%
%%%%
=SML

=TEX
\ldots sums \ldots
%%%%
%%%%
=SML

val ⦏ℂ_plus_eval_thm⦎ = save_thm( "ℂ_plus_eval_thm", (
set_goal([], ⌜∀s m t n⦁
	(λx⦁ PolyEval⋎C (s, m) x + PolyEval⋎C (t, n) x) =
	PolyEval⋎C (PlusCoeffs⋎C (s, m) (t, n))⌝);
a(REPEAT strip_tac THEN rewrite_tac[ℂ_plus_coeffs_def]);
a(EXTEND_PC_T1 "'sho_rw" pure_rewrite_tac[ℂ_poly_eval_plus_thm]);
a(bc_tac [prove_rule[]⌜∀a b c d:ℂ⦁a = c ∧ b = d ⇒ a + b = c + d⌝,
	ℂ_poly_eval_eq_thm]
	THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1" (duplicates "2") *** *)
a(LEMMA_T ⌜¬i ≤ m⌝ asm_rewrite_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));
=TEX
which we can usefully reformulate thus
%%%%
%%%%
=SML

val ⦏ℂ_plus_eval_rw_thm⦎ = save_thm( "ℂ_plus_eval_rw_thm", (
set_goal([], ⌜∀sm tn⦁
	PolyEval⋎C (PlusCoeffs⋎C sm tn) =
	(λx⦁ PolyEval⋎C sm x + PolyEval⋎C tn x) ⌝);
a(REPEAT strip_tac);
a(pair_tac⌜sm = (s, m)⌝ THEN pair_tac⌜tn = (t, n)⌝);
a(rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv) ℂ_plus_eval_thm]);
pop_thm()
));

=TEX
\ldots and products, which in this case require a little lemma first:
%%%%
%%%%
=SML

val ⦏ℂ_const_times_eval_thm⦎ = save_thm( "ℂ_const_times_eval_thm", (
set_goal([], ⌜∀c s m⦁ PolyEval⋎C ((λi⦁c * s i), m) = (λx⦁c * PolyEval⋎C (s, m) x)⌝);
a(REPEAT strip_tac);
a(induction_tac⌜m⌝ THEN asm_rewrite_tac[ℂ_poly_eval_rec_thm]);
a(rewrite_tac ℂ_ops_defs THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℂ_times_eval_thm⦎ = save_thm( "ℂ_times_eval_thm", (
set_goal([], ⌜∀s m t n⦁
	(λx⦁PolyEval⋎C (s, m) x * PolyEval⋎C (t, n) x) =
	PolyEval⋎C (TimesCoeffs⋎C (s, m) (t, n))⌝);
a(REPEAT strip_tac THEN rewrite_tac[]);
a(induction_tac⌜m⌝ THEN
	rewrite_tac[ℂ_times_coeffs_def, ℂ_poly_eval_rec_thm, ℂ_const_times_eval_thm]
	THEN REPEAT strip_tac);
a(asm_rewrite_tac[ℂ_times_plus_distrib_thm, ℂ_plus_eval_rw_thm]);
a(POP_ASM_T discard_tac THEN induction_tac⌜n⌝ THEN REPEAT strip_tac THEN
	asm_rewrite_tac[ℂ_poly_eval_rec_thm]);
(* *** Goal "1" *** *)
a(rewrite_tac[∀_elim⌜t 0⌝ ℂ_times_order_thm]);
a(LEMMA_T ⌜ℕℂ 0 = PolyEval⋎C ((λi⦁ ℕℂ 0), m) x⌝
	(fn th => conv_tac(RIGHT_C (once_rewrite_conv[th])))
	THEN1 rewrite_tac[ℂ_poly_eval_0_thm]);
a(conv_tac eq_sym_conv THEN bc_thm_tac ℂ_poly_eval_eq_thm1
	THEN REPEAT strip_tac
	THEN1 asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[ℂ_times_plus_distrib_thm, ℂ_poly_eval_rec_thm,
	pc_rule1 "lin_arith" prove_rule[]
		⌜m + (n + 1) + 1 = (m + n + 1) + 1⌝]);
a(asm_rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
		⌜(m + n + 1) + 1 = m + n + 2⌝]);
a(rewrite_tac[minus_def, pc_rule1 "lin_arith" prove_rule[]
		⌜m + n + 2 = (m+1) + (n+1)⌝]);
a(rewrite_tac[ℂ_ℕ_exp_plus_thm]);
a(rewrite_tac[ℂ_times_assoc_thm, ∀_elim⌜t(n+1)⌝ ℂ_times_order_thm]);
pop_thm()
));

=TEX
which we can usefully reformulate thus
%%%%
%%%%
=SML

val ⦏ℂ_times_eval_rw_thm⦎ = save_thm( "ℂ_times_eval_rw_thm", (
set_goal([], ⌜∀sm tn⦁
	PolyEval⋎C (TimesCoeffs⋎C sm tn) =
	(λx⦁ PolyEval⋎C sm x * PolyEval⋎C tn x) ⌝);
a(REPEAT strip_tac);
a(pair_tac⌜sm = (s, m)⌝ THEN pair_tac⌜tn = (t, n)⌝);
a(rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv) ℂ_times_eval_thm]);
pop_thm()
));


=TEX
Following what we did for the reals,
we now show that the set of all complex polynomial functions is the
range of the polynomial evaluation function. I.e., a function
is polynomial iff. it can be represented by a sequence of coefficients
and a degree.
We prove the two inclusions separately:
%%%%
%%%%
=SML


val ⦏ℂ_poly_eval_⊆_poly_thm⦎ = (
set_goal([], ⌜{f | ∃s n⦁ f = PolyEval⋎C (s, n)} ⊆ PolyFunc⋎C⌝);
a(pure_rewrite_tac[ℂ_poly_func_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN induction_tac⌜n⌝);
(* *** Goal "1" *** *)
a(conv_tac (LEFT_C un_η_conv));
a(pure_rewrite_tac[ℂ_poly_eval_rec_thm] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(conv_tac (LEFT_C un_η_conv));
a(pure_rewrite_tac[ℂ_poly_eval_rec_thm]);
a(GET_NTH_ASM_T 3 ho_bc_thm_tac THEN asm_rewrite_tac[η_axiom]);
a(GET_NTH_ASM_T 2 ho_bc_thm_tac THEN asm_rewrite_tac[]);
a(rewrite_tac[ℂ_ℕ_exp_def]
	THEN POP_ASM_T discard_tac THEN induction_tac⌜n⌝
	THEN asm_rewrite_tac[ℂ_ℕ_exp_def]);
a(GET_NTH_ASM_T 2 ho_bc_thm_tac THEN asm_rewrite_tac[]);
pop_thm ()
);


=TEX
For the reverse inclusion, and for later use, it is convenient
to prove an induction theorem for polynomials and use it
to derive an induction tactic:
%%%%
%%%%
=SML

val ⦏ℂ_poly_induction_thm⦎ = save_thm( "ℂ_poly_induction_thm", (
set_goal([], ⌜∀p⦁
		(∀c⦁p(λx⦁c))
	∧	(p(λx⦁x))
	∧	(∀f g⦁p f ∧ p g ⇒  p(λx⦁f x + g x))
	∧	(∀f g⦁p f ∧ p g ⇒ p(λx⦁f x * g x))
	⇒	(∀h⦁ h ∈ PolyFunc⋎C ⇒ p h)
⌝);
a(rewrite_tac[ℂ_poly_func_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(PC_T1 "sets_ext1" POP_ASM_T (strip_asm_tac o ∀_elim ⌜{h | p h}⌝)
	THEN1 asm_prove_tac[] THEN all_asm_fc_tac[]);
pop_thm()
));


=TEX
Now the tactic, which expects a term of the form $f \in \mbox{\it PolyFunc}_C$ to
be in the assumptions (where $f$ is the induction variable).
%%%%
%%%%
=SML

fun ⦏ℂ_poly_induction_tac⦎ (tm : TERM) : TACTIC = (
	if not (is_var tm andalso type_of tm =: ⓣℂ → ℂ⌝)
	then term_fail "ℂ_poly_induction_tac" 999001 [tm]
	else ( fn(asms, conc) =>
	let	val asm = find asms (fn t =>  
			let	val (x, s) = dest_bin_op "" 0 "∈" t;
			in	x =$ tm andalso s =$ ⌜PolyFunc⋎C⌝
			end	handle Fail _ => false)
			handle Fail _ => fail "ℂ_poly_induction_tac" 999002 [];
	in	if not (is_free_in tm conc)
			then term_fail "ℂ_poly_induction_tac" 999003 [tm]
		else if any (asms drop (fn t => t =$ asm)) (is_free_in tm)
			then term_fail "ℂ_poly_induction_tac" 999004 [tm]
		else	(asm_ante_tac asm THEN gen_induction_tac1 ℂ_poly_induction_thm) (asms, conc)
	end
	)
);



=TEX


%%%%
%%%%
=SML

val ⦏ℂ_poly_⊆_poly_eval_thm⦎ = (
set_goal([], ⌜PolyFunc⋎C ⊆ {f | ∃s n⦁ f = PolyEval⋎C (s, n)}⌝);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(ℂ_poly_induction_tac⌜x⌝);
(* *** Goal "1" *** *)
a(ante_tac ℂ_const_eval_thm THEN prove_tac[]);
(* *** Goal "2" *** *)
a(ante_tac ℂ_id_eval_thm THEN prove_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜Fst(PlusCoeffs⋎C (s, n) (s', n'))⌝ THEN ∃_tac⌜Snd(PlusCoeffs⋎C (s, n) (s', n'))⌝
	THEN rewrite_tac[]);
a(asm_rewrite_tac[ℂ_plus_eval_rw_thm]);
(* *** Goal "4" *** *)
a(∃_tac⌜Fst(TimesCoeffs⋎C (s, n) (s', n'))⌝ THEN ∃_tac⌜Snd(TimesCoeffs⋎C (s, n) (s', n'))⌝
	THEN rewrite_tac[]);
a(asm_rewrite_tac[ℂ_times_eval_rw_thm]);
pop_thm ()
);

=TEX


%%%%
%%%%
=SML

val ⦏ℂ_poly_func_eq_poly_eval_thm⦎ = save_thm( "ℂ_poly_func_eq_poly_eval_thm", (
set_goal([], ⌜PolyFunc⋎C = {f | ∃s n⦁ f = PolyEval⋎C (s, n)}⌝);
a(rewrite_tac[ℂ_poly_⊆_poly_eval_thm, ℂ_poly_eval_⊆_poly_thm,
	pc_rule1 "sets_ext1" prove_rule[] ⌜∀a b⦁a = b ⇔ a ⊆ b ∧ b ⊆ a⌝]);
pop_thm()
));

=TEX
\subsection{Topological Properties}

%%%%
%%%%
=SML

val ⦏open_ℂ_topology_thm⦎ = save_thm( "open_ℂ_topology_thm", (
set_goal([], ⌜
	O⋎C ∈ Topology
⌝);
a(rewrite_tac[open_ℂ_def]);
a(bc_thm_tac product_topology_thm THEN rewrite_tac[open_ℝ_topology_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏open_ℂ_hausdorff_thm⦎ = save_thm( "open_ℂ_hausdorff_thm", (
set_goal([], ⌜
	O⋎C ∈ Hausdorff
⌝);
a(rewrite_tac[open_ℂ_def, open_ℝ_×_open_ℝ_hausdorff_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏universe_open_ℂ_thm⦎ = save_thm( "universe_open_ℂ_thm", (
set_goal([], ⌜
	Universe ∈ O⋎C
⌝);
a(rewrite_tac[open_ℂ_def]);
a(rewrite_tac[product_topology_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜Universe⌝ THEN rewrite_tac[empty_universe_open_closed_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏space_t_open_ℂ_thm⦎ = save_thm( "space_t_open_ℂ_thm", (
set_goal([], ⌜
	Space⋎T O⋎C = Universe
⌝);
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(bc_thm_tac ∈_space_t_thm);
a(∃_tac⌜Universe⌝ THEN PC_T1 "sets_ext1" rewrite_tac[universe_open_ℂ_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏space_t_subspace_open_ℂ_thm⦎ = save_thm ("space_t_subspace_open_ℂ_thm",
	rewrite_rule[open_ℂ_topology_thm, space_t_open_ℂ_thm]
	(∀_elim⌜O⋎C⌝ subspace_topology_space_t_thm));

=TEX

%%%%
%%%%
=SML

val ⦏space_t_subpace_ℂ_thm⦎ = save_thm( "space_t_subpace_ℂ_thm", (
set_goal([], ⌜
	∀A⦁ Space⋎T (A ◁⋎T O⋎C) = A
⌝);
a(ante_tac(∀_elim ⌜O⋎C⌝ subspace_topology_space_t_thm));
a(rewrite_tac[open_ℂ_topology_thm, space_t_open_ℂ_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_minus_continuous_thm⦎ = save_thm( "ℂ_minus_continuous_thm", (
set_goal([], ⌜~ ∈ (O⋎C, O⋎C) Continuous ⌝);
a(LEMMA_T ⌜~ = λz⦁ (~ z : ℂ)⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[uncurry_def]);
a(rewrite_tac[ℂ_minus_def, open_ℂ_def]);
a(ℝ_continuity_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML
val ⦏ℂ_conj_continuous_thm⦎ = save_thm( "ℂ_conj_continuous_thm", (
set_goal([], ⌜$⋏_ ∈ (O⋎C, O⋎C) Continuous ⌝);
a(LEMMA_T ⌜$⋏_ = λz⦁ z ⋏_⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[uncurry_def]);
a(rewrite_tac[ℂ_conj_def, open_ℂ_def]);
a(ℝ_continuity_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_plus_continuous_thm⦎ = save_thm( "ℂ_plus_continuous_thm", (
set_goal([], ⌜Uncurry $+ ∈ (O⋎C ×⋎T O⋎C, O⋎C) Continuous ⌝);
a(LEMMA_T ⌜Uncurry $+ = λ(w, z)⦁ (w + z : ℂ)⌝ rewrite_thm_tac
	THEN1 rewrite_tac[uncurry_def]);
a(rewrite_tac[ℂ_plus_def, open_ℂ_def]);
a(ℝ_continuity_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_times_continuous_thm⦎ = save_thm( "ℂ_times_continuous_thm", (
set_goal([], ⌜Uncurry $* ∈ (O⋎C ×⋎T O⋎C, O⋎C) Continuous ⌝);
a(LEMMA_T ⌜Uncurry $* = λ(w, z)⦁ (w * z : ℂ)⌝ rewrite_thm_tac
	THEN1 rewrite_tac[uncurry_def]);
a(rewrite_tac[ℂ_times_def, open_ℂ_def]);
a(ℝ_continuity_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_ℕ_exp_continuous_thm⦎ = save_thm( "ℂ_ℕ_exp_continuous_thm", (
set_goal([], ⌜∀n⦁ (λx:ℂ⦁ x^n) ∈ (O⋎C, O⋎C) Continuous⌝);
a(rewrite_tac[open_ℂ_def] THEN REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN rewrite_tac[ℂ_ℕ_exp_def]);
(* *** Goal "1" *** *)
a(ℝ_continuity_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[ℂ_times_def] THEN ℝ_continuity_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_poly_continuous_thm⦎ = save_thm( "ℂ_poly_continuous_thm", (
set_goal([], ⌜∀f⦁f ∈ PolyFunc⋎C ⇒ f ∈ (O⋎C, O⋎C) Continuous ⌝);
a(rewrite_tac[open_ℂ_def] THEN REPEAT strip_tac);
a(ℂ_poly_induction_tac ⌜f⌝);
a(ℝ_continuity_tac[]);
(* *** Goal "2" *** *)
a(ℝ_continuity_tac[]);
(* *** Goal "3" *** *)
a(ℝ_continuity_tac[rewrite_rule[open_ℂ_def]ℂ_plus_continuous_thm]);
(* *** Goal "4" *** *)
a(ℝ_continuity_tac[rewrite_rule[open_ℂ_def]ℂ_times_continuous_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℂ_series_continuous_thm⦎ = save_thm( "ℂ_series_continuous_thm", (
set_goal([], ⌜∀σ s n⦁
		σ ∈ Topology
	∧	(∀i⦁ s i ∈ (σ, O⋎C) Continuous)
	⇒	(λx⦁ Series⋎C (λi⦁ s i x) n) ∈ (σ, O⋎C) Continuous ⌝);
a(rewrite_tac[open_ℂ_def] THEN REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN rewrite_tac[ℂ_series_def]);
(* *** Goal "1" *** *)
a(ℝ_continuity_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[ℂ_plus_def] THEN ℝ_continuity_tac[]
	THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏exp_s1_continuous_thm⦎ = save_thm( "exp_s1_continuous_thm", (
set_goal([], ⌜
	ExpS1 ∈ (O⋎R, O⋎C) Continuous
⌝);
a(rewrite_tac[exp_s1_def1, open_ℂ_def]);
a(ℝ_continuity_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℂ_abs_squared_lemma⦎ = save_thm( "ℂ_abs_squared_lemma", (
set_goal([], ⌜∀x y⦁ Sqrt(x^2 + y^2) = 1. ⇔ x^2 + y^2 = 1. ⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜0. ≤ x^2 ∧ 0. ≤ y^2⌝ THEN1 rewrite_tac[ℝ_0_≤_square_thm]);
a(lemma_tac⌜0. ≤ x^2 + y^2⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [2, 3] discard_tac THEN all_fc_tac[sqrt_0_≤_thm, sqrt_thm]);
a(POP_ASM_T (once_rewrite_thm_tac o eq_sym_rule));
a(asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[sqrt_0_1_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML


val ⦏∈_s1_lemma⦎ = save_thm( "∈_s1_lemma", (
set_goal([], ⌜∀z⦁ z ∈ S1 ⇔ Re z^2 + Im z^2 = 1.⌝);
a(MERGE_PCS_T1 ["'pair", "sets_ext1"] rewrite_tac[s1_def, ℂ_abs_def, ℂ_times_conj_thm, ℝℂ_def, ℂ_abs_squared_lemma]);
pop_thm()
));


=TEX
%%%%
%%%%
=SML

val ⦏open_s1_topology_thm⦎ = save_thm ( "open_s1_topology_thm", ( 
set_goal([], ⌜ O⋎S1 ∈ Topology ⌝);
a(rewrite_tac[open_s1_def] THEN basic_topology_tac[open_ℂ_topology_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏space_t_open_s1_thm⦎ = save_thm ( "space_t_open_s1_thm", ( 
set_goal([], ⌜Space⋎T O⋎S1 = S1 ⌝);
a(rewrite_tac[open_s1_def, space_t_subpace_ℂ_thm]);
pop_thm()
));


=TEX
Constant functions are continuous:
%%%%
%%%%

=SML

val ⦏open_ℂ_const_continuous_thm⦎ = save_thm("open_ℂ_const_continuous_thm",
	all_∀_intro(
	rewrite_rule[open_ℂ_topology_thm, space_t_open_ℂ_thm]
	(list_∀_elim[⌜σ : 'a SET SET⌝, ⌜O⋎C⌝] const_continuous_thm)));

=TEX

as is the identity function:
%%%%
%%%%

=SML

val ⦏open_ℂ_id_continuous_thm⦎ = save_thm("open_ℂ_id_continuous_thm",
	rewrite_rule[open_ℂ_topology_thm]
	(∀_elim⌜O⋎C⌝ id_continuous_thm));



=TEX
It is now useful to set up a proof context to eliminate various trivial facts.
%%%%
%%%%

=SML
val _ = delete_pc "'topology_ℂ" handle Fail _ => ();
val _ = new_pc "'topology_ℂ";

val _ = add_rw_thms [
	open_ℂ_topology_thm,
	space_t_open_ℂ_thm,
	open_ℂ_id_continuous_thm,
	(rewrite_rule[open_ℂ_topology_thm] o ∀_elim⌜O⋎C⌝) open_ℂ_const_continuous_thm,
	open_s1_topology_thm,
	space_t_open_s1_thm
	]
	"'topology_ℂ";
local
	fun ⦏thms_to_eqn_cxt⦎ (thms:THM list) : EQN_CXT = (
		flat(map (cthm_eqn_cxt initial_rw_canon) thms)
	);
	val pos_bits = thms_to_eqn_cxt [open_ℂ_topology_thm];
	val neg_strips = map (mk_¬ ** RAND_C) pos_bits;
	val new_strips = pos_bits @ neg_strips;
in
	val _ = set_st_eqn_cxt new_strips "'topology_ℂ";
	val _ = set_sc_eqn_cxt new_strips "'topology_ℂ";

end;

val _ = set_pr_tac basic_prove_tac "'topology_ℂ";
val _ = set_pr_conv basic_prove_conv "'topology_ℂ";

(*
val _ = commit_pc "'topology_ℂ";
*)

val _ = set_merge_pcs["basic_hol1", "'ℤ", "'ℝ", "'sets_alg", "'topology_ℝ", "'topology_ℂ", "'ℂ"];

=TEX

%%%%
%%%%
=SML

val ⦏exp_exp_s1_thm⦎ = save_thm( "exp_exp_s1_thm", (
set_goal([], ⌜ExpS1 = (Exp : ℂ → ℂ) o ℝι⌝);
a(rewrite_tac[ℂ_times_def, o_def, exp_def, ℂ_exp_def, ℝι_def, ℝℂ_def, exp_s1_def]);
pop_thm()
));
=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_homomorphism_thm⦎ = save_thm( "exp_s1_homomorphism_thm", (
set_goal([], ⌜∀x y⦁ ExpS1(x + y) = ExpS1 x * ExpS1 y⌝);
a(rewrite_tac[exp_s1_def, ℂ_times_def, sin_cos_plus_thm]);
pop_thm()
));

val ⦏exp_s1_homomorphism_thm1⦎ = save_thm ("exp_s1_homomorphism_thm1",
	conv_rule(ONCE_MAP_C eq_sym_conv) exp_s1_homomorphism_thm);


=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_minus_thm⦎ = save_thm( "exp_s1_minus_thm", (
set_goal([], ⌜∀x⦁ ExpS1(~x) = ExpS1 x ⋏-⋏1⌝);
a(REPEAT strip_tac THEN bc_thm_tac ℂ_times_eq_1_thm);
a(rewrite_tac[exp_s1_homomorphism_thm1]);
a(rewrite_tac[exp_s1_def, ℕℂ_def, ℝℂ_def, sin_def]);
a(contr_tac THEN ante_tac (∀_elim⌜x⌝ cos_squared_plus_sin_squared_thm));
a(asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
pop_thm()
));


=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_∈_s1_thm⦎ = save_thm( "exp_s1_∈_s1_thm", (
set_goal([], ⌜∀x⦁ ExpS1 x ∈ S1⌝);
a(rewrite_tac[exp_s1_def, ∈_s1_lemma, cos_squared_plus_sin_squared_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_period_thm⦎ = save_thm( "exp_s1_period_thm", (
set_goal([], ⌜∀x y⦁ ExpS1 x = ExpS1 y ⇔ (∃m⦁ y = x + ℕℝ(2*m) * π ∨ x = y + ℕℝ(2*m) * π)⌝);
a(lemma_tac⌜
	(∀x y⦁ x < y ⇒
		(ExpS1 x = ExpS1 y ⇔ (∃m⦁ y = x + ℕℝ(2*m) * π)))
∧	(∀x y m⦁ x < y ⇒ ¬ x = y + ℕℝ (2 * m) * π)
⌝
	THEN1 ∧_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[exp_s1_def,
	taut_rule⌜∀x y p⦁ Cos x = y ∧ p ⇔ p ∧ Cos x = y⌝,
	sin_cos_period_thm]);
(* *** Goal "2" *** *)
a(contr_tac THEN all_var_elim_asm_tac1);
a(lemma_tac ⌜0. ≤ ℕℝ (2 * m) * π⌝ THEN_LIST [
	bc_thm_tac ℝ_0_≤_0_≤_times_thm,
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(rewrite_tac[ℕℝ_≤_thm] THEN rewrite_tac[ℝ_≤_def, π_def]);
(* *** Goal "3" *** *)
a(REPEAT ∀_tac);
a(lemma_tac⌜x = y ∨ x < y ∨ y < x⌝ THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]
	THEN1 (all_var_elim_asm_tac THEN rewrite_tac[]));
(* *** Goal "3.1" *** *)
a(∃_tac⌜0⌝ THEN rewrite_tac[]);
(* *** Goal "3.2" *** *)
a(LIST_DROP_NTH_ASM_T [2, 3] (ALL_FC_T1 fc_⇔_canon rewrite_tac));
(* *** Goal "3.3" *** *)
a(conv_tac(LEFT_C eq_sym_conv));
a(LIST_DROP_NTH_ASM_T [2, 3] (ALL_FC_T1 fc_⇔_canon rewrite_tac));
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_period_thm1⦎ = save_thm( "exp_s1_period_thm1", (
set_goal([], ⌜∀x y⦁ ExpS1 x = ExpS1 y ⇔  ∃i⦁ y = x + 2. * ℤℝ i * π⌝);
a(asm_rewrite_tac[exp_s1_period_thm] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(∃_tac ⌜ℕℤ m⌝ THEN rewrite_tac[ℕℝ_times_homomorphism_thm, ℤℝ_ℕℤ_thm]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac ⌜~(ℕℤ m)⌝ THEN rewrite_tac[ℕℝ_times_homomorphism_thm, ℤℝ_ℕℤ_thm]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "3" *** *)
a((strip_asm_tac o ∀_elim⌜i⌝) ℤ_cases_thm THEN all_var_elim_asm_tac1
	THEN ∃_tac ⌜m⌝ THEN rewrite_tac[ℕℝ_times_homomorphism_thm, ℤℝ_ℕℤ_thm]
		THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML


val ⦏exp_s1_onto_thm⦎ = save_thm( "exp_s1_onto_thm", (
set_goal([], ⌜∀z⦁ z ∈ S1 ⇒ ∃⋎1x⦁ 0. ≤ x ∧ x < 2. * π ∧ z = ExpS1 x⌝);
a(rewrite_tac[∈_s1_lemma, exp_s1_def] THEN REPEAT strip_tac);
a(bc_thm_tac sin_cos_onto_unit_circle_thm1 THEN strip_tac);
pop_thm()
));

=TEX

%%%%
%%%%
=SML


val ⦏s1_times_thm⦎ = save_thm( "s1_times_thm", (
set_goal([], ⌜∀z w⦁ z ∈ S1 ∧ w ∈ S1 ⇒ z*w ∈ S1⌝);
a(REPEAT strip_tac THEN all_fc_tac[exp_s1_onto_thm]
	THEN all_var_elim_asm_tac1);
a(rewrite_tac[exp_s1_homomorphism_thm1, exp_s1_∈_s1_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML


val ⦏exp_s1_onto_thm1⦎ = save_thm( "exp_s1_onto_thm1", (
set_goal([], ⌜∀c z⦁
	z ∈ S1
⇒	∃⋎1x⦁ c - π ≤ x ∧ x < c + π ∧ z = ExpS1 x⌝);
a(REPEAT strip_tac);
a(all_fc_tac[exp_s1_onto_thm] THEN all_var_elim_asm_tac1);
a(lemma_tac⌜ExpS1 (x + π + ~c) ∈ S1⌝ THEN1 rewrite_tac[exp_s1_∈_s1_thm]);
a(strip_asm_tac(∀_elim⌜ExpS1 (x + π + ~c)⌝ exp_s1_onto_thm));
a(∃⋎1_tac⌜x' + c + ~ π⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(once_rewrite_tac[exp_s1_homomorphism_thm]);
a(DROP_NTH_ASM_T 2 (rewrite_thm_tac o eq_sym_rule));
a(rewrite_tac[exp_s1_homomorphism_thm1]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN rewrite_tac[]);
(* *** Goal "4" *** *)
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜x'' = x' + c + ~ π ⇔ x'' + π - c = x'⌝]);
a(DROP_NTH_ASM_T 4 bc_thm_tac);
a(once_rewrite_tac[exp_s1_homomorphism_thm]);
a(asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));


=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_onto_thm2⦎ = save_thm( "exp_s1_onto_thm2", (
set_goal([], ⌜∀c z⦁
	z ∈ S1 ∧¬z = ExpS1 (c + π)
⇒	∃⋎1x⦁x ∈ OpenInterval (c - π) (c + π) ∧ z = ExpS1 x⌝);
a(rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜c⌝, ⌜z⌝]exp_s1_onto_thm1));
a(∃⋎1_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 4 (strip_asm_tac o rewrite_rule[ℝ_≤_def])
	THEN all_var_elim_asm_tac1 THEN REPEAT strip_tac);
a(swap_nth_asm_concl_tac 3);
a(rewrite_tac[exp_s1_period_thm]);
a(∃_tac⌜1⌝ THEN rewrite_tac[]);
a(PC_T1"ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN asm_rewrite_tac[]);
a(PC_T1"ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));


=TEX

%%%%
%%%%
=SML


val ⦏exp_s1_onto_thm3⦎ = save_thm( "exp_s1_onto_thm3", (
set_goal([], ⌜∀z⦁ z ∈ S1 ⇒ ∃x⦁ ExpS1 x = z⌝);
a(REPEAT strip_tac THEN all_fc_tac[exp_s1_onto_thm]);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
pop_thm()
));


=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_covering_projection_lemma1⦎ = save_thm( "exp_s1_covering_projection_lemma1", (
set_goal([], ⌜∀c⦁
	S1 \ {ExpS1 (c + π)} =
	{z | ∃ x⦁ x ∈ OpenInterval (c - π) (c + π) ∧ z = ExpS1 x}⌝);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[exp_s1_onto_thm2]);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[exp_s1_∈_s1_thm]);
(* *** Goal "3" *** *)
a(pure_asm_rewrite_tac[] THEN POP_ASM_T discard_tac);
a(POP_ASM_T ante_tac
	THEN rewrite_tac[open_interval_def]
	THEN strip_tac);
a(ante_tac (list_∀_elim[⌜c⌝, ⌜ExpS1 x⌝] exp_s1_onto_thm1));
a(rewrite_tac[exp_s1_∈_s1_thm] THEN strip_tac);
a(lemma_tac⌜c + ~ π ≤ x⌝ THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(lemma_tac⌜x = x'⌝ THEN1
	(DROP_NTH_ASM_T 2 bc_thm_tac THEN asm_rewrite_tac[])
	THEN all_var_elim_asm_tac1);
a(contr_tac);
a(DROP_NTH_ASM_T 2 (ante_tac o ∀_elim⌜c + ~ π⌝) THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜~ π < π ∧ ¬c + ~ π = x'⌝ rewrite_thm_tac
	THEN1 (strip_asm_tac π_def
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(rewrite_tac[exp_s1_period_thm]);
a(∃_tac⌜1⌝ THEN rewrite_tac[]);
a(strip_asm_tac π_def
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));



=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_covering_projection_lemma2⦎ = save_thm( "exp_s1_covering_projection_lemma2", (
set_goal([], ⌜∀x⦁
	ExpS1 ∈
	(OpenInterval (x - π) (x + π) ◁⋎T O⋎R,
		(S1 \ {ExpS1 (x + π)}) ◁⋎T O⋎C) 
			Homeomorphism
⌝);
a(REPEAT strip_tac);
a(rewrite_tac[exp_s1_covering_projection_lemma1]);
a(bc_thm_tac ⊆_compact_homeomorphism_thm);
a(∃_tac⌜ClosedInterval (x - π) (x + π)⌝);
a(rewrite_tac[open_ℝ_topology_thm, open_ℝ_hausdorff_thm,
	open_ℂ_topology_thm, open_ℂ_hausdorff_thm,
	exp_s1_continuous_thm, compact_compact_ℝ_thm,
	closed_interval_compact_thm]);
a(rewrite_tac[open_interval_def, closed_interval_def]);
a(REPEAT strip_tac THEN1
	(PC_T1 "sets_ext1" rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[ℝ_≤_def]));
(* *** Goal "1" *** *)
a(ante_tac(list_∀_elim[⌜x⌝, ⌜ExpS1 y⌝] exp_s1_onto_thm1)
	THEN rewrite_tac[exp_s1_∈_s1_thm]
	THEN REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜y⌝ THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o eq_sym_rule)); 
a(lemma_tac⌜x + ~ π ≤ x'⌝ THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac THEN all_var_elim_asm_tac);
(* *** Goal "2" *** *)
a(i_contr_tac THEN all_var_elim_asm_tac1);
a(POP_ASM_T (strip_asm_tac o eq_sym_rule));
a(ante_tac(list_∀_elim[⌜x' + π⌝, ⌜ExpS1 (x + π)⌝] exp_s1_onto_thm1)
	THEN rewrite_tac[exp_s1_∈_s1_thm]
	THEN REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜x + π⌝ THEN_TRY PC_T1"ℝ_lin_arith" asm_prove_tac[]
	THEN all_var_elim_asm_tac1);
a(spec_nth_asm_tac 2 ⌜x'⌝ THEN_TRY PC_T1"ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%
=SML

val ⦏exp_s1_covering_projection_lemma3⦎ = save_thm (
	"exp_s1_covering_projection_lemma3",
 rewrite_rule[open_ℝ_topology_thm,
	open_ℂ_topology_thm,
	exp_s1_continuous_thm,
	exp_s1_∈_s1_thm,
	universe_subspace_topology_thm]
	(list_∀_elim[⌜O⋎R⌝, ⌜O⋎C⌝,
		⌜Universe:ℝ SET⌝, ⌜S1⌝, ⌜ExpS1⌝] 
			subspace_continuous_thm));

=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_covering_projection_lemma4⦎ = save_thm( "exp_s1_covering_projection_lemma4", (
set_goal([], ⌜∀x⦁
	ExpS1 x ∈ S1 \ {ExpS1 (x + π)}
⌝);
a(REPEAT strip_tac THEN1 rewrite_tac[exp_s1_∈_s1_thm]);
a(rewrite_tac[exp_s1_def, sin_cos_π_thm, sin_cos_plus_thm] THEN contr_tac);
a(lemma_tac⌜Sin x = 0. ∧ Cos x = 0.⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ante_tac (∀_elim⌜x⌝cos_squared_plus_sin_squared_thm));
a(asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
pop_thm()
));

=TEX

=TEX

%%%%
%%%%
=SML

val ⦏exp_s1_covering_projection_lemma5⦎ = save_thm( "exp_s1_covering_projection_lemma5", (
set_goal([], ⌜∀x y⦁
	ExpS1 x = ExpS1 y
∧	¬OpenInterval (x + ~ π) (x + π) ∩
		OpenInterval (y + ~ π) (y + π) = {}
⇒	x = y
⌝);
a(PC_T1 "sets_ext1" rewrite_tac[exp_s1_period_thm, open_interval_def] THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1
	THEN strip_asm_tac (∀_elim⌜m:ℕ⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN all_asm_ante_tac
	THEN rewrite_tac[ℕℝ_times_homomorphism_thm,
		ℕℝ_plus_homomorphism_thm,
		ℝ_times_plus_distrib_thm,
		ℝ_times_assoc_thm]
	THEN	(lemma_tac ⌜0. ≤ ℕℝ i * π⌝ THEN_LIST [
		bc_thm_tac ℝ_0_≤_0_≤_times_thm,
		PC_T1 "ℝ_lin_arith" asm_prove_tac[]]));
(* *** Goal "1" (duplicates "2") *** *)
a(rewrite_tac[ℕℝ_≤_thm] THEN rewrite_tac[ℝ_≤_def, π_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℂ_punctured_set_thm⦎ = save_thm (
	"ℂ_punctured_set_thm",
	rewrite_rule[
		open_ℂ_topology_thm,
		open_ℂ_hausdorff_thm,
		space_t_open_ℂ_thm]
		(∀_elim⌜O⋎C⌝ punctured_hausdorff_thm));

=TEX
%%%%
%%%%
=SML

val ⦏exp_s1_covering_projection_thm⦎ = save_thm( "exp_s1_covering_projection_thm", (
set_goal([], ⌜
	ExpS1 ∈ (O⋎R, O⋎S1) CoveringProjection
⌝);
a(rewrite_tac[covering_projection_def, space_t_subspace_open_ℂ_thm,
	exp_s1_continuous_thm,
	exp_s1_covering_projection_lemma3, open_s1_def]
	THEN REPEAT strip_tac);
a(all_fc_tac[exp_s1_onto_thm] THEN all_var_elim_asm_tac1);
a(∃_tac⌜S1 \ {ExpS1(x + π)}⌝);
a(rewrite_tac[exp_s1_covering_projection_lemma4,
	ℂ_punctured_set_thm]);
a(lemma_tac⌜0. < π⌝ THEN1 rewrite_tac[π_def]);
a(∃_tac⌜{I | ∃y⦁ ExpS1 y = ExpS1 x
	∧ I = OpenInterval (y - π) (y + π)}⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[open_interval_open_thm]);
(* *** Goal "2" *** *)
a(lemma_tac⌜¬ExpS1 x = ExpS1(x' + π)⌝);
(* *** Goal "2.1" *** *)
a(swap_nth_asm_concl_tac 1 THEN POP_ASM_T ante_tac);
a(rewrite_tac[exp_s1_homomorphism_thm]);
a(rewrite_tac[exp_s1_def, sin_cos_π_thm, ℂ_times_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2.2" *** *)
a(strip_asm_tac (list_∀_elim[⌜x'⌝, ⌜ExpS1 x⌝]exp_s1_onto_thm2));
a(∃_tac⌜OpenInterval (x'' + ~ π) (x'' + π)⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[open_interval_def]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(∃_tac⌜x''⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜ExpS1 y = ExpS1 y'⌝ THEN1 asm_rewrite_tac[]
	THEN all_var_elim_asm_tac1);
a(ALL_FC_T rewrite_tac[exp_s1_covering_projection_lemma5]);
(* *** Goal "4" *** *)
a(lemma_tac⌜S1 \ {ExpS1 (x + π)} ⊆ S1⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(ALL_FC_T rewrite_tac[⊆_subspace_topology_thm]);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o eq_sym_rule));
a(all_var_elim_asm_tac1);
a(LEMMA_T ⌜ExpS1 (x + π) = ExpS1 (y + π)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[exp_s1_homomorphism_thm]);
a(rewrite_tac[rewrite_rule[]exp_s1_covering_projection_lemma2]);
pop_thm()
));



=TEX
%%%%
%%%%

=SML

val ⦏exp_s1_path_lifting_thm⦎ = save_thm( "exp_s1_path_lifting_thm",
	(all_∀_intro o 
		rewrite_rule [exp_s1_covering_projection_thm, open_ℝ_topology_thm,
			open_ℂ_topology_thm, space_t_ℝ_thm, open_s1_topology_thm] o
			list_∀_elim [
				⌜O⋎R⌝, ⌜O⋎S1⌝, ⌜ExpS1⌝])
						covering_projection_path_lifting_bc_thm);

=TEX
%%%%
%%%%

=SML

val ⦏exp_s1_path_lifting_thm1⦎ = save_thm ( "exp_s1_path_lifting_thm1", ( 
set_goal([], ⌜
∀ y f⦁
	f ∈ Paths O⋎S1
⇒	(∃ g⦁ g ∈ Paths O⋎R ∧ (∀ s⦁ ExpS1 (g s) = f s))⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃x⦁ ExpS1 x = f 0.⌝);
(* *** Goal "1" *** *)
a(lemma_tac⌜f 0. ∈ S1⌝);
(* *** Goal "1.1" *** *)
a(ALL_FC_T (MAP_EVERY ante_tac) [paths_space_t_thm]);
a(rewrite_tac[space_t_open_s1_thm] THEN STRIP_T rewrite_thm_tac);
(* *** Goal "1.2" *** *)
a(contr_tac THEN all_fc_tac[conv_rule (ONCE_MAP_C eq_sym_conv) exp_s1_onto_thm]
	THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(all_fc_tac[exp_s1_path_lifting_thm]);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

=SML
(*

val ⦏s1_s1_loop_thm⦎ = save_thm ( "s1_s1_loop_thm", ( 
set_goal([], ⌜
∀ f⦁
	f ∈ (O⋎S1, O⋎S1) Continuous
⇒	(λ t⦁ f (ExpS1 (2. * π * t))) ∈ Loops(O⋎S1, f (ℕℂ 0))⌝);
a(rewrite_tac[loops_def, paths_def] THEN REPEAT strip_tac);


pop_thm()
));

*)
=TEX
%%%%
%%%%

=SML

val ⦏exp_s1_unique_path_lifting_thm⦎ = save_thm( "exp_s1_unique_path_lifting_thm", (
set_goal([], ⌜
∀f g a⦁
	f ∈ Paths O⋎R ∧ g ∈ Paths O⋎R ∧
	(∀x⦁ ExpS1(f x) = ExpS1(g x)) ∧
	g a = f a
⇒	∀x⦁ f x = g x
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a((bc_thm_tac o rewrite_rule [exp_s1_covering_projection_thm, open_ℝ_topology_thm,
			open_ℂ_topology_thm, open_s1_topology_thm, space_t_ℝ_thm,
			universe_ℝ_connected_thm] o
			list_∀_elim [
				⌜O⋎R⌝, ⌜O⋎R⌝, ⌜O⋎S1⌝, ⌜ExpS1⌝])
						unique_lifting_bc_thm
	THEN ∃_tac⌜a⌝);
a(ALL_FC_T asm_rewrite_tac[(rewrite_rule [open_ℝ_topology_thm] o ∀_elim⌜O⋎R⌝) paths_continuous_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏translated_path_ℝ_path_thm⦎ = save_thm ( "translated_path_ℝ_path_thm", ( 
set_goal([], ⌜
∀f c⦁ f ∈ Paths O⋎R ⇒ (λx⦁ f x + c) ∈ Paths O⋎R
⌝);
a(rewrite_tac[paths_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ℝ_continuity_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(all_asm_fc_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%
=SML

val ⦏ℤℝ_minus_homomorphism_thm⦎ = save_thm ( "ℤℝ_minus_homomorphism_thm", ( 
set_goal([], ⌜
∀i⦁ ℤℝ(~i) = ~(ℤℝ i)
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜ℤℝ i + ℤℝ(~i) = 0.⌝ (fn th => ante_tac th THEN  PC_T1 "ℝ_lin_arith" prove_tac[]));
a(LEMMA_T  ⌜ℤℝ i + ℤℝ(~i) = ℤℝ(i + ~i)⌝ rewrite_thm_tac THEN1 
	(pure_rewrite_tac[ℤℝ_plus_homomorphism_thm] THEN rewrite_tac[]));
a(rewrite_tac [ℤℝ_ℕℤ_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

(*
drop_main_goal();
*)

val _ = save_consistency_thm ⌜PathS1LiftLength⌝ (
push_consistency_goal ⌜PathS1LiftLength⌝;
a(prove_∃_tac THEN REPEAT strip_tac);
a(cases_tac⌜f' ∈ Paths O⋎S1⌝ THEN asm_rewrite_tac[]);
a(all_fc_tac[exp_s1_path_lifting_thm1]);
a(∃_tac⌜g 1.- g 0.⌝ THEN REPEAT strip_tac);
a(rename_tac[(⌜g'⌝, "h")] THEN rewrite_tac[]);
a(LEMMA_T ⌜∀x⦁ (λy⦁ h y + ~(h 0.) + g 0.) x = g x⌝
	(fn th => (ante_tac o ∀_elim ⌜1.⌝ o rewrite_rule[]) th THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(bc_thm_tac exp_s1_unique_path_lifting_thm);
a(∃_tac⌜0.⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac translated_path_ℝ_path_thm	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LEMMA_T⌜ExpS1(h 0.) =  ExpS1(g 0.)⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(POP_ASM_T (rewrite_thm_tac o conv_rule (ONCE_MAP_C eq_sym_conv)));
a(rewrite_tac[exp_s1_period_thm1] THEN REPEAT strip_tac);
a(∃_tac⌜~i⌝ THEN asm_rewrite_tac[ℤℝ_minus_homomorphism_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "3" *** *)
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
);

val ⦏path_s1_lift_length_def⦎ = get_spec ⌜PathS1LiftLength⌝;

=TEX
%%%%
%%%%

=SML

(*
drop_main_goal();
*)

val _ = save_consistency_thm ⌜LoopS1Degree⌝ (
push_consistency_goal ⌜LoopS1Degree⌝;
a(prove_∃_tac THEN REPEAT strip_tac);
a(rename_tac[(⌜f'⌝, "f")] THEN
	lemma_tac⌜∃D⦁ ∀g⦁ f ∈ Loops (O⋎S1, f 0.) ∧ g ∈ Paths O⋎R ∧ (∀ s⦁ ExpS1 (g s) = f s) ⇒
		g 1. + ~(g 0.) = 2. * ℤℝ D * π⌝);
(* *** Goal "1" *** *)
a(cases_tac⌜f ∈ Loops(O⋎S1, f 0.)⌝ THEN asm_rewrite_tac[]);
a(TOP_ASM_T (strip_asm_tac o rewrite_rule[loops_def]));
a(all_fc_tac[exp_s1_path_lifting_thm1]);
a(LEMMA_T ⌜ExpS1(g 0.) = ExpS1(g 1.)⌝ ante_tac);
(* *** Goal "1.1" *** *)
a(conv_tac eq_sym_conv THEN asm_rewrite_tac[] THEN DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(rewrite_tac[exp_s1_period_thm1,
	pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜∀x y z:ℝ⦁x = y + z ⇔ x - y = z⌝]
		THEN REPEAT strip_tac);
a(∃_tac⌜i⌝ THEN strip_tac THEN POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(rename_tac[(⌜g'⌝, "h")] THEN REPEAT strip_tac);
a(LEMMA_T ⌜∀x⦁ (λy⦁ h y + ~(h 0.) + g 0.) x = g x⌝
	(fn th => (ante_tac o ∀_elim ⌜1.⌝ o rewrite_rule[]) th THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(bc_thm_tac exp_s1_unique_path_lifting_thm);
a(∃_tac⌜0.⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(bc_thm_tac translated_path_ℝ_path_thm	THEN REPEAT strip_tac);
(* *** Goal "1.2.2" *** *)
a(LEMMA_T⌜ExpS1(h 0.) =  ExpS1(g 0.)⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(POP_ASM_T (rewrite_thm_tac o conv_rule (ONCE_MAP_C eq_sym_conv)));
a(rewrite_tac[exp_s1_period_thm1] THEN REPEAT strip_tac);
a(∃_tac⌜~i⌝ THEN asm_rewrite_tac[ℤℝ_minus_homomorphism_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.2.2.3" *** *)
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜D⌝ THEN once_rewrite_tac[∈_loops_thm]);
a(REPEAT ∀_tac THEN cases_tac ⌜x = f 0.⌝ THEN asm_rewrite_tac[]);
pop_thm()
);

val ⦏loop_s1_degree_def⦎ = get_spec ⌜LoopS1Degree⌝;

=TEX
%%%%
%%%%

=SML

val ⦏exp_s1_path_fibration_thm⦎ = save_thm ( "exp_s1_path_fibration_thm", ( 
set_goal([], ⌜ ∀f H⦁
	f ∈ Paths O⋎R
∧	H ∈ (O⋎R ×⋎T O⋎R, O⋎S1) Continuous
∧	(∀ x⦁ H (x, 0.) = ExpS1 (f x))
⇒	(∃ L⦁
		L ∈ (O⋎R ×⋎T O⋎R, O⋎R) Continuous
	∧	(∀ x⦁ L (x, 0.) = f x)
	∧	(∀ x s⦁ s ∈ ClosedInterval 0. 1. ⇒ ExpS1 (L (x, s)) = H (x, s)))
⌝);
a(rewrite_tac[paths_def] THEN REPEAT strip_tac);
a((bc_thm_tac o all_∀_intro o 
		rewrite_rule [exp_s1_covering_projection_thm, open_ℝ_topology_thm,
			homotopy_lifting_property_def,
			open_ℂ_topology_thm, space_t_ℝ_thm, open_s1_topology_thm] o
			list_∀_elim [
				⌜O⋎R⌝, ⌜O⋎R⌝, ⌜O⋎S1⌝, ⌜ExpS1⌝])
						covering_projection_fibration_thm
	THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

local
	
val ⦏ℂ_continuity_fact_thms⦎ : THM list = map (rewrite_rule[open_ℂ_def]) [
	ℂ_minus_continuous_thm,
	ℂ_conj_continuous_thm,
	ℂ_plus_continuous_thm,
	ℂ_times_continuous_thm,
	ℂ_ℕ_exp_continuous_thm,
	exp_s1_continuous_thm];

in

fun ⦏ℂ_continuity_tac⦎ (thms : THM list): TACTIC = (
	TRY (rewrite_tac[open_ℂ_def]) THEN
		ℝ_continuity_tac (thms @ ℂ_continuity_fact_thms)
);

end (* local ... in ... end *);

=TEX
%%%%
%%%%
=SML

val ⦏exp_s1_0_thm⦎ = save_thm ( "exp_s1_thm", ( 
set_goal([], ⌜
	ExpS1 0. = ℕℂ 1
⌝);
a(rewrite_tac[exp_s1_def, ℕℂ_def, ℝℂ_def, sin_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏exp_s1_2_i_π_thm⦎ = save_thm ( "exp_s1_2_π_thm", ( 
set_goal([], ⌜
	∀i⦁ ExpS1 (2. * ℤℝ i * π) = ℕℂ 1
⌝);
a(strip_tac THEN rewrite_tac[eq_sym_rule exp_s1_0_thm, exp_s1_period_thm1]);
a(∃_tac⌜~i⌝ THEN rewrite_tac[ℤℝ_minus_homomorphism_thm]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));



=TEX
%%%%
%%%%
=SML

val ⦏iota_s1_loop_thm⦎ = save_thm ( "iota_s1_loop_thm", ( 
set_goal([], ⌜
	IotaS1 ∈ Loops(O⋎S1, ℕℂ 1)
⌝);
a(rewrite_tac[eq_sym_rule exp_s1_0_thm, iota_s1_def]);
a((bc_thm_tac o rewrite_rule[] o
	list_∀_elim[⌜O⋎S1⌝, ⌜λt⦁ExpS1(2. * π * t)⌝])loop_from_arc_thm
		THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[open_s1_def] THEN bc_thm_tac subspace_range_continuous_bc_thm);
a(rewrite_tac[exp_s1_∈_s1_thm]);
a(ℂ_continuity_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[exp_s1_period_thm1] THEN ∃_tac⌜~(ℕℤ 1)⌝);
a(rewrite_tac[ℤℝ_minus_homomorphism_thm, ℤℝ_def]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏iota_s1_continuous_thm⦎ = save_thm ( "iota_s1_continuous_thm", ( 
set_goal([], ⌜
	IotaS1 ∈(O⋎R, O⋎S1) Continuous
⌝);
a((ante_tac o rewrite_rule[loops_def, paths_def]) iota_s1_loop_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏s1_s1_loop_loop_thm⦎ = save_thm ( "s1_s1_loop_loop_thm", ( 
set_goal([], ⌜
∀f⦁ f ∈ (O⋎S1, O⋎S1) Continuous ⇒ S1S1Loop f ∈ Loops(O⋎S1, f(ℕℂ 1))
⌝);
a(REPEAT strip_tac THEN strip_asm_tac iota_s1_loop_thm);
a(ALL_FC_T (MAP_EVERY ante_tac) [(rewrite_rule[open_s1_topology_thm] o
		list_∀_elim[⌜O⋎S1⌝, ⌜O⋎S1⌝]) loop_comp_continuous_loop_thm]);
a(rewrite_tac[s1_s1_loop_def]);
pop_thm()
));



=TEX
%%%%
%%%%
=SML

val ⦏π_recip_clauses⦎ = save_thm ( "π_recip_clauses", ( 
set_goal([], ⌜
	π * π ⋏-⋏1 = 1. ∧ π ⋏-⋏1 * π = 1.
⌝);
a(conv_tac (RIGHT_C (once_rewrite_conv[ℝ_times_comm_thm])));
a(rewrite_tac[] THEN bc_thm_tac ℝ_times_recip_thm);
a(strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_2_π_lemma⦎ = save_thm ( "times_2_π_lemma", ( 
set_goal([], ⌜
	∀x y⦁ x = 2. * y * π ⇔ y = (1/2) * x * π ⋏-⋏1
⌝);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(conv_tac (RIGHT_C ℝ_anf_conv));
a(rewrite_tac[ℝ_times_assoc_thm1, π_recip_clauses]);
(* *** Goal "2" *** *)
a(conv_tac (RIGHT_C ℝ_anf_conv));
a(rewrite_tac[ℝ_times_assoc_thm1, π_recip_clauses]);
pop_thm()
));


=TEX
%%%%
%%%%
=SML

val ⦏ℤ_≤_cases_thm1⦎ = save_thm("ℤ_≤_cases_thm1",
	rewrite_rule[ℤ_less_def] ℤ_less_cases_thm);
val ⦏ℝ_times_mono_⇔_thm1⦎ = save_thm("ℝ_times_mono_thm1",
	(conv_rule (ONCE_MAP_C eq_sym_conv)) ℝ_times_mono_⇔_thm);

val ⦏ℤℝ_0_less_thm⦎ = save_thm ( "ℤℝ_0_less_thm", ( 
set_goal([], ⌜
	∀i⦁ 0. < ℤℝ i ⇔ ℕℤ 0 < i
⌝);
a(strip_tac);
a((strip_asm_tac o ∀_elim⌜i⌝) ℤ_cases_thm1 THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(rewrite_tac[ℤℝ_ℕℤ_thm, ℕℤ_less_thm, ℕℝ_less_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x⦁ 0. < x ⇔ ~x < 0.⌝,
	pc_rule1 "ℤ_lin_arith" prove_rule[]⌜∀x⦁ ℕℤ 0 < x ⇔ ~x < ℕℤ 0⌝,
	ℕℤ_less_thm]);
a(rewrite_tac[ℤℝ_minus_homomorphism_thm, ℕℤ_less_thm, ℕℤ_plus_homomorphism_thm,
	ℤℝ_def, ℤℝ_ℕℤ_thm,ℕℝ_less_thm]);
pop_thm()
));


val ⦏ℤℝ_less_thm⦎ = save_thm ( "ℤℝ_less_thm", ( 
set_goal([], ⌜
	∀i j⦁ ℤℝ i < ℤℝ j ⇔ i < j
⌝);
a(REPEAT ∀_tac THEN once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁ x < y ⇔ 0. < y - x⌝,
	pc_rule1 "ℤ_lin_arith" prove_rule[]⌜∀x y⦁ x < y ⇔ ℕℤ 0 < y -  x⌝]);
a(LEMMA_T ⌜ℤℝ j + ~(ℤℝ i) = ℤℝ(j + ~i)⌝ rewrite_thm_tac
	THEN1 rewrite_tac[ℤℝ_def, ℤℝ_minus_homomorphism_thm]);
a(rewrite_tac[ℤℝ_0_less_thm]);
pop_thm()
));


val ⦏ℤℝ_one_one_thm⦎ = save_thm ( "ℤℝ_one_one_thm", ( 
set_goal([], ⌜
	∀i j⦁ ℤℝ i = ℤℝ j ⇔ i = j
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y:ℝ⦁ x = y ⇔ ¬x < y ∧ ¬y < x⌝,
	pc_rule1 "ℤ_lin_arith" prove_rule[]⌜∀x y:ℤ⦁ x = y ⇔ ¬x < y ∧ ¬y < x⌝]);
a(rewrite_tac[ℤℝ_less_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏discrete_subgroup_ℝ_discrete_thm⦎ = save_thm ( "discrete_subgroup_ℝ_discrete_thm", ( 
set_goal([], ⌜∀c⦁
	0. < c ⇒ {z | ∃i⦁ z = c * ℤℝ i} ◁⋎T O⋎R ∈ Discrete⋎T
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜{z | ∃i⦁ z = c * ℤℝ i} ◁⋎T O⋎R ∈ Topology⌝ THEN1 basic_topology_tac[]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[open_singletons_discrete_thm]);
a(rewrite_tac[subspace_ℝ_space_t_thm, subspace_topology_def]
	THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(∃_tac ⌜OpenInterval (c * ℤℝ i - c) (c * ℤℝ i + c)⌝
	THEN rewrite_tac[open_interval_open_thm]);
a(rewrite_tac[open_interval_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(prove_tac[]);
(* *** Goal "4" *** *)
a(rename_tac[(⌜i'⌝, "j")] THEN swap_nth_asm_concl_tac 1);
a(LIST_DROP_NTH_ASM_T [1, 2] (MAP_EVERY ante_tac) THEN POP_ASM_T discard_tac);
a(LEMMA_T⌜c * ℤℝ i + ~ c = c * ℤℝ (i - ℕℤ 1)⌝ rewrite_thm_tac
	THEN1 (rewrite_tac[ℤℝ_def, ℤℝ_minus_homomorphism_thm] THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(LEMMA_T⌜c * ℤℝ i + c = c * ℤℝ (i + ℕℤ 1)⌝ rewrite_thm_tac
	THEN1 (rewrite_tac[ℤℝ_def, ℤℝ_minus_homomorphism_thm] THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_times_mono_⇔_thm1]);
a(rewrite_tac[ℤℝ_less_thm]);
a(REPEAT strip_tac THEN LEMMA_T ⌜i = j⌝ rewrite_thm_tac);
a(PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ker_exp_s1_discrete_thm⦎ = save_thm ( "ker_exp_s1_discrete_thm", ( 
set_goal([], ⌜
	{z | ∃i⦁ z = 2. * ℤℝ i * π} ◁⋎T O⋎R ∈ Discrete⋎T
⌝);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x⦁ 2. * x * π = (2. * π) * x⌝]);
a(bc_thm_tac discrete_subgroup_ℝ_discrete_thm);
a(strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

The below works around a possible bug in higher-order matching.

=SML

val ⦏s1_s1_degree_homotopy_invariant_lemma1⦎ = save_thm ( "s1_s1_degree_homotopy_invariant_lemma1", ( 
set_goal([], ⌜∀H⦁ 
	H ∈ (O⋎S1 ×⋎T O⋎R, O⋎S1) Continuous
⇒	(λ(y, s)⦁ H(IotaS1 y, s)) ∈ (O⋎R ×⋎T O⋎R, O⋎S1) Continuous
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜(λ(y, s)⦁ H(IotaS1 y, s)) = (λys⦁H((λ(y, s)⦁ (IotaS1 y, s)) ys))⌝
	pure_rewrite_thm_tac THEN1 rewrite_tac[]);
a(bc_thm_tac comp_continuous_thm);
a(∃_tac⌜O⋎S1 ×⋎T O⋎R⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ℂ_continuity_tac[iota_s1_continuous_thm]);
(* *** Goal "2" *** *)
a(basic_topology_tac[]);
(* *** Goal "1.3" *** *)
a(basic_topology_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%

The below works around a possible bug in higher-order matching.

=SML

val ⦏s1_s1_degree_homotopy_invariant_lemma2⦎ = save_thm ( "s1_s1_degree_homotopy_invariant_lemma2", ( 
set_goal([], ⌜∀H⦁ 
	L ∈ (O⋎R ×⋎T O⋎R, O⋎R) Continuous
⇒	(λ y⦁ L (IotaI y, 1.)) ∈ Paths O⋎R
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜(λ y⦁ L (IotaI y, 1.)) = (λ y⦁ (λz⦁ L (z, 1.)) (IotaI y))⌝
		pure_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac comp_iota_i_path_thm);
a(REPEAT strip_tac THEN ℂ_continuity_tac[]);
pop_thm()
));


=TEX
%%%%
%%%%
=SML

val ⦏s1_s1_degree_homotopy_invariant_thm⦎ = save_thm ( "s1_s1_degree_homotopy_invariant_thm", ( 
set_goal([], ⌜∀f g⦁ 
	f ∈ (O⋎S1, O⋎S1) Continuous ∧
	g ∈ (O⋎S1, O⋎S1) Continuous ∧
	((O⋎S1, {}, O⋎S1) Homotopic) f g
⇒	S1S1Degree f = S1S1Degree g
⌝);
a(rewrite_tac[homotopic_def, homotopy_def, s1_s1_degree_def, s1_s1_loop_def] THEN REPEAT strip_tac);
a(all_fc_tac[∀_elim⌜f⌝ s1_s1_loop_loop_thm]);
a(TOP_ASM_T (strip_asm_tac o rewrite_rule[loops_def]));
a(all_fc_tac [paths_space_t_thm]);
a(POP_ASM_T (ante_tac o ∀_elim⌜0.⌝));
a(rewrite_tac[] THEN strip_tac);
a(all_fc_tac[exp_s1_onto_thm3]);
a(all_fc_tac[exp_s1_path_lifting_thm]);
a(rename_tac[(⌜g'⌝, "lf")] THEN all_fc_tac [s1_s1_degree_homotopy_invariant_lemma1]);
a(lemma_tac⌜∀y⦁ (λ(y, s)⦁ H(IotaS1 y, s)) (y, 0.) = ExpS1(lf y)⌝
	THEN1 asm_rewrite_tac[s1_s1_loop_def]);
a(all_fc_tac[exp_s1_path_fibration_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∀s⦁0. ≤ s ∧ s ≤ 1. ⇒ (λy⦁ ExpS1(L(IotaI y, s))) ∈ Loops(O⋎S1, ExpS1(L(0., s)))⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[loops_def] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(LEMMA_T ⌜(λ y⦁ ExpS1 (L (IotaI y, s))) = (λ y⦁ (λz⦁ ExpS1 (L (z, s))) (IotaI y))⌝
		pure_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac comp_iota_i_path_thm);
a(REPEAT strip_tac THEN ℂ_continuity_tac[]);
a(rewrite_tac[open_s1_def] THEN bc_thm_tac subspace_range_continuous_bc_thm);
a(rewrite_tac[exp_s1_continuous_thm, exp_s1_∈_s1_thm]);
(* *** Goal "1.2" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(asm_rewrite_tac[iota_i_def]);
(* *** Goal "1.3" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(asm_rewrite_tac[iota_i_def]);
a(LEMMA_T⌜¬t ≤ 0.⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜(if t ≤ 1. then t else 1.) = 1.⌝ rewrite_thm_tac
	THEN1 (cases_tac ⌜t ≤ 1.⌝ THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LEMMA_T⌜IotaS1 1. = IotaS1 0.⌝ rewrite_thm_tac THEN DROP_ASMS_T discard_tac);
a(rewrite_tac[iota_s1_def]);
(* *** Goal "2" *** *)
a(all_fc_tac [s1_s1_degree_homotopy_invariant_lemma2]);
a(GET_NTH_ASM_T 2 (strip_asm_tac o ∀_elim⌜1.⌝));
a(lemma_tac⌜(∀ s⦁ ExpS1 ((λ y⦁ L (IotaI y, 1.)) s) = (λ y⦁ ExpS1 (L (IotaI y, 1.))) s)⌝
	THEN1 rewrite_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [loop_s1_degree_def] THEN rewrite_tac[]);
a(POP_ASM_T discard_tac);
a(LEMMA_T⌜(λ y⦁ ExpS1 (L (IotaI y, 1.))) = (λ t⦁ g (IotaS1 t))⌝ rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[] THEN lemma_tac ⌜∀x⦁ ExpS1 (L (x, 1.)) = H (IotaS1 x, 1.)⌝);
(* *** Goal "2.1.1" *** *)
a(REPEAT strip_tac THEN GET_NTH_ASM_T 4 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.1.2" *** *)
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(rewrite_tac[iota_s1_def, iota_i_def]);
a(if_cases_tac THEN asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(GET_NTH_ASM_T 5 (rewrite_thm_tac o conv_rule (ONCE_MAP_C eq_sym_conv)));
a(LEMMA_T ⌜IotaI 1. = 1. ∧ IotaI 0. = 0.⌝ rewrite_thm_tac THEN1 rewrite_tac[iota_i_def]);
a(REPEAT strip_tac);
a(LEMMA_T⌜L (1., 1.) + ~ (L (0., 1.)) = L (1., 0.) + ~ (L (0., 0.))⌝ ante_tac);
(* *** Goal "2.2.1" *** *)
a(lemma_tac ⌜∃c⦁ ∀s⦁ L(1., IotaI s) + ~(L(0., IotaI s)) = c⌝);
(* *** Goal "2.2.1.1" *** *)
a((bc_thm_tac o rewrite_rule [ker_exp_s1_discrete_thm, universe_ℝ_connected_thm] o
	list_∀_elim[⌜O⋎R⌝, ⌜{z | ∃i⦁ z = 2. * ℤℝ i * π} ◁⋎T O⋎R⌝,
		⌜(λs⦁ L(1., IotaI s) + ~(L(0., IotaI s)))⌝])
			connected_discrete_continuous_thm);
a(REPEAT strip_tac THEN1 (bc_thm_tac subspace_topology_thm THEN REPEAT strip_tac));
a(bc_thm_tac subspace_range_continuous_bc_thm THEN rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "2.2.1.1.1" *** *)
a(LEMMA_T ⌜ExpS1 (L (0., IotaI x')) = ExpS1(L(1., IotaI x'))⌝
	(strip_asm_tac o rewrite_rule[exp_s1_period_thm1]));
(* *** Goal "2.2.1.1.1.1" *** *)
a(lemma_tac⌜0. ≤ IotaI x' ∧ IotaI x' ≤ 1.⌝
	THEN1 (rewrite_tac[iota_i_def] THEN if_cases_tac THEN asm_rewrite_tac[]
		THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LIST_DROP_NTH_ASM_T [8] (ALL_FC_T rewrite_tac));
a(rewrite_tac[iota_s1_def]);
(* *** Goal "2.2.1.1.1.2" *** *)
a(∃_tac⌜i⌝ THEN POP_ASM_T rewrite_thm_tac);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2.2.1.1.2" *** *)
a(ℂ_continuity_tac[iota_i_continuous_thm]);
(* *** Goal "2.2.1.2" *** *)
a(POP_ASM_T (fn th => (ante_tac o ∀_elim⌜0.⌝) th THEN (ante_tac o ∀_elim⌜1.⌝) th));
a(rewrite_tac[iota_i_def] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [1, 2] rewrite_tac);
a(asm_rewrite_tac[ℤℝ_one_one_thm, times_2_π_lemma]);
a(rewrite_tac[ℝ_times_assoc_thm1]);
a(rewrite_tac[ℝ_times_assoc_thm, π_recip_clauses, ℤℝ_one_one_thm, s1_s1_loop_def]);
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
	val _ = output_theorems{out_file="wrk072.th.doc", theory="ℂ"};
end;
=TEX
} %\Hide
\end{document}



