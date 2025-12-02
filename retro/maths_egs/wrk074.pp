=IGN
********************************************************************************
wrk073.doc: this file is supplementary material for the ProofPower system

Copyright (c) 2004 Lemma 1 Ltd.

This file is supplied under the GNU General Public Licence (GPL) version 2.

See the file LICENSE supplied with ProofPower source for the terms of the GPL
or visit the OpenSource web site at http://www.opensource.org/

Contact: Rob Arthan < rda@lemma-one.com >
********************************************************************************
$Id: wrk074.doc,v 1.35 2011/02/06 17:42:49 rda Exp rda $
********************************************************************************
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\usepackage{A4}
\usepackage{url}

\def\ThmsII#1#2{%
{\vertbarfalse
\begin{minipage}[t]{0.49\hsize}
#1
\end{minipage}
\begin{minipage}[t]{0.49\hsize}
#2
\end{minipage}}}

\def\ThmsIII#1#2#3{%
{\vertbarfalse
\begin{minipage}[t]{0.325\hsize}
#1
\end{minipage}
\begin{minipage}[t]{0.325\hsize}
#2
\end{minipage}
\begin{minipage}[t]{0.325\hsize}
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

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}

\def\LogName{\mbox{{\sf log}}}
\def\Log#1{\LogName(#1)}

\def\SinName{\mbox{{\sf sin}}}
\def\Sin#1{\SinName(#1)}

\def\CosName{\mbox{{\sf cos}}}
\def\Cos#1{\CosName(#1)}

\def\Abs#1{|#1|}

\def\ElemsName{\mbox{{\sf elems}}}
\def\Elems#1{\ElemsName(#1)}

\def\SizeName{\#}
\def\Size#1{\#\left(#1\right)}

%\def\Binomial#1#2{\left(\begin{array}{c}#1\\#2\end{array}\right)}
\def\Binomial#1#2{C_{#2}^{#1}}

\def\DividesName{\mathrel{\mbox{{\sf divides}}}}
\def\Divides#1#2{#1\DividesName#2}

\def\DivName{\mathop{\mbox{{\sf div}}}}
\def\Div#1#2{#1\DivName#2}

\def\ModName{\mathop{\mbox{{\sf mod}}}}
\def\Mod#1#2{#1\ModName#2}

\def\Prime{\mbox{{\sf prime}}}

\title{Mathematical Case Studies: Some Number Theory\thanks{
First posted 19 December 2005;
for full changes history see: \protect\url{https://github.com/RobArthan/pp-contrib}.
}}
\author{Rob Arthan\\{\tt rda@lemma-one.com}}
\makeindex
\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This {\ProductHOL} document presents some definitions and theorems from number theory.
The topics currently covered include: divisors and greatest common divisors; Euclid's algorithm; e infinitude of the primes; fundamental theorem of arithmetic;
divergence of the series of prime reciprocals; Wilson's theorem.
\end{abstract}
\vfill
\begin{centering}

\bf Copyright \copyright\ : Lemma 1 Ltd 2005--\number\year \\
Reference: LEMMA1/HOL/WRK074; Current git revision: \VCVersion%


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

This document is one of a suite of mathematical case studies in {\ProductHOL}.
It deals with some elementary number theory.

Topics currently covered include divisors and greatest common divisors, Euclid's algorithm, the infinitude of the primes, fundamental theorem of arithmetic,
divergence of the series of reciprocals of the primes.

There are also a few definitions and lemmas relating to general subrings of the real numbers.
These are used to define the subring of integers and the subfield of rational numbers.


\section{THE THEORY {\em numbers}}\label{theory}

\subsection{Preliminaries}
=IGN
open_theory "numbers";
=SML
force_delete_theory "numbers" handle Fail _ => ();
open_theory"fincomb";
new_theory "numbers";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℤ", "'ℝ"];
=TEX

\subsection{Divisors in ℕ}
We begin to develop the theory of divisors by first defining an infix relation, $\DividesName$, such that $\Divides{n}{m}$ iff. $m$ is a multiple of $n$.
 
=SML
declare_infix(200, "Divides");
ⓈHOLCONST
│ ⦏$Divides⦎ : ℕ → ℕ → BOOL
├──────
│ ∀n m⦁ n Divides m ⇔ ∃k⦁ m = k * n
■
It is often convenient to reduce
=INLINEFT
n Divides m
=TEX
\ to
=INLINEFT
m Mod n = 0
=TEX
.
The following block of theorems provide this and several other useful facts, e.g., that {\em Divides} is a partial ordering, i.e., it is reflexive, antisymmetric and transitive.

\ThmsIII{
=GFT
times_eq_0_thm
times_cancel_thm
times_eq_eq_1_thm
times_eq_1_thm
ℕ_exp_clauses
ℕ_exp_eq_0_thm
ℕ_exp_eq_1_thm
ℕ_exp_1_thm
ℕ_exp_divides_thm
ℕ_exp_times_thm
ℕ_exp_ℕ_exp_thm
=TEX
}{%
=GFT
div_mod_1_thm
m_div_mod_m_thm
zero_div_mod_thm
less_div_mod_thm
div_mod_times_cancel_thm
mod_clauses
div_clauses
mod_eq_0_thm
divides_0_thm
divides_trans_thm
divides_mod_thm
=TEX
}{%
=GFT
divides_refl_thm
divides_antisym_thm
divides_plus_thm
divides_times_thm
divides_≤_thm
divisors_finite_thm
divides_1_thm
mod_plus_homomorphism_thm
mod_times_homomorphism_thm
mod_ℕ_exp_thm
square_≤_mono_thm
=TEX
}

We now specify the greatest common divisor function by requiring it to produce greatest lower bounds with respect to the divisor ordering.

ⓈHOLCONST
│ ⦏Gcd⦎ : ℕ → ℕ → ℕ
├──────
│ ∀m n⦁	0 < m ∨ 0 < n
│ ⇒	Gcd m n Divides m ∧ Gcd m n Divides n
│ ∧ 	(∀d⦁	d Divides m ∧ d Divides n
│	⇒	d Divides Gcd m n)
■

We will need to prove the consistency of the above definition.
Our approach is based on the one  which exhibits the greatest common divisor of $m$ and $n$ as the smallest positive value of the form $am + bn$.
To follow that approach directly requires $a$ and $b$ to range over both positive and negative integers.
A slightly less symmetrical alternative is to take the g.c.d. to be the smallest positive value of the form $(am)\;Mod\;n$.
This works over the natural numbers and is the method we use.

Various useful lemmas about greatest common divisors are then proved culminating in the theorem that Euclid's algorithm computes them.

\ThmsIII{
=GFT
Gcd_consistent
gcd_def
gcd_pos_thm
=TEX
}{%
=GFT
gcd_unique_thm
gcd_idemp_thm
gcd_comm_thm
=TEX
}{%
=GFT
gcd_plus_thm
gcd_eq_mod_thm
euclid_algorithm_thm
=TEX
}

Now we define the set of prime numbers:

ⓈHOLCONST
│ ⦏Prime⦎ : ℕ SET
├──────
│ Prime = {p | 1 < p ∧ ∀m n⦁ p = m*n ⇒ m = 1 ∨ n = 1}
■
The first important fact we need about prime numbers states that a number is prime iff. it is greater than 1 and whenever it divides a product it divides one of the factors.
The right-to-left direction of this is simple.
It is for this the other direction that we needed to develop the theory of the g.c.d.

\ThmsIII{
=GFT
prime_0_less_thm
prime_2_≤_thm
prime_divides_thm
=TEX
}{%
=GFT
gcd_prime_thm
prime_thm
=TEX
}{%
=GFT
prime_divisor_thm
prime_divisor_thm1
=TEX
}

\subsection{Indexed Sums and Products in ℕ}
A useful application of the set fold operation is to define the following indexed sum operation. Given an index set, $a$, and a function, $f$, assigning a number to each member of $a$,
=INLINEFT
IndSum⋎N a f
=TEX
\ is the indexed sum $\sum_{x\in a}f(x)$, which is defined on any set $a$ in which $f$ has finite support.


ⓈHOLCONST
│ ⦏IndSum⋎N⦎ : 'a SET → ('a → ℕ) → ℕ
├──────
│ ∀f⦁	IndSum⋎N {} f = 0
│ ∧	∀x a⦁	a ∈ Finite ∧ ¬x ∈ a
│	⇒	IndSum⋎N ({x} ∪ a) f = f x + IndSum⋎N a f
■

We will write $\sum\,a\,f$ as shorthand for
=INLINEFT
IndSum⋎N a f
=TEX
.
=SML
declare_alias("Σ", ⌜IndSum⋎N⌝);
=TEX
Similarly, we define indexed products:
=TEX
ⓈHOLCONST
│ ⦏IndProd⋎N⦎ : 'a SET → ('a → ℕ) → ℕ
├──────
│ ∀f⦁	IndProd⋎N {} f = 1
│ ∧	∀x a⦁	a ∈ Finite ∧ ¬x ∈ a
│	⇒	IndProd⋎N ({x} ∪ a) f = f x * IndProd⋎N a f
■

We will write $\prod\,a\,f$ as shorthand for
=INLINEFT
IndProd⋎N a f
=TEX
.
=SML
declare_alias("Π", ⌜IndProd⋎N⌝);
=TEX

The theorems about sums and products comprise various generalities that make the definitions useful in the common cases.
Then as an exercise for the definitions, we prove the ``division by 3 rule'' which says that a number is divisible by 3 iff. the sum of its decimal digits is divisible by 3.

\ThmsIII{
=GFT
IndSum⋎N_consistent
ind_sum_ℕ_def
ind_sum_ℕ_0_thm
ind_sum_ℕ_local_thm
=TEX
}{%
=GFT
IndProd⋎N_consistent
ind_prod_ℕ_def
ind_prod_ℕ_1_thm
ind_prod_ℕ_0_thm
=TEX
}{%
=GFT
ind_prod_ℕ_local_thm
div_3_rule_thm1
div_3_rule_thm
=TEX
}

Using indexed products, we can now give Euclid's proof that there are infinitely many primes:

\ThmsIII{}{
=GFT
prime_infinite_thm
=TEX
}{}

\subsection{Unique Factorisation in ℕ}
The next group of theorems in the script prove the fundamental theorem of arithmetic, i.e., the statement that any positive natural number can be written uniquely as a product of prime powers.

The existence proof is standard, although it is very convenient to give an explicit formula for the exponent of a prime in the factorisation ({\em exponent\_thm}). This makes the uniqueness part of the argument very simple.

\ThmsIII{
=GFT
prime_Π_thm
prime_divides_prime_thm
divides_ℕ_exp_thm
=TEX
}{%
=GFT
divides_cancel_thm
exponent_thm
unique_factorisation_thm
=TEX
}{%
=GFT
prime_divisors_unique_thm
prime_divisors_finite_thm
=TEX
}

Having proved the above, we have the consistency of the
following function that maps a non-zero number $m$
and a prime $p$ to the exponent of $p$ in the prime
factorisation of $m$.
ⓈHOLCONST
│ ⦏Exponent⦎ : ℕ → ℕ → ℕ
├──────
│ ∀m⦁	0 < m
│ ⇒	{p | ¬Exponent m p = 0} ∈ Finite
│ ∧	{p | ¬Exponent m p = 0} ⊆ Prime
│ ∧	m = Π {p | ¬ Exponent m p = 0} (λ p⦁ p ^ Exponent m p)
■


\subsection{Divergence of the Series of Prime Reciprocals}
The next block of theorems lead up to the proof that the sum $\sum_p 1/p$ taken over all primes p diverges.
This is done using essentially the argument given in Hardy and Wright~\cite{Hardy78}.
It is convenient to define the notion of a square-free number, i.e., a number that is not divisible by a square other than 1.

ⓈHOLCONST
│ ⦏SquareFree⦎ : ℕ SET
├──────
│ ∀m⦁ m ∈ SquareFree ⇔ ∀n⦁ n^2 Divides m ⇒ n = 1
■
We first derive several facts about square-free numbers.
In particular we show that a number is square-free iff. it is not divisible by the square of any prime.
This shows that the non-zero exponents in the prime factorisation of a square-free number are all equal to 1.
Using this, we show that given any finite set of primes $P$, the set of square-free number whose prime divisors lie in $P$ is finite and has $2^\Size{P}$ elements.
We then show that every number can be written as a product $n^2\times d$ where $d$ is square-free.

\ThmsIII{
=GFT
square_free_0_less_thm
square_free_prime_thm
factorisation_square_free_thm
=TEX
}{
=GFT
divides_square_free_thm
square_free_factorisation_thm
square_free_finite_size_thm
=TEX
}{
=GFT
square_free_1_thm
square_free_divisor_thm
square_free_divisor_thm1
=TEX
}

We now give a series of theorems that build up to the proof that
$\sum_p 1/p$ taken over prime $p \le n$
is unbounded as $n$ tends to infinity.
The argument is that of~\cite{Hardy78}[Theorem 19] adapted to fit into the typed framework of HOL.

Consider a finite set of primes, $P$ and a positive natural number $n$. If $m \le n^2$, then either all prime divisors of $m$ are in $P$ or not. We will estimate the number of $m$ falling under each of the two cases:

\begin{itemize}
\item
If all the prime divisors of $m$ lie in $P$, $m$ can be written as $m = k^2d$ where $k \le n$ and where $d$ is a square-free number whose prime divisors lie in $P$.
There are at most $n$ choices for $k$ and $2^{\Size{P}}$ so there are at most $n2^{\Size{P}}$ such $m$.
\item
If $m$ is divisible by a prime $q$ that is not in $P$, we have $m = kq$ for some $k \le \Div{n^2}{q}$. 
The number of such $m$ is therefore
$\sum_q \Div{n^2}{q}$ taken over all prime $q$ with $q \not\in P$ and $q \le n^2$.
\end{itemize}

Let $Q$ be the set of primes $q \le n^2$ which are not in $P$, then, as any $m \le n^2$ falls under one of the two cases, one has:
\begin{eqnarray}
n^2 &\le&  n2^{\Size{P}} +
	\sum_{q \in Q}
	\Div{n^2}{q}
\end{eqnarray}

Putting $n = 2^{\Size{P}+1}$ this gives:
\begin{eqnarray}
2^{2\Size{P}+2} &\le&  2^{2\Size{P}+1} +
	\sum_{q \in Q}
	\Div{2^{2\Size{P}+2}}{q}
\end{eqnarray}

Whence, subtracting $2^{2\Size{P}+1}$ from both sides and then, observing that $\Div{i}{q} \le i/q$, and dividing through by $2^{2\Size{P}+2}$, one has:
\begin{eqnarray}
2^{2\Size{P}+1} &\le& \sum_{q \in Q} \Div{2^{2\Size{P}+2}}{q}\\
1/2 &\le& \sum_{q \in Q} 1/q
\end{eqnarray}

I.e., given any finite set of primes $P$, taking $Q$ to be the set of primes q that are not in $P$ and that satisfy $q \le 2^{2\Size{P}+2}$, the sum of reciprocals of the elements of $Q$ is greater than $1/2$.
That the sum of the series of reciprocals of the primes diverges follows by an easy induction (given any initial subsequence of the sequence of primes for which the sum or reciprocals is $s$, say, the above argument gives a longer initial subsequence whose sum is $s +1/2$).
The following block of theorems implement the above proof.

\ThmsII{
=GFT
recip_primes_div_estimate_thm1
divisors_finite_size_thm
recip_primes_div_estimate_thm2
recip_primes_div_estimate_thm3
recip_primes_div_estimate_thm4
=TEX
}{
=GFT
ℕℝ_ind_sum_thm
ind_sum_≤_mono_thm
ℕℝ_div_≤_thm
recip_primes_div_estimate_thm5
recip_primes_div_thm
=TEX
}
\subsection{Coprimality}
=SML
declare_infix(200, "Coprime");

ⓈHOLCONST
│ $⦏Coprime⦎ : ℕ → ℕ → BOOL
├──────
│ ∀m n⦁ m Coprime n ⇔ ∀i⦁ i Divides m ∧ i Divides n ⇒ i = 1
■
\ThmsIII{
=GFT
coprime_prime_thm
=TEX
}{%
=GFT
coprime_gcd_thm
=TEX
}{%
=GFT

=TEX
}
\subsection{Real Integral Domains}
In general, an integral domain is a ring without zero divisors.
As we are only concerned with subrings of the reals here, any subring of the reals is an integral domain. 
 
ⓈHOLCONST
│ ⦏RealID⦎ : ℝ SET SET
├──────
│ ∀A⦁ A ∈ RealID ⇔
│	ℕℝ 1 ∈ A
│ ∧	(∀x y⦁x ∈ A ∧ y ∈ A ⇒ x + y ∈ A)
│ ∧	(∀x⦁x ∈ A ⇒ ~x ∈ A)
│ ∧	(∀x y⦁x ∈ A ∧ y ∈ A ⇒ x * y ∈ A)
■

The domain of (rational) integers comprises the intersection of all real integral domains:

ⓈHOLCONST
│ ⦏ℤ⋎R⦎ : ℝ SET
├──────
│ ℤ⋎R = ⋂RealID
■
=SML
declare_alias("ℤ", ⌜ℤ⋎R⌝);
=TEX
To get started, we prove that ℝ is a real integral domain, as is the intersection of any family of real integral domains, and so in particular is ℤ, the intersection of all real integral domains.
We then show that ℤ is precisely the image of the type ℤ of integers under the injection ℤℝ:

\ThmsII{
=GFT
ℝ_real_i_d_thm
⋂_real_i_d_thm
=TEX
}{%
=GFT
ℤ_real_i_d_thm
ℤ_thm
=TEX
}

\subsection{Real Fields}
A real field is a real integral domain that is closed under taking reciprocals of non-zero elements.

ⓈHOLCONST
│ ⦏RealField⦎ : ℝ SET SET
├──────
│ ∀A⦁ A ∈ RealField ⇔
│	A ∈ RealID
│ ∧	(∀x⦁x ∈ A \ {ℕℝ 0} ⇒ x ⋏-⋏1 ∈ A)
■

The field of rational numbes is the intersection of all real fields.

ⓈHOLCONST
│ ⦏ℚ⋎R⦎ : ℝ SET
├──────
│ ℚ⋎R = ⋂RealField
■

Following a similar pattern to the last section, we prove that ℝ is a real field, as is the intersection of any family of real fields, in particular, ℚ, the intersection of all real fields.
We prove that ℤ is a subset of ℚ.
An explicit formula for the set ℚ is given in the next section.

\ThmsII{
=GFT
ℝ_real_field_thm
⋂_real_field_thm
=TEX
}{
=GFT
rat_real_i_d_thm
ℤ_⊆_rat_thm
=TEX
}

=SML
declare_alias("ℚ", ⌜ℚ⋎R⌝);
=TEX
\subsection{Fields of Fractions}
The field of fractions of a set $A$, (typically an integral domain) is the intersection of all fields that contain $A$.

ⓈHOLCONST
│ ⦏FieldOfFractions⦎ : ℝ SET → ℝ SET
├──────
│ ∀A⦁ FieldOfFractions A = ⋂{K | K ∈ RealField ∧ A ⊆ K}
■
We prove that the field of fractions of any set is indeed a real field and that ℚ is the field of fractions of ℤ.
We then show that if $A$ is an integral domain, then its field of fractions does indeed comprise precisely the set of fractions $a/b$ with $a, b \in A$ and $b \not = 0$.
Using this we can derive an explicit formula for the set ℚ.


\ThmsII{
=GFT
field_of_fractions_field_thm
field_of_fractions_thm
rat_field_of_fractions_thm
=TEX
}{
=GFT
rat_thm
rat_thm1
=TEX
}
\section{Irrationality of Quadratic Surds}
We prove that any quadratic surd that is not an integer is irrational, and in particular, that $\sqrt{2}$ is irrational.
The proof is as follows:
if $m^2 = kn^2$ for any natural numbers $k$, $m$ and $n$ with $k$ positive and $n > 1$, then any prime divisor of $n$ is also a prime divisor of $m$.
Thus, by infinite descent, the only solutions of this equation with $k$ and $n$ positive have $n = 1$, i.e., the only solutions are when $k = m^2$ is a square.
Thus to prove that $\sqrt{2}$ is irrational it suffices to show that it is not an integer.

\ThmsII{
=GFT
sqrt_eq_thm
quadratic_surd_thm1
quadratic_surd_thm
=TEX
}{
=GFT
sqrt_2_lemma
sqrt_2_irrational_thm
=TEX
}
\section{Arithmetic {\it modulo} a Prime}
The next block of results develop some basic facts about arithemetic {\it modulo} prime numbers, e.g., the existence of multiplicative inverses {\it modulo} primes.
The block concludes with Wilson's theorem: if $1 < p$, then $p$ is prime iff. $(p-1)!$ is congruent to $-1$ {\it modulo} $p$.
We state this in term of the $\ModName$ operator on the natural numbers so that it becomes ``$p$ is prime iff. $\Mod{(p-1)!}{p} = p - 1$''.

\ThmsII{
=GFT
plus_mod_thm
times_mod_p_inverse_thm
times_mod_p_inverse_thm1
=TEX
}{
=GFT
times_mod_p_inverse_unique_thm
wilson_lemma1
wilson_thm
=TEX
}
\section{The Two Squares Theorem}
The combinatorial part of the Heath-Brown proof of the two squares theorem is given in~\cite{LEMMA1/HOL/WRK073},
with the various assumptions on the prime $p$ made explicit.
We complete the proof using the concept of primes defined in this document.

This involves transferring results from the type of integers to the type of natural numbers.
The following function is convenient for doing the transfer.

ⓈHOLCONST
│ ⦏Abs⋎ℕ⦎ : ℤ → ℕ
├──────
│ ∀i⦁ ℕℤ (Abs⋎ℕ i) = Abs i
■
With some basic properties of the function
=INLINEFT
Abs⋎ℕ
=TEX
\ and one or two little lemmas about squares, we derive
the two squares theorem from the combinatorial result
of~\cite{LEMMA1/HOL/WRK073},

\ThmsIII{
=GFT
Abs⋎ℕ_consistent
abs_ℕ_thm
abs_ℕ_ℕℤ_thm
=TEX
}{
=GFT
abs_ℕ_times_thm
abs_ℕ_cases_thm
ℤ_abs_square_thm
=TEX
}{
=GFT
prime_¬_square_thm
two_squares_thm
=TEX
}

\bibliographystyle{fmu}
\bibliography{fmu}

\appendix
{%\HOLindexOff
\let\Section\section
\let\subsection\Hide
\def\section#1{\Section{#1}\label{listing}}
\let\subsection\Hide
\include{wrk074.th}}

=TEX

\twocolumn[\section*{INDEX}\label{INDEX}]
\addcontentsline{toc}{section}{INDEX}
{\small\printindex}

\end{document} %% COMMENT THIS LINE OUT TO TYPESET THE PROOF SCRIPTS
=TEX
%%%%
%%%%
=SML
val ⦏divides_def⦎ = get_spec ⌜$Divides⌝;
val ⦏prime_def⦎ = get_spec ⌜Prime⌝;
val ⦏coprime_def⦎ = get_spec ⌜$Coprime⌝;
val ⦏square_free_def⦎ = get_spec ⌜SquareFree⌝;
val ⦏real_i_d_def⦎ = get_spec ⌜RealID⌝;
val ⦏ℤ_def⦎ = get_spec ⌜ℤ⋎R⌝;
val ⦏real_field_def⦎ = get_spec ⌜RealField⌝;
val ⦏rat_def⦎ = get_spec ⌜ℚ⋎R⌝;
val ⦏field_of_fractions_def⦎ = get_spec ⌜FieldOfFractions⌝;
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀m n a⦁ (∀i⦁i ∈ a ⇒ i ≤ m) ∧ n ∈ a ⇒ Max a ∈ a⌝);
a(∀_tac THEN induction_tac ⌜m:ℕ⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[] THEN all_var_elim_asm_tac1);
a(all_fc_tac[get_spec⌜Max⌝] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜m + 1 ∈ a⌝
	THEN1 (all_fc_tac[get_spec⌜Max⌝] THEN asm_rewrite_tac[]));
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN ∃_tac⌜n⌝
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(cases_tac⌜i = m + 1⌝ THEN1 all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏max_∈_thm⦎ = save_pop_thm"max_∈_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n a⦁ (∀i⦁i ∈ a ⇒ i ≤ m) ∧ n ∈ a ⇒ n ≤ Max a⌝);
a(∀_tac THEN induction_tac ⌜m:ℕ⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[] THEN all_var_elim_asm_tac1);
a(all_fc_tac[get_spec⌜Max⌝] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜m + 1 ∈ a⌝
	THEN1 (all_fc_tac[get_spec⌜Max⌝] THEN asm_rewrite_tac[]
		THEN all_asm_fc_tac[]));
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(cases_tac⌜i = m + 1⌝ THEN1 all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏≤_max_thm⦎ = save_pop_thm"≤_max_thm";
=TEX
%%%%
%%%% DIVISORS IN ℕ
%%%%
=SML
val ⦏div_mod_unique_thm1⦎ =
	rewrite_rule[taut_rule
		⌜∀p1 p2 p3⦁ (p1 ⇒ p2 ⇒ p3) ⇔ (p1 ∧ p2 ⇒ p3)⌝]
	(conv_rule (ONCE_MAP_C(RAND_C(RAND_C (RANDS_C eq_sym_conv))))
		div_mod_unique_thm);
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁m * n = 0 ⇔ m = 0 ∨ n = 0⌝);
a(REPEAT ∀_tac);
a(cases_tac⌜m = 0⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜n = 0⌝ THEN asm_rewrite_tac[]);
a(LEMMA_T⌜1 ≤ m ∧ 1 ≤ n⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏times_eq_0_thm⦎ = save_pop_thm "times_eq_0_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀k m n⦁0 < k ∧ k * m = k * n ⇒ m = n⌝);
a(contr_tac);
a((LEMMA_T⌜m ≤ n ∨ n ≤ m⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 rewrite_tac[≤_cases_thm])
		THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(lemma_tac⌜k*i = 0⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(fc_tac[times_eq_0_thm] THEN all_var_elim_asm_tac1
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜k*i = 0⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(fc_tac[times_eq_0_thm] THEN all_var_elim_asm_tac1
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏times_cancel_thm⦎ = save_pop_thm "times_cancel_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁0 < n ∧ m * n = n ⇒ m = 1⌝);
a(REPEAT strip_tac THEN
	bc_thm_tac (once_rewrite_rule[times_comm_thm] times_cancel_thm));
a(∃_tac⌜n⌝ THEN asm_rewrite_tac[]);
val ⦏times_eq_eq_1_thm⦎ = save_pop_thm "times_eq_eq_1_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁m * n = 1 ⇔ m = 1 ∧ n = 1⌝);
a(REPEAT ∀_tac);
a(cases_tac⌜m = 0 ∨ n = 0 ∨ m = 1 ∨ n = 1⌝ THEN_TRY
	(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(LEMMA_T⌜2 ≤ m ∧ 2 ≤ n⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3, 4, 5, 6] discard_tac);
a(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏times_eq_1_thm⦎ = save_pop_thm "times_eq_1_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m:ℕ⦁ m ^ 0 = 1 ∧ m ^ 1 = m ∧ m ^ 2 = m * m⌝);
a(pure_rewrite_tac[prove_rule[]⌜2 = 1 + 1⌝, ℕ_exp_def]);
a(pure_once_rewrite_tac[prove_rule[]⌜1 = 0 + 1⌝]
	THEN pure_rewrite_tac[ℕ_exp_def]
	THEN rewrite_tac[]);
val ⦏ℕ_exp_clauses⦎ = save_pop_thm "ℕ_exp_clauses";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁m^n = 0 ⇔ m = 0 ∧ ¬n = 0⌝);
a(REPEAT_UNTIL is_⇒ strip_tac);
(* *** Goal "1" *** *)
a(induction_tac⌜n:ℕ⌝
	THEN asm_rewrite_tac[ℕ_exp_def, times_eq_0_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
a(strip_asm_tac(∀_elim⌜n⌝ ℕ_cases_thm)
	THEN1 all_var_elim_asm_tac1
	THEN rewrite_tac[ℕ_exp_def]);
val ⦏ℕ_exp_eq_0_thm⦎ = save_pop_thm "ℕ_exp_eq_0_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁m^n = 1 ⇔ m = 1 ∨ n = 0⌝);
a(REPEAT_UNTIL is_⇒ strip_tac);
(* *** Goal "1" *** *)
a(induction_tac⌜n:ℕ⌝
	THEN  asm_rewrite_tac[ℕ_exp_def, times_eq_1_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN_TRY asm_rewrite_tac[ℕ_exp_def]);
a(induction_tac⌜n:ℕ⌝
	THEN  asm_rewrite_tac[ℕ_exp_def]);
val ⦏ℕ_exp_eq_1_thm⦎ = save_pop_thm "ℕ_exp_eq_1_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m:ℕ⦁ m^1 = m⌝);
a(REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜m⌝, ⌜0⌝](∧_right_elim ℕ_exp_def)));
a(rewrite_tac[∧_left_elim ℕ_exp_def]);
val ⦏ℕ_exp_1_thm⦎ = save_pop_thm "ℕ_exp_1_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m:ℕ; k n⦁ k ≤ n ⇒ m^k Divides m^n⌝);
a(rewrite_tac[≤_def, divides_def] THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN induction_tac⌜i⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜1⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜m*k'⌝ THEN asm_rewrite_tac[plus_assoc_thm1, ℕ_exp_def, times_assoc_thm]);
val ⦏ℕ_exp_divides_thm⦎ = save_pop_thm "ℕ_exp_divides_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n k:ℕ⦁
	(m ^ n) * (m ^ k) = m ^ (n + k)
⌝);
a(REPEAT strip_tac);
a(induction_tac ⌜k⌝ THEN rewrite_tac[ℕ_exp_def,
	plus_assoc_thm1]);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏ℕ_exp_times_thm⦎ = save_pop_thm "ℕ_exp_times_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n k:ℕ⦁
	(m ^ n) ^ k = m ^ (n*k)
⌝);
a(REPEAT strip_tac);
a(induction_tac ⌜k⌝ THEN asm_rewrite_tac[ℕ_exp_def]);
a(rewrite_tac[ℕ_exp_times_thm]);
a(conv_tac (ONCE_MAP_C anf_conv) THEN strip_tac);
val ⦏ℕ_exp_ℕ_exp_thm⦎ = save_pop_thm "ℕ_exp_ℕ_exp_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁m Div 1 = m ∧ m Mod 1 = 0⌝);
a(∀_tac);
a(bc_thm_tac div_mod_unique_thm1 THEN rewrite_tac[]);
val ⦏div_mod_1_thm⦎ = save_pop_thm "div_mod_1_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ 0 < m ⇒ m Div m = 1 ∧ m Mod m = 0⌝);
a(∀_tac THEN ⇒_tac);
a(bc_thm_tac div_mod_unique_thm1 THEN asm_rewrite_tac[]);
val ⦏m_div_mod_m_thm⦎ = save_pop_thm "m_div_mod_m_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁0 < m ⇒ 0 Div m = 0 ∧ 0 Mod m = 0⌝);
a(∀_tac THEN ⇒_tac);
a(bc_thm_tac div_mod_unique_thm1 THEN asm_rewrite_tac[]);
val ⦏zero_div_mod_thm⦎ = save_pop_thm "zero_div_mod_thm";
=TEX
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁n < m ⇒ n Div m = 0 ∧ n Mod m = n⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(bc_thm_tac div_mod_unique_thm1 THEN asm_rewrite_tac[]);
val ⦏less_div_mod_thm⦎ = save_pop_thm "less_div_mod_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀k m n⦁0 < k ⇒ (m*k + n) Div k = m + n Div k ∧  (m*k + n) Mod k = n Mod k⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(bc_thm_tac div_mod_unique_thm1
	THEN ALL_FC_T rewrite_tac[mod_less_thm]);
a(rewrite_tac[times_plus_distrib_thm, plus_assoc_thm]);
a(bc_thm_tac div_mod_thm THEN REPEAT strip_tac);
val ⦏div_mod_times_cancel_thm⦎ = save_pop_thm "div_mod_times_cancel_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀k m n⦁
	0 < k
⇒	(m*k) Mod k = 0
∧	(k*m) Mod k = 0
∧	(k*m + n) Mod k = n Mod k
∧	(m*k + n) Mod k = n Mod k
∧	(n + k*m) Mod k = n Mod k
∧	(n + m*k) Mod k = n Mod k
∧	(k + n) Mod k = n Mod k
∧	(n + k) Mod k = n Mod k
∧	0 Mod k = 0
∧	k Mod k = 0
∧	(m Mod k) Mod k = m Mod k
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(rewrite_tac[∀_elim⌜k⌝ times_comm_thm, ∀_elim⌜n⌝ plus_order_thm]);
a(ALL_FC_T rewrite_tac[rewrite_rule[∀_elim⌜n⌝ plus_order_thm]
	div_mod_times_cancel_thm, m_div_mod_m_thm, zero_div_mod_thm]);
a(pure_once_rewrite_tac[prove_rule[]
	⌜m*k = m*k + 0 ∧ k + n = 1*k + n ∧ n + k = 1*k + n⌝]);
a(ALL_FC_T pure_rewrite_tac[div_mod_times_cancel_thm]
	THEN ALL_FC_T rewrite_tac[zero_div_mod_thm]);
a(lemma_tac⌜m Mod k < k⌝ THEN1 ALL_FC_T rewrite_tac[mod_less_thm]);
a(ALL_FC_T rewrite_tac[less_div_mod_thm]);
val ⦏mod_clauses⦎ = save_pop_thm "mod_clauses";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀k⦁0 < k ⇒
(∀m⦁
	0 < k
⇒	(m*k) Div k = m
∧	(k*m) Div k = m
∧	0 Div k = 0
∧	k Div k = 1)
∧ (∀m n⦁
	n < k
⇒	(k*m + n) Div k = m
∧	(m*k + n) Div k = m
∧	(n + k*m) Div k = m
∧	(n + m*k) Div k = m
∧	(k + n) Div k = 1
∧	(n + k) Div k = 1)
⌝);
a(PC_T1 "predicates" rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜k*m = m*k ∧ n + m*k = m*k + n ∧
	k + n = 1*k + n ∧ n + k = 1*k + n⌝,
	taut_rule ⌜∀p q⦁ p ∧ p ∧ q ⇔ p ∧ q⌝]);
a(∀_tac THEN ⇒_tac THEN ∧_tac THEN REPEAT_UNTIL is_∧ strip_tac);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[m_div_mod_m_thm, less_div_mod_thm]);
a(pure_once_rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜m*k = m*k + 0⌝]);
a(ALL_FC_T pure_rewrite_tac[div_mod_times_cancel_thm]);
a(ALL_FC_T rewrite_tac[zero_div_mod_thm]);
(* *** Goal "2" *** *)
a(ALL_FC_T pure_rewrite_tac[div_mod_times_cancel_thm]);
a(ALL_FC_T rewrite_tac[m_div_mod_m_thm, less_div_mod_thm]);
val ⦏div_clauses⦎ = save_pop_thm "div_clauses";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁
	0 < n
⇒	(m Mod n = 0 ⇔ ∃k⦁m = k*n)
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜m Div n⌝);
a(ALL_FC_T (conv_tac o LEFT_C o once_rewrite_conv)[div_mod_thm]);
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1 THEN ALL_FC_T rewrite_tac[mod_clauses]);
val ⦏mod_eq_0_thm⦎ = save_pop_thm "mod_eq_0_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁
	0 < n
⇒	(n Divides m ⇔ m Mod n = 0)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
(* *** Goal "1" *** *)
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[mod_eq_0_thm]);
a(rewrite_tac[divides_def]);
val ⦏divides_mod_eq_0_thm⦎ = save_pop_thm "divides_mod_eq_0_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁m Divides 0 ∧ (0 Divides m ⇔ m = 0)⌝);
a(REPEAT ∀_tac THEN rewrite_tac[divides_def]);
a(∃_tac⌜0⌝ THEN rewrite_tac[]);
val ⦏divides_0_thm⦎ = save_pop_thm "divides_0_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀n m⦁
	n Divides m ⇔ (if 0 < n then m Mod n else m) = 0
⌝);
a(REPEAT ∀_tac);
a(cases_tac⌜¬0 < n⌝ THEN asm_rewrite_tac[divides_def]);
(* *** Goal "1" *** *)
a(lemma_tac⌜n = 0⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(cases_tac⌜m = 0⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[mod_eq_0_thm]);
val ⦏divides_mod_thm⦎ = save_pop_thm "divides_mod_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜ ∀m⦁ m Divides m ⌝);
a(REPEAT strip_tac
	THEN rewrite_tac[divides_def]
	THEN ∃_tac ⌜1⌝ THEN rewrite_tac[]);
val ⦏divides_refl_thm⦎ = save_pop_thm "divides_refl_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜ ∀m n⦁ n Divides m ∧ m Divides n ⇔ m = n ⌝);
a(REPEAT ∀_tac THEN cases_tac⌜n = 0⌝
	THEN1 asm_rewrite_tac[divides_0_thm]);
a(cases_tac⌜m = 0⌝
	THEN1 (asm_rewrite_tac[divides_0_thm]
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(lemma_tac⌜0 < n ∧ 0 < m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[divides_mod_thm]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[mod_eq_0_thm]);
a(lemma_tac⌜(k'*k)*m = m⌝ THEN1
	(POP_ASM_T (fn th => conv_tac (RIGHT_C(rewrite_conv[th])))
		THEN asm_rewrite_tac[times_assoc_thm]));
a(all_fc_tac[times_eq_eq_1_thm]);
a(all_fc_tac[times_eq_1_thm]);
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac THEN ALL_FC_T rewrite_tac[mod_clauses]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac THEN ALL_FC_T rewrite_tac[mod_clauses]);
val ⦏divides_antisym_thm⦎ = save_pop_thm "divides_antisym_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜ ∀m n k⦁ n Divides m ∧ m Divides k ⇒ n Divides k ⌝);
a(REPEAT ∀_tac THEN rewrite_tac[divides_def]
	THEN REPEAT strip_tac);
a(∃_tac⌜k''*k'⌝ THEN asm_rewrite_tac[times_assoc_thm]);
val ⦏divides_trans_thm⦎ = save_pop_thm "divides_trans_thm";

=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n d⦁
	d Divides n 
⇒	(d Divides (m+n) ⇔ d Divides m)⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[divides_mod_thm]);
a(cases_tac⌜d = 0⌝ THEN1 (asm_rewrite_tac[] THEN taut_tac));
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[divides_def]);
a(lemma_tac⌜0 < d⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[] THEN once_rewrite_tac[plus_comm_thm]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac THEN ALL_FC_T rewrite_tac[mod_clauses]);
(* *** Goal "2" *** *)
a(all_asm_ante_tac THEN rewrite_tac[divides_def]
		THEN REPEAT strip_tac
		THEN all_var_elim_asm_tac1);
a(∃_tac⌜k' + k⌝ THEN PC_T1 "lin_arith" prove_tac[]);
val ⦏divides_plus_thm⦎ = save_pop_thm "divides_plus_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m d⦁ d Divides m*d ∧ d Divides d*m⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[∀_elim⌜d⌝ times_comm_thm]);
a(rewrite_tac[divides_def] THEN prove_tac[]);
val ⦏divides_times_thm⦎ = save_pop_thm "divides_times_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁
	0 < m
∧	n Divides m
⇒	0 < n ∧ n ≤ m⌝);
a(rewrite_tac[divides_def] THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(swap_nth_asm_concl_tac 1);
a(LEMMA_T⌜n = 0⌝ rewrite_thm_tac THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN cases_tac⌜k = 0⌝
	THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜1 ≤ k⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" prove_tac[]);
val ⦏divides_≤_thm⦎ = save_pop_thm "divides_≤_thm";

=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ 0 < m ⇒ {d | d Divides m} ∈ Finite⌝ );
a(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm);
a(∃_tac⌜{k | k < m + 1}⌝ THEN rewrite_tac[range_finite_size_thm]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_fc_tac[divides_≤_thm] THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏divisors_finite_thm⦎ = save_pop_thm "divisors_finite_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁m Divides 1 ⇔ m = 1⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T⌜0 < 1⌝ asm_tac THEN1 rewrite_tac[]);
a(all_fc_tac[divides_≤_thm]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[divides_mod_thm]);
val ⦏divides_1_thm⦎ = save_pop_thm "divides_1_thm";


=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n k⦁0 < k ⇒ (m + n) Mod k = (m Mod k + n Mod k) Mod k⌝);
a(REPEAT strip_tac);
a(all_fc_tac[div_mod_thm]);
a(TOP_ASM_T (ante_tac o ∀_elim⌜m⌝));
a(POP_ASM_T (ante_tac o ∀_elim⌜n⌝) THEN REPEAT strip_tac);
a(REPEAT (POP_ASM_T (fn th => conv_tac(LEFT_C(once_rewrite_conv[th])))));
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜∀a b c d⦁(a*k + b) + (c*k + d) = (a+c)*k + b + d⌝]);
a(ALL_FC_T rewrite_tac[div_mod_times_cancel_thm]);
val ⦏mod_plus_homomorphism_thm⦎ = save_pop_thm "mod_plus_homomorphism_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n k⦁0 < k ⇒ (m * n) Mod k = ((m Mod k) * (n Mod k)) Mod k⌝);
a(REPEAT strip_tac);
a(all_fc_tac[div_mod_thm]);
a(TOP_ASM_T (ante_tac o ∀_elim⌜m⌝));
a(POP_ASM_T (ante_tac o ∀_elim⌜n⌝) THEN REPEAT strip_tac);
a(REPEAT (POP_ASM_T (fn th => conv_tac(LEFT_C(once_rewrite_conv[th])))));
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜∀a b c d⦁(a*k + b) * (c*k + d) = (a*c*k + a*d +b*c)*k + b*d⌝]);
a(ALL_FC_T rewrite_tac[div_mod_times_cancel_thm]);
val ⦏mod_times_homomorphism_thm⦎ = save_pop_thm "mod_times_homomorphism_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n k⦁0 < k ⇒ (m ^ n) Mod k = ((m Mod k) ^ n) Mod k⌝);
a(REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN rewrite_tac[ℕ_exp_def]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac
	[mod_times_homomorphism_thm]);
a(ALL_FC_T asm_rewrite_tac[mod_clauses]);
val ⦏mod_ℕ_exp_thm⦎ = save_pop_thm "mod_ℕ_exp_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n:ℕ⦁ m ≤ n ⇔ m^2 ≤ n^2⌝);
a(lemma_tac⌜∀m n:ℕ⦁ m ≤ n ⇒ m^2 ≤ n^2⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[ℕ_exp_clauses, ≤_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1);
a(rewrite_tac[times_plus_distrib_thm, plus_assoc_thm]
	THEN prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN1 all_asm_fc_tac[]);
a(swap_nth_asm_concl_tac 1 THEN lemma_tac⌜n + 1 ≤ m⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(lemma_tac⌜n^2 < (n+1)^2⌝
	THEN1 (rewrite_tac[ℕ_exp_clauses] THEN PC_T1 "lin_arith" prove_tac[]));
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏square_≤_mono_thm⦎ = save_pop_thm "square_≤_mono_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁
	0 < m ∧ 0 < n ∧ 0 < m Mod n
⇒	∃a⦁ 0 < (a*m) Mod n
∧ 	∀b⦁ 0 < (b*m) Mod n ⇒ (a*m) Mod n ≤ (b*m) Mod n⌝);
a(REPEAT strip_tac);
a(PC_T1 "predicates" lemma_tac
	⌜ ∃i⦁ i ∈ { i | ∃a⦁0 < (a*m) Mod n ∧ i = (a*m) Mod n } ⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜m Mod n⌝ THEN REPEAT strip_tac);
a(∃_tac⌜1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_fc_tac[min_∈_thm]);
a(∃_tac⌜a⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 discard_tac);
a(PC_T1 "predicates" lemma_tac
	⌜ (b*m) Mod n ∈ { i | ∃a⦁0 < (a*m) Mod n ∧ i = (a*m) Mod n } ⌝
	THEN1 (REPEAT strip_tac THEN asm_prove_tac[]));
a(all_fc_tac[min_≤_thm]);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val ⦏gcd_consistent_lemma1⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n a d⦁
	0 < m ∧ 0 < n ∧ 0 < d
∧	m Mod d = 0 ∧ n Mod d = 0
⇒	((a*m) Mod n) Mod d = 0
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[mod_eq_0_thm]);
a(ante_tac(list_∀_elim[⌜a*m⌝, ⌜n⌝] div_mod_thm));
a(strip_tac THEN LEMMA_T
	⌜(((a*m) Div n)*n + (a*m) Mod n) Mod d = (a*m) Mod d⌝ ante_tac
	THEN1 POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(ALL_FC_T once_rewrite_tac[mod_plus_homomorphism_thm]);
a(all_var_elim_asm_tac1
	THEN rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv) times_assoc_thm]
	THEN ALL_FC_T rewrite_tac[mod_clauses]);
val ⦏gcd_consistent_lemma2⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀a b m n p r s⦁
	a*m = b*(n+1) + r
∧	m = p*r + s
⇒	∃q⦁(q*m) Mod (n+1) = s Mod (n+1)⌝);
a(REPEAT strip_tac);
a(∃_tac⌜n*p*a+1⌝);
a(scale_nth_asm_tac⌜n*p⌝ 2);
a(rewrite_tac[times_assoc_thm, times_plus_distrib_thm] THEN
	POP_ASM_T (asm_rewrite_thm_tac o rewrite_rule[times_assoc_thm]));
a(LEMMA_T ⌜
	n*p*(b*(n + 1) + r) + p * r + s =
	(n+1)*(p*b*n + p*r) + s⌝ rewrite_thm_tac THEN1
	PC_T1 "lin_arith" prove_tac[]);
a(rewrite_tac[rewrite_rule[](∀_elim⌜n+1⌝mod_clauses)]);
val ⦏gcd_consistent_lemma3⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀a b m n p r s⦁
	a*m = b*(n+1) + r
∧	n + 1 = p*r + s
⇒	∃q⦁(q*m) Mod (n+1) = s Mod (n+1)⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜∀x⦁(x*m) Mod (n + 1) = (x*m + n + 1) Mod (n + 1)⌝
	rewrite_thm_tac THEN1
		rewrite_tac[rewrite_rule[](∀_elim⌜n+1⌝mod_clauses)]);
a(∃_tac⌜n*p*a⌝);
a(scale_nth_asm_tac⌜n*p⌝ 2);
a(rewrite_tac[times_assoc_thm, times_plus_distrib_thm] THEN
	POP_ASM_T (rewrite_thm_tac o rewrite_rule[times_assoc_thm]));
a(LEMMA_T⌜∀x⦁x + n + 1 = x + p*r + s⌝ rewrite_thm_tac THEN1
	asm_rewrite_tac[]);
a(LEMMA_T ⌜
	n*p*(b*(n+1) + r) + p * r + s =
	(n+1)*(p*b*n + p*r) + s⌝ rewrite_thm_tac THEN1
	PC_T1 "lin_arith" prove_tac[]);
a(rewrite_tac[rewrite_rule[](∀_elim⌜n+1⌝mod_clauses)]);
val ⦏gcd_consistent_lemma4⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n k a⦁
	0 < m ∧ 0 < n ∧ 0 < m Mod n
∧	0 < (a*m) Mod n
∧ 	(∀b⦁ 0 < (b*m) Mod n ⇒ (a*m) Mod n ≤ (b*m) Mod n)
⇒	m Mod ((a*m) Mod n) = 0 ∧ n Mod ((a*m) Mod n) = 0⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN 
	LEMMA_T ⌜1 ≤ n⌝
		(strip_asm_tac o once_rewrite_rule[plus_comm_thm]
			o rewrite_rule[≤_def]) THEN1
	PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN contr_tac);
(* *** Goal "1" *** *)
a(ante_tac(list_∀_elim[ ⌜a⌝, ⌜(a*m) Div (i+1)⌝,
	⌜m⌝, ⌜i⌝, ⌜m Div ((a*m) Mod (i+1))⌝,
	⌜(a*m) Mod (i+1)⌝,
	⌜m Mod ((a*m) Mod (i+1))⌝ ]gcd_consistent_lemma3));
a(asm_tac (prove_rule[]⌜0 < i + 1⌝));
a(ALL_FC_T rewrite_tac[
	conv_rule(ONCE_MAP_C eq_sym_conv) div_mod_thm]);
a(lemma_tac⌜m Mod ((a*m) Mod (i + 1)) < (a*m) Mod (i+1)⌝
		THEN1 EXTEND_PC_T1 "'mmp1" all_fc_tac[mod_less_thm]);
a(lemma_tac⌜(a*m) Mod (i+1) < (i+1)⌝
	THEN1 (bc_thm_tac mod_less_thm THEN REPEAT strip_tac));
a(lemma_tac⌜m Mod ((a*m) Mod (i + 1)) < (i+1)⌝
	THEN1 all_fc_tac[less_trans_thm]);
a(ALL_FC_T rewrite_tac [less_div_mod_thm]);
a(contr_tac);
a(DROP_NTH_ASM_T 7 (ante_tac o ∀_elim⌜q⌝));
a(asm_rewrite_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(ante_tac(list_∀_elim[ ⌜a⌝, ⌜(a*m) Div (i+1)⌝,
	⌜m⌝, ⌜i⌝, ⌜(i+1) Div ((a*m) Mod (i+1))⌝,
	⌜(a*m) Mod (i+1)⌝,
	⌜(i+1) Mod ((a*m) Mod (i+1))⌝ ]gcd_consistent_lemma4));
a(asm_tac (prove_rule[]⌜0 < i + 1⌝));
a(ALL_FC_T rewrite_tac[
	conv_rule(ONCE_MAP_C eq_sym_conv) (div_mod_thm)]);
a(lemma_tac⌜(i+1) Mod ((a*m) Mod (i+1)) < (a*m) Mod (i+1)⌝
	THEN1 (bc_thm_tac mod_less_thm THEN REPEAT strip_tac));
a(lemma_tac⌜(a*m) Mod (i+1) < (i+1)⌝
	THEN1 (bc_thm_tac mod_less_thm THEN REPEAT strip_tac));
a(lemma_tac⌜(i+1) Mod ((a*m) Mod (i + 1)) < (i+1)⌝
	THEN1 all_fc_tac[less_trans_thm]);
a(ALL_FC_T rewrite_tac [less_div_mod_thm]);
a(contr_tac);
a(DROP_NTH_ASM_T 7 (ante_tac o ∀_elim⌜q⌝));
a(asm_rewrite_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏gcd_consistent_lemma5⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜Gcd⌝;
a(prove_∃_tac THEN REPEAT strip_tac);
a(cases_tac⌜m' = 0⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(∃_tac⌜n'⌝ THEN REPEAT strip_tac THEN 
	rewrite_tac[divides_0_thm, divides_refl_thm]);
(* *** Goal "2" *** *)
a(cases_tac⌜n' = 0⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "2.1" *** *)
a(∃_tac⌜m'⌝ THEN REPEAT strip_tac THEN 
	rewrite_tac[divides_0_thm, divides_refl_thm]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜0 < m' ∧ 0 < n'⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(cases_tac⌜m' Mod n' = 0⌝);
(* *** Goal "2.2.1" *** *)
a(∃_tac⌜n'⌝ THEN REPEAT strip_tac
	THEN rewrite_tac[divides_mod_thm]
	THEN ALL_FC_T asm_rewrite_tac[mod_clauses]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜0 < m' Mod n'⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN LIST_DROP_NTH_ASM_T [5, 6] discard_tac);
a(all_fc_tac [gcd_consistent_lemma1]);
a(all_fc_tac [gcd_consistent_lemma5]);
a(∃_tac⌜(a*m') Mod n'⌝ THEN asm_rewrite_tac[divides_mod_thm]);
a(∀_tac THEN cases_tac ⌜¬0 < d⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN1 all_var_elim_asm_tac1);
a(bc_thm_tac gcd_consistent_lemma2
	THEN REPEAT strip_tac);
val _ = save_consistency_thm ⌜Gcd⌝ (pop_thm());
=TEX
%%%%
%%%%

=SML
val ⦏gcd_def⦎ = save_thm("gcd_def", get_spec⌜Gcd⌝);
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁ 0 < m ∨ 0 < n ⇒ 0 < Gcd m n⌝);
a(REPEAT strip_tac THEN EXTEND_PC_T1 "'mmp1" all_fc_tac[gcd_def]);
(* *** Goal "1" *** *)
a(swap_nth_asm_concl_tac 2 THEN REPEAT strip_tac
	THEN ∃_tac ⌜n⌝);
a(LEMMA_T ⌜Gcd m n = 0⌝ rewrite_thm_tac THEN1 PC_T1"lin_arith" asm_prove_tac[]);
a(rewrite_tac[divides_0_thm] THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 2 THEN REPEAT strip_tac
	THEN ∃_tac ⌜m⌝);
a(LEMMA_T ⌜Gcd m n = 0⌝ rewrite_thm_tac THEN1 PC_T1"lin_arith" asm_prove_tac[]);
a(rewrite_tac[divides_0_thm] THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏gcd_pos_thm⦎ = save_pop_thm "gcd_pos_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n d⦁
	(0 < m ∨ 0 < n)
∧	d Divides m ∧ d Divides n ∧ Gcd m n Divides d
⇒	d = Gcd m n
⌝);
a(REPEAT strip_tac THEN all_fc_tac[gcd_def]
	THEN all_fc_tac[divides_antisym_thm]);
val ⦏gcd_unique_thm⦎ = save_pop_thm "gcd_unique_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ 0 < m ⇒ Gcd m m = m⌝);
a(REPEAT strip_tac THEN conv_tac eq_sym_conv);
a(bc_thm_tac gcd_unique_thm);
a(asm_rewrite_tac[divides_refl_thm]);
a(ALL_FC_T rewrite_tac[gcd_def]);
val ⦏gcd_idemp_thm⦎ = save_pop_thm "gcd_idemp_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n d⦁
	0 < m ∨ 0 < n
⇒	Gcd m n = Gcd n m
⌝);
a(REPEAT strip_tac THEN1 conv_tac eq_sym_conv
	THEN bc_thm_tac gcd_unique_thm);
(* *** Goal "1" duplicates "2" *** *)
a(fc_tac[gcd_def] THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 3 (ante_tac o list_∀_elim[⌜Gcd m n⌝, ⌜n⌝]));
a(asm_rewrite_tac[]);
val ⦏gcd_comm_thm⦎ = save_pop_thm "gcd_comm_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n d⦁
	0 < m ∨ 0 < n
⇒	Gcd (m + n) n = Gcd m n
⌝);
a(REPEAT ∀_tac THEN ⇒_T asm_tac);
a(bc_thm_tac gcd_unique_thm THEN asm_rewrite_tac[]);
a(lemma_tac⌜0 < m + n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(ALL_FC_T asm_rewrite_tac[gcd_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac  ⌜Gcd (m + n) n Divides m + n ∧ Gcd (m + n) n Divides n⌝ 
	THEN1 ALL_FC_T rewrite_tac[gcd_def]);
a(DROP_NTH_ASM_T 2 ante_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[divides_plus_thm]);
(* *** Goal "2" *** *)
a(ante_tac(list_∀_elim[⌜m⌝, ⌜n⌝] gcd_def)
	THEN asm_rewrite_tac[] THEN strip_tac);
a(lemma_tac⌜Gcd m n Divides m + n⌝ 
	THEN1 ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[divides_plus_thm]);
a(all_fc_tac[gcd_def]);
val ⦏gcd_plus_thm⦎ = save_pop_thm "gcd_plus_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜
	∀m n⦁	0 < m ∧ 0 < n ∧ 0 < m Mod n
	⇒	∃a⦁ 0 < (a*m) Mod n
	∧ 	(∀b⦁ 0 < (b*m) Mod n ⇒ (a*m) Mod n ≤ (b*m) Mod n)
	∧	Gcd m n = (a*m) Mod n
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[gcd_consistent_lemma1]);
a(∃_tac⌜a⌝ THEN asm_rewrite_tac[]);
a(conv_tac eq_sym_conv THEN bc_thm_tac gcd_unique_thm);
a(asm_rewrite_tac[divides_mod_thm]);
a(ALL_FC_T rewrite_tac[gcd_pos_thm, gcd_consistent_lemma5]);
a(bc_thm_tac gcd_consistent_lemma2);
a(ALL_FC_T asm_rewrite_tac[gcd_pos_thm]);
a(ante_tac (all_∀_elim gcd_def) THEN asm_rewrite_tac[]);
a(rewrite_tac[divides_mod_thm]);
a(ALL_FC_T rewrite_tac[gcd_pos_thm] THEN taut_tac);
val ⦏gcd_eq_mod_thm⦎ = save_pop_thm"gcd_eq_mod_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁
	0 < m ∧ 0 < n
⇒	Gcd m n = if m < n then Gcd m (n-m) else if m = n then m else Gcd (m-n) n
⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (pc_rule1"lin_arith" prove_rule[]
	⌜m < n ∨ m = n ∨ (¬m < n ∧ ¬ m = n ∧ n < m)⌝)
	THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜m + 1 ≤ n⌝ (strip_asm_tac o
	rewrite_rule[≤_def, pc_rule1"lin_arith" prove_rule[]
	⌜∀i⦁ (m + 1) + i = (i + 1) + m⌝])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(LEMMA_T ⌜0 < i + 1⌝ asm_tac THEN REPEAT strip_tac);
a(rewrite_tac[]);
a(ALL_FC_T once_rewrite_tac [gcd_comm_thm]);
a(ALL_FC_T rewrite_tac[gcd_plus_thm]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[gcd_idemp_thm]);
(* *** Goal "3" *** *)
a(LEMMA_T ⌜n + 1 ≤ m⌝ (strip_asm_tac o
	rewrite_rule[≤_def, pc_rule1"lin_arith" prove_rule[]
	⌜∀i⦁ (n + 1) + i = (i + 1) + n⌝])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T[2, 3, 4] discard_tac
	THEN all_var_elim_asm_tac1);
a(LEMMA_T ⌜0 < i + 1⌝ asm_tac THEN REPEAT strip_tac);
a(rewrite_tac[]);
a(ALL_FC_T rewrite_tac[gcd_plus_thm]);
val ⦏euclid_algorithm_thm⦎ = save_pop_thm "euclid_algorithm_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁
	0 < m ∧ 0 < n ∧ m ≤ n
⇒	∃a b⦁ b*n ≤ a*m ∧ Gcd m n = a*m - b*n 
⌝);
a(REPEAT strip_tac);
a(CASES_T ⌜n Divides m⌝ ante_tac THEN1 strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[divides_≤_thm]);
a(lemma_tac⌜n = m⌝ THEN_LIST
	[PC_T1 "lin_arith" asm_prove_tac[], all_var_elim_asm_tac]);
a(∃_tac⌜1⌝ THEN ∃_tac⌜0⌝ THEN rewrite_tac[]);
a( ALL_FC_T rewrite_tac[gcd_idemp_thm]);
(* *** Goal "2" *** *)
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[divides_mod_eq_0_thm]);
a(REPEAT strip_tac THEN lemma_tac⌜0 < m Mod n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_fc_tac[gcd_eq_mod_thm]);
a(rename_tac[] THEN POP_ASM_T rewrite_thm_tac);
a(∃_tac⌜a⌝ THEN ∃_tac⌜(a*m) Div n⌝);
a(once_rewrite_tac[taut_rule⌜∀p1 p2⦁p1 ∧ p2 ⇔ p1 ∧ (p1 ⇒ p2)⌝]);
a(ante_tac(list_∀_elim[⌜(a*m)⌝, ⌜n⌝] div_mod_thm)
	THEN REPEAT strip_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def]));
a(TOP_ASM_T (fn th => conv_tac(RIGHT_C(LEFT_C(
		once_rewrite_conv[eq_sym_rule th])))));
a(rewrite_tac[] THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏bezout_thm1⦎ = save_pop_thm "bezout_thm1";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁
	0 < m ∧ 0 < n 
⇒	(∃a b⦁ b*n ≤ a*m ∧ Gcd m n = a*m - b*n)
∨	(∃a b⦁ a*m ≤ b*n ∧ Gcd m n = b*n - a*m)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(strip_asm_tac (list_∀_elim[⌜m⌝, ⌜n⌝] ≤_cases_thm)
	THEN_LIST [
		∨_left_tac THEN bc_thm_tac bezout_thm1 THEN REPEAT strip_tac,
		∨_right_tac THEN ALL_FC_T once_rewrite_tac[gcd_comm_thm]]);
a(all_fc_tac[bezout_thm1]);
a(∃_tac⌜b⌝ THEN ∃_tac⌜a⌝ THEN asm_rewrite_tac[]);
val ⦏bezout_thm⦎ = save_pop_thm "bezout_thm";
=TEX
%%%%
%%%% PRIMES IN ℕ
%%%%

=SML
set_goal([], ⌜∀p⦁ p ∈ Prime ⇒ 0 < p⌝);
a(rewrite_tac[prime_def] THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏prime_0_less_thm⦎ = save_pop_thm"prime_0_less_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p⦁ p ∈ Prime ⇒ 2 ≤ p⌝);
a(rewrite_tac[prime_def] THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏prime_2_≤_thm⦎ = save_pop_thm"prime_2_≤_thm";
=TEX
%%%%
%%%% PRIMES IN ℕ
%%%%

=SML
set_goal([], ⌜∀p⦁ p ∈ Prime ⇔ (1 < p ∧ ∀d⦁d Divides p ⇔ d = 1 ∨ d = p)⌝);
a(rewrite_tac[prime_def, divides_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1);
a(list_spec_nth_asm_tac 2 [⌜k⌝, ⌜d⌝]);
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜p⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a(all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 2 (ante_tac o ∀_elim ⌜m⌝));
a(LEMMA_T⌜∃ k⦁ m * n = k * m⌝ asm_rewrite_thm_tac
	THEN1 (∃_tac⌜n⌝ THEN PC_T1 "lin_arith" prove_tac[]));
a(all_asm_ante_tac THEN cases_tac⌜m = 0⌝ THEN1 asm_rewrite_tac[]);
a(strip_asm_tac (∀_elim⌜n⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN1 rewrite_tac[]);
a(strip_asm_tac (∀_elim⌜i⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN1 rewrite_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏prime_divides_thm⦎ = save_pop_thm"prime_divides_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m p⦁
	0 < m ∧ p ∈ Prime
⇒	Gcd m p = 1 ∨ Gcd m p = p⌝);
a(REPEAT strip_tac
	THEN all_fc_tac[prime_0_less_thm]
		THEN all_asm_ante_tac);
a(rewrite_tac[prime_divides_thm] THEN REPEAT strip_tac);
a(lemma_tac⌜Gcd m p Divides p⌝ THEN1 ALL_FC_T rewrite_tac[gcd_def]);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
val ⦏gcd_prime_thm⦎ = save_pop_thm "gcd_prime_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p⦁
	(∀m n⦁	p Divides m*n
	⇒	p Divides m ∨ p Divides n)
∧	1 < p
⇒	p ∈ Prime
⌝);
a(rewrite_tac[prime_def, divides_mod_thm] THEN contr_tac);
a(all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 4 (ante_tac o list_∀_elim[⌜m⌝, ⌜n⌝]));
a(lemma_tac ⌜0 < m*n ⌝ THEN1
	PC_T1"lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[]);
a(ALL_FC_T rewrite_tac[m_div_mod_m_thm]);
a(lemma_tac ⌜0 < m ∧ 0 < n⌝ THEN1
	(LIST_DROP_NTH_ASM_T [1, 2, 3] discard_tac
		THEN contr_tac THEN lemma_tac⌜m = 0 ∨ n = 0⌝
		THEN_TRY all_var_elim_asm_tac1 THEN
			PC_T1"lin_arith" asm_prove_tac[]));
a(cases_tac⌜m < m*n⌝ THEN1 
	ALL_FC_T asm_rewrite_tac[less_div_mod_thm]);
(* *** Goal "1" *** *)
a(cases_tac⌜n < m*n⌝ THEN1 
	(ALL_FC_T asm_rewrite_tac[less_div_mod_thm] THEN
		PC_T1 "lin_arith" asm_prove_tac[]));
a(LEMMA_T⌜2 ≤ m⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1"lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN PC_T1"lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜2 ≤ n⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1"lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN PC_T1"lin_arith" asm_prove_tac[]);
val ⦏prime_lemma1⦎ = pop_thm ();
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p m n⦁
	p ∈ Prime ∧ p Divides m*n
⇒	p Divides m ∨ p Divides n
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(all_fc_tac[prime_0_less_thm]);
a(cases_tac⌜m = 0 ∨ n = 0⌝ THEN_TRY
	(asm_rewrite_tac[divides_0_thm]));
a(lemma_tac⌜0 < m ∧ 0 < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(cases_tac⌜Gcd m p = p⌝ THEN1
	(POP_ASM_T (once_rewrite_thm_tac o eq_sym_rule) THEN
		ALL_FC_T rewrite_tac[gcd_def] THEN REPEAT strip_tac));
a(cases_tac⌜Gcd n p = p⌝ THEN1
	(POP_ASM_T (once_rewrite_thm_tac o eq_sym_rule) THEN
		ALL_FC_T rewrite_tac[gcd_def]
			THEN REPEAT strip_tac));
a(lemma_tac⌜Gcd m p = 1 ∧ Gcd n p = 1⌝ THEN1
	(fc_tac[gcd_prime_thm]
		THEN LIST_DROP_NTH_ASM_T [1, 2] fc_tac
			THEN REPEAT strip_tac));
a(asm_rewrite_tac[divides_mod_thm]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜∀a⦁a = 0 ⇔ ¬0 < a⌝]);
a(contr_tac);
a(all_fc_tac[gcd_eq_mod_thm]);
a(LIST_DROP_NTH_ASM_T [1, 4] (MAP_EVERY ante_tac));
a(asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T (interval 1 14) discard_tac);
a(conv_tac (ONCE_MAP_C eq_sym_conv) THEN contr_tac);
a(LEMMA_T⌜((a' * m)*(a * n)) Mod p = 1⌝ ante_tac THEN1
	ALL_FC_T once_asm_rewrite_tac[mod_times_homomorphism_thm]);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[prime_def]));
a(ALL_FC_T asm_rewrite_tac[less_div_mod_thm]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[divides_mod_thm]
	THEN REPEAT strip_tac);
a(LEMMA_T⌜((a' * a)*(m * n)) Mod p = 0⌝ ante_tac THEN1
	(ALL_FC_T once_asm_rewrite_tac[mod_times_homomorphism_thm]
		THEN ALL_FC_T asm_rewrite_tac[mod_clauses]));
a(conv_tac(ONCE_MAP_C anf_conv) THEN PC_T1 "lin_arith" prove_tac[]);
val ⦏prime_lemma2⦎ = pop_thm ();
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p⦁
	p ∈ Prime
⇔	1 < p ∧ (∀m n⦁ p Divides m*n ⇒ p Divides m ∨ p Divides n)
⌝);
a(REPEAT strip_tac THEN_LIST [
	POP_ASM_T (strip_asm_tac o rewrite_rule[prime_def])
		THEN asm_rewrite_tac[],
	all_fc_tac[prime_lemma2],
	all_fc_tac[prime_lemma1]]);
val ⦏prime_thm⦎ = save_pop_thm "prime_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜ ∀m⦁ 1 < m ⇒ ∃p n⦁p ∈ Prime ∧ m = p*n ⌝);
a(∀_tac THEN cov_induction_tac⌜m:ℕ⌝);
a(REPEAT strip_tac);
a(cases_tac⌜m ∈ Prime⌝ THEN1
	(∃_tac⌜m⌝ THEN ∃_tac⌜1⌝ THEN asm_rewrite_tac[]));
a(POP_ASM_T (strip_asm_tac o rewrite_rule[prime_def]));
a(cases_tac⌜m' = 0⌝ THEN1
	(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(lemma_tac⌜1 < m'⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(cases_tac⌜¬m'< m⌝);
(* *** Goal "1" *** *)
a(cases_tac⌜n = 0⌝ THEN1
	(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(LEMMA_T⌜2 ≤ n⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN  PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [8] all_fc_tac);
a(∃_tac⌜p⌝ THEN ∃_tac⌜n'*n⌝ THEN asm_rewrite_tac[times_assoc_thm]);
val ⦏prime_divisor_thm1⦎ = save_pop_thm "prime_divisor_thm1";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜ ∀m⦁ 1 < m ⇒ ∃p⦁ p ∈ Prime ∧ p Divides m⌝);
a(rewrite_tac[divides_def] THEN REPEAT strip_tac
	THEN all_fc_tac[prime_divisor_thm1]);
a(∃_tac⌜p⌝ THEN REPEAT strip_tac THEN ∃_tac⌜n⌝
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏prime_divisor_thm⦎ = save_pop_thm"prime_divisor_thm";
=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜IndSum⋎N⌝;
a(∃_tac ⌜λa f⦁SetFold 0 ($ +) f a⌝);
a(∀_tac THEN rewrite_tac[] THEN bc_thm_tac(set_fold_def));
a(rewrite_tac[plus_assoc_thm]);
val _ = save_consistency_thm ⌜IndSum⋎N⌝ (pop_thm());
val ⦏ind_sum_ℕ_def⦎ = save_thm("ind_sum_ℕ_def", get_spec ⌜IndSum⋎N⌝);
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀ A f⦁
	A ∈ Finite
∧	Σ A f = 0
⇒	∀x⦁x ∈ A ⇒ f x = 0⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN POP_ASM_T ante_tac);
a(intro_∀_tac(⌜f⌝, ⌜f⌝));
a(finite_induction_tac⌜A⌝ THEN1 rewrite_tac[]);
a(ALL_FC_T rewrite_tac[ind_sum_ℕ_def]);
a(REPEAT ∀_tac THEN ⇒_tac);
a(REPEAT strip_tac THEN1 all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
val ⦏ind_sumℕ_0_thm⦎ = save_pop_thm "ind_sum_ℕ_0_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀ A; f g : 'a → ℕ⦁
	A ∈ Finite
∧	(∀x⦁x ∈ A ⇒ f x = g x)
⇒	Σ A f = Σ A g⌝);
a(REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜f⌝, ⌜f⌝));
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_sum_ℕ_def]);
a(REPEAT strip_tac);
a(lemma_tac⌜∀ x⦁ x ∈ A ⇒ f x = g x⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
a(ALL_ASM_FC_T rewrite_tac[ind_sum_ℕ_def]);
a(spec_nth_asm_tac 2 ⌜x⌝);
val ⦏ind_sum_ℕ_local_thm⦎ = save_pop_thm "ind_sum_ℕ_local_thm";
=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜IndProd⋎N⌝;
a(∃_tac ⌜λa f⦁SetFold 1 ($ *) f a⌝);
a(∀_tac THEN rewrite_tac[] THEN bc_thm_tac(set_fold_def));
a(PC_T1 "lin_arith" prove_tac[]);
val _ = save_consistency_thm ⌜IndProd⋎N⌝ (pop_thm());
val ⦏ind_prod_ℕ_def⦎ = save_thm("ind_prod_ℕ_def", get_spec ⌜IndProd⋎N⌝);
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀ A f⦁
	A ∈ Finite
∧	Π A f = 1
⇒	∀x⦁x ∈ A ⇒ f x = 1⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN POP_ASM_T ante_tac);
a(intro_∀_tac(⌜f⌝, ⌜f⌝));
a(finite_induction_tac⌜A⌝ THEN1 rewrite_tac[]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(REPEAT ∀_tac THEN ⇒_tac);
a(all_fc_tac[times_eq_1_thm]);
a(REPEAT strip_tac THEN1 all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
val ⦏ind_prod_ℕ_1_thm⦎ = save_pop_thm "ind_prod_ℕ_1_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀ A f⦁
	A ∈ Finite
∧	Π A f = 0
⇒	∃x⦁x ∈ A ∧ f x = 0⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(intro_∀_tac(⌜f⌝, ⌜f⌝));
a(finite_induction_tac⌜A⌝ THEN1 rewrite_tac[]);
(* *** Goal "1" *** *)
a(rewrite_tac[ind_prod_ℕ_def]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(rewrite_tac[times_eq_0_thm]);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
val ⦏ind_prod_ℕ_0_thm⦎ = save_pop_thm "ind_prod_ℕ_0_thm";

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀ A f g⦁
	A ∈ Finite
∧	(∀x⦁x ∈ A ⇒ f x = g x)
⇒	Π A f = Π A g⌝);
a(REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜f⌝, ⌜f⌝));
a(finite_induction_tac⌜A⌝
	THEN1 rewrite_tac[ind_prod_ℕ_def]);
a(REPEAT strip_tac);
a(lemma_tac⌜∀ x⦁ x ∈ A ⇒ f x = g x⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
a(ALL_ASM_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(spec_nth_asm_tac 2 ⌜x⌝ THEN asm_rewrite_tac[]);
val ⦏ind_prod_ℕ_local_thm⦎ = save_pop_thm "ind_prod_ℕ_local_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀ x : 'a ; f⦁
	Π {} f = 1 ∧ Π {x} f = f x⌝);
a(REPEAT ∀_tac THEN rewrite_tac[ind_prod_ℕ_def]);
a(lemma_tac⌜{} ∈ Finite⌝ THEN1 rewrite_tac[empty_finite_thm]);
a(LEMMA_T ⌜{x} = {x} ∪ {}⌝ once_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(LEMMA_T ⌜¬x ∈ {}⌝ asm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(ALL_FC_T pure_rewrite_tac[ind_prod_ℕ_def]);
a(rewrite_tac[ind_prod_ℕ_def]);
val ⦏ind_prod_ℕ_clauses⦎ = save_pop_thm "ind_prod_ℕ_clauses";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀ a b f⦁
	a ∈ Finite
∧	b ∈ Finite
⇒	Π (a ∪ b) f * Π (a ∩ b) f = (Π a f) * (Π b f)⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜a⌝ THEN1 rewrite_tac[ind_prod_ℕ_def]);
a(lemma_tac⌜a ∪ b ∈ Finite⌝ THEN1 asm_rewrite_tac[∪_finite_thm]);
a(cases_tac⌜¬x ∈ b⌝);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜¬x ∈ a ∪ b⌝ asm_tac THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]⌜∀A B C⦁(A ∪ B) ∪ C = A ∪ B ∪ C⌝]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(LEMMA_T⌜({x} ∪ a) ∩ b = a ∩ b⌝ asm_rewrite_thm_tac
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(asm_rewrite_tac[times_assoc_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜({x} ∪ a) ∪ b = a ∪ b ∧ ({x} ∪ a) ∩ b = {x} ∪ a ∩ b⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜a ∩ b ∈ Finite⌝ THEN1 ALL_FC_T rewrite_tac[∩_finite_thm]);
a(LEMMA_T ⌜¬x ∈ a ∩ b⌝ asm_tac THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(asm_rewrite_tac[pc_rule1"lin_arith" prove_rule[]⌜∀i j⦁ i * f x * j = f x * i * j⌝,
	times_assoc_thm]);
val ⦏ind_prod_ℕ_∪_thm⦎ = save_pop_thm "ind_prod_ℕ_∪_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀ a b f⦁
	a ∈ Finite
∧	b ∈ Finite
∧	a ∩ b = {}
⇒	Π (a ∪ b) f = (Π a f) * (Π b f)⌝);
a(REPEAT strip_tac);
a(ALL_FC_T (MAP_EVERY ante_tac)[ind_prod_ℕ_∪_thm]);
a(asm_rewrite_tac[ind_prod_ℕ_def]);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
val ⦏ind_prod_ℕ_disj_∪_thm⦎ = save_pop_thm "ind_prod_ℕ_disj_∪_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀ u f⦁
	u ∈ Finite
∧	u ⊆ Finite
∧	(∀a b⦁a ∈ u ∧ b ∈ u ∧ ¬a ∩ b = {} ⇒a = b)
⇒	Π (⋃u) f = Π u (λa⦁ Π a f)⌝);
a(REPEAT strip_tac);
a(REPEAT_N 2 (POP_ASM_T ante_tac));
a(intro_∀_tac(⌜f⌝, ⌜f⌝));
a(finite_induction_tac ⌜u⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[ind_prod_ℕ_def]);
(* *** Goal "2" *** *)
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀v w⦁⋃(v ∪ w) = ⋃v ∪ ⋃w⌝,
	⋃_singleton_thm]);
a(lemma_tac⌜x ∩ ⋃ u = {}⌝
	THEN1 PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(list_spec_nth_asm_tac 4 [⌜s⌝, ⌜x⌝]);
(* *** Goal "2.1.1" *** *)
a(REPEAT_N 4 (POP_ASM_T ante_tac)
	THEN PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(all_var_elim_asm_tac);
(* *** Goal "2.2" *** *)
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀y v f⦁ {y} ∪ v ⊆ f ⇒ y ∈ f ∧ v ⊆ f⌝]);
a(all_fc_tac[⋃_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def,
	ind_prod_ℕ_disj_∪_thm]);
a(LEMMA_T ⌜Π (⋃ u) f = Π u (λ u⦁ Π u f)⌝ rewrite_thm_tac);
a(DROP_NTH_ASM_T 8 (strip_asm_tac o ∀_elim⌜f⌝));
a(list_spec_nth_asm_tac 9 [⌜u'⌝, ⌜b⌝]);
val ⦏ind_prod_ℕ_⋃_thm⦎ = save_pop_thm "ind_prod_ℕ_⋃_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀A f d⦁
	A ∈ Finite
∧	0 < d
⇒	Π A f Mod d = (Π A (λk⦁ f k Mod d)) Mod d⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[ind_prod_ℕ_def]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(ALL_FC_T once_rewrite_tac[mod_times_homomorphism_thm]);
a(asm_rewrite_tac[]);
a(ALL_FC_T rewrite_tac[mod_clauses]);
val ⦏ind_prod_ℕ_mod_thm⦎ = save_pop_thm "ind_prod_ℕ_mod_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀A f⦁
	A ∈ Finite
⇒	Π A (λk⦁1) = 1⌝);
a(REPEAT strip_tac);
a(finite_induction_tac⌜A⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[ind_prod_ℕ_def]);
(* *** Goal "2" *** *)
a(ALL_FC_T asm_rewrite_tac[ind_prod_ℕ_def]);
val ⦏ind_prod_ℕ_k_1_thm⦎ = save_pop_thm "ind_prod_ℕ_k_1_thm";

=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ Π {k | 1 ≤ k ∧ k ≤ m} (λk⦁k) = m!⌝);
a(REPEAT strip_tac);
a(induction_tac⌜m⌝ THEN rewrite_tac[factorial_def]);
(* *** Goal "1" *** *)
a(rewrite_tac[ind_prod_ℕ_def,
	pc_rule1"lin_arith" prove_rule[]⌜∀k⦁¬(1 ≤ k ∧ k = 0)⌝,
	pc_rule1"sets_ext1" prove_rule[]⌜{x|F}={}⌝]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜{k| 1 ≤ k ∧ k ≤ m + 1} =
	{m+1} ∪ {k| 1 ≤ k ∧ k ≤ m}⌝
	rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" REPEAT strip_tac
		THEN_TRY all_var_elim_asm_tac1
		THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]));
a(LEMMA_T ⌜¬m+1 ∈ {k|1 ≤ k ∧ k ≤ m}⌝
	asm_tac
	THEN1 rewrite_tac[]);
a(lemma_tac⌜{k|1 ≤ k ∧ k ≤ m} ∈ Finite⌝
	THEN1 rewrite_tac[range_finite_size_thm1]);
a(ALL_FC_T asm_rewrite_tac[ind_prod_ℕ_def]);
val ⦏factorial_ind_prod_ℕ_thm⦎ = save_pop_thm "factorial_ind_prod_ℕ_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ 0 < m ⇒ (m - 1)! = Π {k | 1 ≤ k ∧ k < m} (λk⦁k)⌝);
a(∀_tac THEN STRIP_T (strip_asm_tac o
	rewrite_rule[pc_rule1"lin_arith" prove_rule[]
	⌜∀m⦁0 < m ⇔ 1 ≤ m⌝, ≤_def]));
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜∀k⦁k < 1 + i ⇔ k ≤ i⌝,
	factorial_ind_prod_ℕ_thm]);
val ⦏factorial_ind_prod_ℕ_thm1⦎ = save_pop_thm "factorial_ind_prod_ℕ_thm1";

=TEX
%%%%
%%%%

=TEX
=SML
val ⦏mod_3_plus_thm⦎ = rewrite_rule[](all_∀_intro(list_∀_elim[⌜m:ℕ⌝, ⌜n:ℕ⌝, ⌜3⌝]mod_plus_homomorphism_thm));
=TEX
=SML
val ⦏mod_3_times_thm⦎ = rewrite_rule[](all_∀_intro(list_∀_elim[⌜m:ℕ⌝, ⌜n:ℕ⌝, ⌜3⌝]mod_times_homomorphism_thm));
=TEX
=SML
val ⦏mod_3_ℕ_exp_thm⦎ = rewrite_rule[](all_∀_intro(list_∀_elim[⌜m:ℕ⌝, ⌜n:ℕ⌝, ⌜3⌝]mod_ℕ_exp_thm));
=TEX
=SML
val ⦏mod_3_clauses⦎ = rewrite_rule[](∀_elim⌜3⌝ mod_clauses);
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀digits; n:ℕ⦁
	Σ {i | i < n} (λi⦁digits i * 10 ^ i) Mod 3 =
	Σ {i | i < n} (λi⦁digits i) Mod 3
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜n⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[ind_sum_ℕ_def, pc_rule1"sets_ext1" prove_rule[]⌜{x|F} = {}⌝]);
(* *** Goal "1" *** *)
a(PC_T1 "predicates" lemma_tac⌜{i|i < n + 1} = {n} ∪ {i|i < n} ∧ ¬n ∈ {i|i < n}
	∧ {i|i < n} ∈ Finite⌝
	THEN1 rewrite_tac[range_finite_size_thm]);
(* *** Goal "2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(ALL_FC_T asm_rewrite_tac[ind_sum_ℕ_def]);
a(once_rewrite_tac[mod_3_plus_thm]);
a(asm_rewrite_tac[]);
a(once_rewrite_tac[mod_3_times_thm]);
a(once_rewrite_tac[mod_3_ℕ_exp_thm]);
a(LEMMA_T⌜1 ^ n = 1⌝ (fn th => rewrite_tac[th, mod_3_clauses]));
a(DROP_ASMS_T discard_tac
	THEN induction_tac⌜n⌝ THEN asm_rewrite_tac[ℕ_exp_def]);
val ⦏div_3_rule_thm1⦎ = save_pop_thm "div_3_rule_thm1";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀digits; n:ℕ⦁
	3 Divides Σ {i | i < n} (λi⦁digits i * 10 ^ i) ⇔
	3 Divides Σ {i | i < n} (λi⦁digits i)
⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[divides_mod_thm, div_3_rule_thm1]);
val ⦏div_3_rule_thm⦎ = save_pop_thm "div_3_rule_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜ 2 ∈ Prime ⌝);
a(rewrite_tac[prime_divides_thm] THEN ∀_tac);
a(cases_tac⌜d = 0⌝ THEN1 asm_rewrite_tac[divides_0_thm]);
a(lemma_tac⌜1 Divides 2 ∧ 2 Divides 2⌝
	THEN1 rewrite_tac[divides_mod_thm]);
a(cases_tac⌜d = 1⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜d = 2⌝ THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜0 < 2⌝ asm_tac THEN REPEAT strip_tac);
a(contr_tac THEN all_fc_tac[divides_≤_thm]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏prime_2_thm⦎ = save_pop_thm "prime_2_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜ ¬ Prime ∈ Finite ⌝);
a(contr_tac);
a(lemma_tac⌜¬ Π Prime (λm⦁m) = 0⌝);
(* *** Goal "1" *** *)
a(contr_tac THEN all_fc_tac[ind_prod_ℕ_0_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]);
a(contr_tac THEN all_var_elim_asm_tac1 THEN all_fc_tac[prime_0_less_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜1 < Π Prime (λm⦁m) + 1⌝ asm_tac THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_fc_tac[prime_divisor_thm1]);
a(POP_ASM_T ante_tac);
a(lemma_tac⌜∃A⦁ Prime = {p} ∪ A ∧ ¬p ∈ A ∧ A ⊆ Prime⌝
	THEN1 (∃_tac⌜Prime \ {p}⌝
		THEN POP_ASM_T ante_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(all_fc_tac[⊆_finite_thm]);
a(ALL_FC_T asm_rewrite_tac[ind_prod_ℕ_def]);
a(LEMMA_T⌜∀i j⦁¬i Mod p = j Mod p ⇒ ¬i = j⌝ bc_thm_tac
	THEN1 (contr_tac THEN all_var_elim_asm_tac1));
a(all_fc_tac[prime_0_less_thm]);
a(ALL_FC_T rewrite_tac[mod_clauses] THEN contr_tac);
a(LEMMA_T⌜p Divides 1⌝ ante_tac THEN1 asm_rewrite_tac[divides_mod_thm]);
a(rewrite_tac[divides_1_thm]);
a(contr_tac THEN all_var_elim_asm_tac1 THEN all_fc_tac [prime_2_≤_thm]);
val ⦏prime_infinite_thm⦎ = save_pop_thm "prime_infinite_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p A f⦁
	A ∈ Finite
∧	p ∈ Prime
∧	p Divides Π A f
⇒	∃x⦁ x ∈ A ∧ p Divides f x
⌝);
a(REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜f⌝, ⌜f⌝));
a(finite_induction_tac⌜A⌝);
(* *** Goal "1" *** *)
a(rewrite_tac [ind_prod_ℕ_def, divides_1_thm]);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[prime_def]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac [ind_prod_ℕ_def]);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 (fn th => fc_tac[rewrite_rule[prime_thm] th]));
(* *** Goal "2.1" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
val ⦏prime_Π_thm⦎ = save_pop_thm "prime_Π_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p q⦁
	p ∈ Prime ∧ q ∈ Prime ∧ p Divides q ⇒ p = q
⌝);
a(rewrite_tac[prime_def, divides_def]
	THEN REPEAT strip_tac);
a(cases_tac⌜k = 1⌝
	THEN1 (all_var_elim_asm_tac1
		THEN rewrite_tac[]));
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(all_var_elim_asm_tac1);
val ⦏prime_divides_prime_thm⦎ = save_pop_thm "prime_divides_prime_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p m n⦁
	p ∈ Prime ∧ p Divides m ^ n
⇒	m = 0 ∨ p Divides m
⌝);
a(REPEAT ∀_tac THEN cases_tac⌜m=0⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(swap_nth_asm_concl_tac 1 THEN induction_tac⌜n⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[ℕ_exp_def, divides_1_thm]);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[divides_mod_thm,
	div_mod_1_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[ℕ_exp_def] THEN swap_nth_asm_concl_tac 1);
a(DROP_NTH_ASM_T 3 (fn th => all_fc_tac[rewrite_rule[prime_thm] th]));
val ⦏divides_ℕ_exp_thm⦎ = save_pop_thm "divides_ℕ_exp_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n d⦁
	¬m = 0
⇒	(d*m Divides m*n ⇔ d Divides n)
⌝);
a(rewrite_tac[divides_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜k⌝ THEN bc_thm_tac times_cancel_thm);
a(∃_tac⌜m⌝ THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(∃_tac⌜k⌝ THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏divides_cancel_thm⦎ = save_pop_thm "divides_cancel_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀e⦁
	{k | ¬e k = 0} ∈ Finite
∧	{k | ¬e k = 0} ⊆ Prime
⇒	∀k⦁e k =
	if	k ∈ Prime
	then	Max {i | k^i Divides Π {k | ¬e k = 0} (λ p⦁ p ^ e p)}
	else	0
⌝);
a(REPEAT strip_tac);
a(cases_tac⌜¬k ∈ Prime⌝ THEN asm_rewrite_tac[]
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(conv_tac eq_sym_conv THEN bc_thm_tac(get_spec⌜Max⌝)
	THEN rewrite_tac[]);
a(cases_tac⌜e k = 0⌝ THEN1 asm_rewrite_tac[ℕ_exp_def]);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN1 rewrite_tac[divides_mod_thm, div_mod_1_thm]);
a(contr_tac THEN lemma_tac⌜1 ≤ i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(lemma_tac⌜k Divides Π {k|¬ e k = 0} (λ p⦁ p ^ e p)⌝
	THEN1 bc_thm_tac divides_trans_thm);
(* *** Goal "1.1" *** *)
a(∃_tac⌜k^i⌝ THEN REPEAT strip_tac);
a(all_fc_tac[ℕ_exp_divides_thm]);
a(POP_ASM_T (rewrite_thm_tac o rewrite_rule[ℕ_exp_1_thm]));
(* *** Goal "1.2" *** *)
a(all_fc_tac[prime_Π_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]
	THEN contr_tac);
a(lemma_tac⌜x ∈ Prime⌝ THEN PC_T1 "sets_ext1" asm_prove_tac[]);
a(cases_tac⌜x = 0⌝
	THEN1 (all_var_elim_asm_tac1
		THEN all_fc_tac[prime_0_less_thm]));
a(all_fc_tac[divides_ℕ_exp_thm]);
a(all_fc_tac[prime_divides_prime_thm] THEN all_var_elim_asm_tac1);
(* *** Goal "2" *** *)
a(LEMMA_T⌜¬k ∈ {j|¬e j = 0 ∧ ¬j = k}⌝ asm_tac
	THEN1 REPEAT strip_tac);
a(LEMMA_T⌜{j|¬e j = 0} = {k} ∪ {j|¬e j = 0 ∧ ¬j = k}⌝ 
	rewrite_thm_tac
	THEN1 (DROP_NTH_ASM_T 2 ante_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(lemma_tac⌜{j|¬e j = 0 ∧ ¬j = k} ⊆ {j|¬e j = 0}⌝ 
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(once_rewrite_tac[times_comm_thm]);
a(rewrite_tac[divides_def] THEN prove_tac[]);
(* *** Goal "2.2" *** *)
a(contr_tac THEN lemma_tac⌜e k + 1 ≤ i⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜k ^ (e k + 1) Divides
	k ^ e k * Π {j|¬ e j = 0 ∧ ¬ j = k} (λ p⦁ p ^ e p)⌝ ante_tac
	THEN1 bc_thm_tac divides_trans_thm);
(* *** Goal "2.2.1" *** *)
a(∃_tac⌜k^i⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℕ_exp_divides_thm THEN REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a(rewrite_tac[ℕ_exp_def]);
a(all_fc_tac[prime_0_less_thm]);
a(cases_tac⌜k ^ e k = 0⌝
	THEN1 (POP_ASM_T ante_tac
		THEN asm_rewrite_tac[times_eq_0_thm, ℕ_exp_eq_0_thm]
		THEN strip_tac THEN all_var_elim_asm_tac1));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[divides_cancel_thm]);
a(contr_tac THEN all_fc_tac[prime_Π_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]
	THEN contr_tac);
a(lemma_tac⌜x ∈ Prime⌝ THEN PC_T1 "sets_ext1" asm_prove_tac[]);
a(cases_tac⌜x = 0⌝
	THEN1 (all_var_elim_asm_tac1
		THEN all_fc_tac[prime_0_less_thm]));
a(all_fc_tac[divides_ℕ_exp_thm]);
a(all_fc_tac[prime_divides_prime_thm] THEN all_var_elim_asm_tac1);
val ⦏exponent_thm⦎ = save_pop_thm "exponent_thm";

=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ 0 < m
⇒	∃⋎1 e⦁
	{k | ¬e k = 0} ∈ Finite
∧	{k | ¬e k = 0} ⊆ Prime
∧	m = Π {k | ¬e k = 0} (λp⦁ p ^ e p)
⌝);
a(lemma_tac⌜∀m⦁ 0 < m
⇒	∃ e⦁
	{k | ¬e k = 0} ∈ Finite
∧	{k | ¬e k = 0} ⊆ Prime
∧	m = Π {k | ¬e k = 0} (λp⦁ p ^ e p)
⌝);
a(∀_tac);
a(cov_induction_tac⌜m⌝);
a(cases_tac⌜m = 0⌝ THEN1 asm_rewrite_tac[]);
a(cases_tac⌜m = 1⌝ THEN1 all_var_elim_asm_tac1
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(POP_ASM_T discard_tac THEN ∃_tac⌜λm:ℕ⦁0⌝
	THEN rewrite_tac[pc_rule1"sets_ext1" prove_rule[]
		⌜{x|F} = {}⌝, ind_prod_ℕ_def,
		empty_finite_thm]
	THEN contr_tac);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜1 < m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [2, 3, 4] discard_tac);
a(all_fc_tac[prime_divisor_thm1] THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜n⌝));
(* *** Goal "1.2.1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 1);
a(DROP_NTH_ASM_T 2 ante_tac THEN cases_tac⌜n = 0⌝
	THEN1 asm_rewrite_tac[] THEN REPEAT strip_tac);
a(all_fc_tac[prime_2_≤_thm]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 2 ante_tac THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(lemma_tac⌜n = 0⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.2.3" *** *)
a(∃_tac⌜λk⦁if k = p then e p + 1 else e k⌝
	THEN rewrite_tac[]);
a(LEMMA_T ⌜{k|¬ (if k = p then e p + 1 else e k) = 0} =
	{p} ∪ {k|¬ e k = 0}⌝
	(fn th => asm_rewrite_tac[th, ∪_finite_thm, singleton_finite_thm])
	THEN1(PC_T1 "sets_ext1" rewrite_tac[] THEN strip_tac
		THEN cases_tac⌜x = p⌝ THEN asm_rewrite_tac[])
	THEN REPEAT strip_tac);
(* *** Goal "1.2.3.1" *** *)
a(LIST_DROP_NTH_ASM_T [2, 4] (MAP_EVERY ante_tac));
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.2.3.2" *** *)
a(cases_tac⌜e p = 0⌝);
(* *** Goal "1.2.3.2.1" *** *)
a(LEMMA_T⌜¬p ∈ {k|¬ e k = 0}⌝ asm_tac THEN1 asm_rewrite_tac[]);
a(ALL_FC_T asm_rewrite_tac[ind_prod_ℕ_def]);
a(rewrite_tac[ℕ_exp_1_thm]
	THEN  bc_tac[prove_rule[]⌜∀x y⦁x = y ⇒p*x = p*y⌝,
		ind_prod_ℕ_local_thm]
	THEN REPEAT strip_tac);
a(rewrite_tac[]);
a(cases_tac⌜x = p⌝ THEN1 all_var_elim_asm_tac);
a(asm_rewrite_tac[]);
(* *** Goal "1.2.3.2.2" *** *)
a(LEMMA_T ⌜{p} ∪ {k|¬ e k = 0} = {p} ∪ {k|¬ e k = 0 ∧ ¬k = p}⌝
	rewrite_thm_tac
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T ⌜{k|¬ e k = 0} = {p} ∪ {k|¬ e k = 0 ∧ ¬k = p}⌝
	rewrite_thm_tac
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜¬p ∈ {k|¬ e k = 0 ∧ ¬k = p}⌝ asm_tac
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜{k|¬ e k = 0 ∧ ¬k = p} ∈ Finite⌝ strip_asm_tac
	THEN1 (bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{k|¬ e k = 0}⌝
		THEN REPEAT strip_tac
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(rewrite_tac[ℕ_exp_def, times_assoc_thm]);
a(bc_tac[prove_rule[]⌜∀x y⦁x = y ∧ a = b ⇒ p*a*x = p*b*y⌝,
		ind_prod_ℕ_local_thm]
	THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
a(∃⋎1_tac⌜e⌝ THEN REPEAT strip_tac);
a(ALL_FC_T once_rewrite_tac[exponent_thm]);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(DROP_NTH_ASM_T  3 (rewrite_thm_tac o eq_sym_rule));
val ⦏unique_factorisation_thm⦎ = save_pop_thm "unique_factorisation_thm";
=TEX
%%%%
%%%%

=SML
(*
drop_main_goal();
*)
push_consistency_goal⌜Exponent⌝;
a(prove_∃_tac THEN REPEAT strip_tac);
a(cases_tac⌜0 < m'⌝ THEN asm_rewrite_tac[]);
a(all_fc_tac[unique_factorisation_thm]);
a(∃_tac⌜e⌝ THEN asm_rewrite_tac[]);
save_consistency_thm ⌜Exponent⌝ (pop_thm());
val ⦏exponent_def⦎ = get_spec⌜Exponent⌝;
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀P Q e⦁ 
	P ∈ Finite
∧	P ⊆ Prime
∧	Q ∈ Finite
∧	Q ⊆ Prime
∧	Π P (λ k⦁ k ^ (e k + 1)) = Π Q (λk⦁ k ^ (e k + 1))
⇒	P = Q⌝);
a(lemma_tac⌜∀P Q e⦁ 
	P ∈ Finite
∧	P ⊆ Prime
∧	Q ∈ Finite
∧	Q ⊆ Prime
∧	Π P (λ k⦁ k ^ (e k + 1)) = Π Q (λk⦁ k ^ (e k + 1))
⇒	Q ⊆ P⌝);
a(REPEAT strip_tac THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(lemma_tac⌜x Divides Π P (λ k⦁ k ^ (e k + 1))⌝);
(* *** Goal "1.1" *** *)
a(DROP_NTH_ASM_T 2 rewrite_thm_tac);
a(lemma_tac⌜Q \ {x} ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜Q⌝
		THEN REPEAT strip_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜¬x ∈ Q \ {x}⌝ asm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(LEMMA_T⌜Q = {x} ∪ (Q \ {x})⌝ once_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(rewrite_tac[divides_def, ℕ_exp_def]);
a(∃_tac⌜x ^ e x * Π (Q \ {x}) (λ k⦁ k * k ^ e k)⌝
	THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜x ∈ Prime⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[prime_Π_thm]);
a(POP_ASM_T ante_tac THEN ALL_FC_T rewrite_tac[] THEN strip_tac);
a(lemma_tac⌜x' ∈ Prime⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜¬x' = 0⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac1
	THEN all_fc_tac[prime_0_less_thm]));
a(all_fc_tac[divides_ℕ_exp_thm]);
a(LEMMA_T ⌜x = x'⌝ asm_rewrite_thm_tac);
a(ALL_FC_T rewrite_tac[prime_divides_prime_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜∀a b⦁a = b ⇔ a ⊆ b ∧ b ⊆ a⌝]);
a(REPEAT strip_tac THEN DROP_NTH_ASM_T 6 bc_thm_tac
	THEN ∃_tac⌜e⌝
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val ⦏prime_divisors_unique_thm⦎ = save_pop_thm "prime_divisors_unique_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ 
	0 < m
⇒	{p | p ∈ Prime ∧ p Divides m} ∈ Finite⌝);
a(REPEAT strip_tac THEN bc_thm_tac ⊆_finite_thm);
a(∃_tac⌜{d | d Divides m}⌝ THEN ALL_FC_T rewrite_tac[divisors_finite_thm]);
a(PC_T1 "sets_ext1" prove_tac[]);
val ⦏prime_divisors_finite_thm⦎ = save_pop_thm "prime_divisors_finite_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁	m ∈ SquareFree ⇒ 0 < m ⌝);
a(rewrite_tac[square_free_def, pc_rule1 "lin_arith" prove_rule[]
	⌜∀a⦁0 < a ⇔ ¬a = 0⌝] THEN contr_tac
	THEN all_var_elim_asm_tac1);
a(swap_nth_asm_concl_tac 1 THEN strip_tac);
a(∃_tac⌜0⌝ THEN rewrite_tac[divides_0_thm]);
val ⦏square_free_0_less_thm⦎ = save_pop_thm "square_free_0_less_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁
	m ∈ SquareFree ⇔ ∀p⦁p ∈ Prime ⇒ ¬p^2 Divides m
⌝);
a(rewrite_tac[square_free_def, ℕ_exp_clauses] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[prime_2_≤_thm]);
a(swap_nth_asm_concl_tac 2 THEN all_asm_fc_tac[]);
a(all_var_elim_asm_tac1);
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 1);
a(cases_tac⌜n = 0⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "2.1" *** *)
a(rewrite_tac[divides_0_thm]);
a(swap_nth_asm_concl_tac 1 THEN REPEAT strip_tac);
a(∃_tac⌜2⌝ THEN asm_rewrite_tac[prime_2_thm, divides_0_thm]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜1 < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_fc_tac[prime_divisor_thm1] THEN all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(swap_nth_asm_concl_tac 1 THEN bc_thm_tac divides_trans_thm);
a(∃_tac⌜(p * n') * p * n'⌝ THEN REPEAT strip_tac);
a(rewrite_tac[divides_def]);
a(∃_tac⌜n' * n'⌝ THEN PC_T1 "lin_arith" prove_tac[]);
val ⦏square_free_prime_thm⦎ = save_pop_thm "square_free_prime_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀P Q⦁ 
	P ∈ Finite
∧	P ⊆ Prime
⇒	Π P (λ k⦁ k) ∈ SquareFree⌝);
a(rewrite_tac[square_free_prime_thm, ℕ_exp_clauses,
	divides_def] THEN contr_tac);
a(lemma_tac⌜p Divides Π P (λ k⦁ k)⌝
	THEN1 (asm_rewrite_tac[] THEN rewrite_tac[divides_def]
		THEN  ∃_tac⌜k*p⌝ THEN PC_T1 "lin_arith" prove_tac[]));
a(all_fc_tac[prime_Π_thm]);
a(lemma_tac⌜x = p⌝
	THEN1 (conv_tac eq_sym_conv 
		THEN bc_thm_tac prime_divides_prime_thm
		THEN REPEAT strip_tac THEN PC_T1 "sets_ext1" asm_prove_tac[])
	THEN all_var_elim_asm_tac);
a(LIST_DROP_NTH_ASM_T [1, 3] discard_tac);
a(swap_nth_asm_concl_tac 2);
a(lemma_tac⌜P \ {p} ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜P⌝
		THEN REPEAT strip_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜¬p ∈ P \ {p}⌝ asm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(LEMMA_T⌜P = {p} ∪ (P \ {p})⌝ once_rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(all_fc_tac[prime_0_less_thm]);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]⌜k*p*p=p*p*k⌝]);
a(contr_tac THEN all_fc_tac[times_cancel_thm]);
a(lemma_tac⌜p Divides Π (P \ {p}) (λ k⦁ k)⌝
	THEN1 (rewrite_tac [divides_def] THEN ∃_tac⌜k⌝
		THEN asm_rewrite_tac[] THEN PC_T1 "lin_arith" prove_tac[]));
a(all_fc_tac[prime_Π_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[] THEN swap_nth_asm_concl_tac 1);
a(conv_tac eq_sym_conv 
		THEN bc_thm_tac prime_divides_prime_thm
		THEN REPEAT strip_tac THEN PC_T1 "sets_ext1" asm_prove_tac[]);
val ⦏factorisation_square_free_thm⦎ = save_pop_thm "factorisation_square_free_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m d⦁ 
	d Divides m
∧	m ∈ SquareFree
⇒	d ∈ SquareFree⌝);
a(rewrite_tac[square_free_def] THEN REPEAT strip_tac);
a(all_fc_tac[divides_trans_thm]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
val ⦏divides_square_free_thm⦎ = save_pop_thm "divides_square_free_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ 
	m ∈ SquareFree
⇒	m = Π {p|p ∈ Prime ∧ p Divides m} (λk⦁k)⌝);
a(strip_tac THEN cov_induction_tac⌜m:ℕ⌝ THEN REPEAT strip_tac);
a(all_fc_tac[square_free_0_less_thm]);
a(cases_tac⌜m = 1⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(LEMMA_T⌜∀p⦁¬(p ∈ Prime ∧ p Divides 1)⌝ rewrite_thm_tac
	THEN1 (rewrite_tac[divides_1_thm] THEN contr_tac
		THEN all_var_elim_asm_tac1
		THEN all_fc_tac[prime_2_≤_thm]));
a(rewrite_tac[ind_prod_ℕ_def, pc_rule1"sets_ext1" prove_rule[]
	⌜{x|F} = {}⌝]);
(* *** Goal "2" *** *)
a(lemma_tac⌜1 < m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN LIST_DROP_NTH_ASM_T [2, 3] discard_tac);
a(all_fc_tac[prime_divisor_thm1]);
a(cases_tac⌜n = 1⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "2.1" *** *)
a(rewrite_tac[]);
a(LEMMA_T ⌜{p'|p' ∈ Prime ∧ p' Divides p} = {p}⌝
	(fn th => rewrite_tac[th, ind_prod_ℕ_clauses]));
a(PC_T1 "sets_ext1" asm_rewrite_tac[]);
a(REPEAT strip_tac THEN1 all_fc_tac[prime_divides_prime_thm]
	THEN all_var_elim_asm_tac
	THEN asm_rewrite_tac[divides_refl_thm]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜¬n = 0⌝
	THEN1 (contr_tac THEN all_var_elim_asm_tac1
		THEN DROP_ASM_T ⌜1 < p * 0⌝ ante_tac
		THEN rewrite_tac[]));
a(all_fc_tac[prime_2_≤_thm]);
a(all_var_elim_asm_tac1);
a(lemma_tac⌜n < p * n⌝);
(* *** Goal "2.2.1" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def]) THEN all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜n Divides p*n⌝ THEN1 rewrite_tac[divides_times_thm]);
a(all_fc_tac[divides_square_free_thm]);
a(lemma_tac⌜¬p Divides n⌝);
(* *** Goal "2.2.2.1" *** *)
a(rewrite_tac[divides_def] THEN swap_nth_asm_concl_tac 9);
a(rewrite_tac[square_free_prime_thm] THEN strip_tac);
a(∃_tac⌜p⌝ THEN REPEAT strip_tac);
a(rewrite_tac[ℕ_exp_clauses]);
a(rewrite_tac[divides_def] THEN rename_tac[]
	THEN asm_rewrite_tac[]);
a(∃_tac⌜k⌝ THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T[11] all_fc_tac);
a(lemma_tac⌜0 < p*n⌝ THEN1 (rewrite_tac[times_eq_0_thm,
		pc_rule1"lin_arith" prove_rule[]
		⌜∀a b⦁0 < a ⇔ ¬a = 0⌝]
	THEN contr_tac THEN all_var_elim_asm_tac1
	THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(lemma_tac⌜{p'|p' ∈ Prime ∧ p' Divides p * n} \ {p} ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm 
		THEN ∃_tac⌜{p'|p' ∈ Prime ∧ p' Divides p * n}⌝
		THEN ALL_FC_T rewrite_tac[prime_divisors_finite_thm]
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(LEMMA_T⌜¬p ∈ {p'|p' ∈ Prime ∧ p' Divides p * n} \ {p}⌝ asm_tac
	THEN1 REPEAT strip_tac);
a(LEMMA_T⌜{p'|p' ∈ Prime ∧ p' Divides p * n} =
	{p} ∪ ({p'|p' ∈ Prime ∧ p' Divides p * n} \ {p})⌝
	once_rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" prove_tac[]
		THEN1 rewrite_tac[divides_times_thm]));
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(LEMMA_T⌜{p'|p' ∈ Prime ∧ p' Divides n} =
	{p'|p' ∈ Prime ∧ p' Divides p * n} \ {p}⌝
	(fn th1 => DROP_NTH_ASM_T 4 (fn th2 =>
			conv_tac(LEFT_C(once_rewrite_conv[th2])))
		THEN rewrite_tac[th1]));
a(PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2,1" *** *)
a(bc_thm_tac divides_trans_thm THEN ∃_tac⌜n⌝
	THEN REPEAT strip_tac THEN rewrite_tac[divides_times_thm]);
(* *** Goal "2.2.2.2.2" *** *)
a(contr_tac THEN all_var_elim_asm_tac1);
(* *** Goal "2.2.2.3" *** *)
a(GET_NTH_ASM_T 3 (fn th => fc_tac[rewrite_rule[prime_thm]th]));
a(all_fc_tac[prime_divides_prime_thm] THEN all_var_elim_asm_tac1);
val ⦏square_free_factorisation_thm⦎ = save_pop_thm "square_free_factorisation_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀P⦁
	P ⊆ Prime
∧	P ∈ Finite
⇒	{m | m ∈ SquareFree ∧ ∀p⦁p ∈ Prime ∧ p Divides m ⇒ p ∈ P} ∈ Finite
∧	#{m | m ∈ SquareFree ∧ ∀p⦁p ∈ Prime ∧ p Divides m ⇒ p ∈ P} = 2 ^ #P⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN all_fc_tac[ℙ_finite_size_thm]);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac bijection_finite_size_thm);
a(∃_tac⌜λA⦁ Π A (λk:ℕ⦁k)⌝ THEN asm_rewrite_tac[ℙ_thm]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac prime_divisors_unique_thm);
a(∃_tac⌜λk⦁0⌝ THEN asm_rewrite_tac[ℕ_exp_clauses]);
a(REPEAT strip_tac
	THEN_TRY (bc_thm_tac ⊆_finite_thm
		THEN ∃_tac ⌜P⌝ THEN REPEAT strip_tac)
	THEN PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(∃_tac⌜{p|p ∈ Prime ∧ p Divides x}⌝
	THEN all_fc_tac[square_free_factorisation_thm]);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜x' ⊆ Prime⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(all_var_elim_asm_tac1 THEN all_fc_tac[factorisation_square_free_thm]);
(* *** Goal "2.3" *** *)
a(all_fc_tac[⊆_finite_thm] THEN all_var_elim_asm_tac1);
a(all_fc_tac[prime_Π_thm]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[]));
a(lemma_tac⌜x ∈ Prime⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(ALL_FC_T asm_rewrite_tac[prime_divides_prime_thm]);
a(PC_T1 "sets_ext1" asm_prove_tac[]);
val ⦏square_free_finite_size_thm⦎ = save_pop_thm "square_free_finite_size_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜1 ∈ SquareFree⌝);
a(rewrite_tac[square_free_def, divides_1_thm,
	times_eq_1_thm, ℕ_exp_clauses]);
val ⦏square_free_1_thm⦎ = save_pop_thm "square_free_1_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁	∃n d⦁
	n^2 ≤ m
∧	d ∈ SquareFree
∧	m = d * n^2
⌝);
a(REPEAT strip_tac);
a(cases_tac⌜m = 0⌝
	THEN1 (all_var_elim_asm_tac1 THEN ∃_tac⌜0⌝ THEN ∃_tac⌜1⌝
		THEN rewrite_tac[square_free_1_thm, ℕ_exp_clauses]));
a(∃_tac⌜Max {n | n^2 Divides m}⌝);
a(lemma_tac⌜0 < m ∧ 1 ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(lemma_tac⌜∀ i⦁ i ∈ {n|n ^ 2 Divides m} ⇒ i ≤ m+1⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[ℕ_exp_clauses]);
a(contr_tac THEN all_fc_tac[divides_≤_thm]);
a(LEMMA_T⌜m+1 ≤ i⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 ante_tac THEN all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜Max {n | n^2 Divides m} ∈ {n | n^2 Divides m}⌝
	THEN1 bc_thm_tac max_∈_thm);
(* *** Goal "2.1" *** *)
a(∃_tac⌜1⌝ THEN ∃_tac⌜m+1⌝ THEN pure_asm_rewrite_tac[]
	THEN rewrite_tac[ℕ_exp_clauses,
		∀_elim⌜1⌝ divides_mod_thm, div_mod_1_thm]);
(* *** Goal "2.2" *** *)
a(TOP_ASM_T (strip_asm_tac o once_rewrite_rule[divides_def]));
a(all_fc_tac[divides_≤_thm]);
a(∃_tac⌜k⌝ THEN REPEAT strip_tac);
a(rewrite_tac[square_free_def] THEN contr_tac);
a(cases_tac⌜k = 0⌝
	THEN1 (all_var_elim_asm_tac1
		THEN DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[])
		THEN all_var_elim_asm_tac1));
a(swap_nth_asm_concl_tac 3);
a(cases_tac⌜n=0⌝ THEN1 asm_rewrite_tac[ℕ_exp_clauses, divides_0_thm]);
a(contr_tac THEN LEMMA_T
	⌜∀a b⦁ a^2 Divides k ∧ m = k*b^2  ⇒ (a*b)^2 Divides m⌝
	(fn th => all_fc_tac[th]));
(* *** Goal "2.2.1" *** *)
a(DROP_ASMS_T discard_tac
	THEN rewrite_tac[divides_def, ℕ_exp_clauses]
	THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(∃_tac⌜k'⌝ THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜n * Max {n|n ^ 2 Divides m} ≤ Max {n|n ^ 2 Divides m}⌝);
(* *** Goal "2.2.2.1" *** *)
a(bc_thm_tac ≤_max_thm);
a(∃_tac⌜m+1⌝ THEN GET_NTH_ASM_T 10 pure_rewrite_thm_tac
	THEN asm_rewrite_tac[]);
a(lemma_tac⌜2 ≤ n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T[5, 7] discard_tac
	THEN POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def])
	THEN all_var_elim_asm_tac1);
a(all_fc_tac[pc_rule1"lin_arith"prove_rule[]
	⌜∀a⦁(2+i)*a ≤ a ⇒ a = 0⌝]);
a(swap_nth_asm_concl_tac 9 THEN POP_ASM_T rewrite_thm_tac);
a(rewrite_tac[ℕ_exp_clauses, divides_0_thm]);
a(REPEAT strip_tac);
val ⦏square_free_divisor_thm⦎ = save_pop_thm "square_free_divisor_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁	0 < m
⇒	∃n d⦁
	0 < n ∧ 0 < d ∧ n^2 ≤ m
∧	d ∈ SquareFree
∧	m = d * n^2
⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜m⌝ square_free_divisor_thm));
a(∃_tac⌜n⌝ THEN ∃_tac⌜d⌝ THEN asm_rewrite_tac[]);
a(POP_ASM_T ante_tac);
a(cases_tac⌜d = 0⌝ THEN1
	(asm_rewrite_tac[] THEN contr_tac
		THEN all_var_elim_asm_tac1));
a(cases_tac⌜n = 0⌝ THEN1
	(asm_rewrite_tac[ℕ_exp_clauses] THEN contr_tac
		THEN all_var_elim_asm_tac1));
a(STRIP_T discard_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏square_free_divisor_thm1⦎ = save_pop_thm "square_free_divisor_thm1";
=TEX
%%%%
%%%%

=SML
val ⦏one_≤_lemma⦎ = pc_rule1 "lin_arith" prove_rule[] ⌜∀m⦁1 ≤ m ⇔ 0 < m⌝;
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀P n⦁
	0 < n
∧	P ⊆ Prime
∧	P ∈ Finite
⇒	{m | 1 ≤ m ∧ m ≤ n^2 ∧ ∀p⦁p ∈ Prime ∧ p Divides m ⇒ p ∈ P} ∈ Finite
∧	#{m | 1 ≤ m ∧ m ≤ n^2 ∧ ∀p⦁p ∈ Prime ∧ p Divides m ⇒ p ∈ P} ≤ n * 2 ^ #P⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN rewrite_tac[one_≤_lemma]);
a(lemma_tac⌜
	({i | i < n} ×
	{m|m ∈ SquareFree ∧ (∀ p⦁ p ∈ Prime ∧ p Divides m ⇒ p ∈ P)}) ∈ Finite
∧	#({i | i < n} ×
	{m|m ∈ SquareFree ∧ (∀ p⦁ p ∈ Prime ∧ p Divides m ⇒ p ∈ P)})	= n * 2 ^ #P⌝);
(* *** Goal "1" *** *)
a(strip_asm_tac (∀_elim⌜n⌝ range_finite_size_thm));
a(POP_ASM_T (fn th => conv_tac(RIGHT_C(RIGHT_C(once_rewrite_conv[eq_sym_rule th])))));
a(all_fc_tac[square_free_finite_size_thm]);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac ×_finite_size_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(TOP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac surjection_finite_size_thm);
a(∃_tac⌜λ(k, d)⦁if d*(k+1)^2 ≤ n^2 then d*(k+1)^2 else 1⌝
	THEN asm_rewrite_tac[]);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(strip_asm_tac(∀_elim⌜x⌝square_free_divisor_thm1)
	THEN all_var_elim_asm_tac1);
a(LEMMA_T⌜1 ≤ n'⌝ (strip_asm_tac o 
	once_rewrite_rule[plus_comm_thm] o
	rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(rename_tac[(⌜i⌝, "k")]
	THEN DROP_NTH_ASM_T 4 discard_tac
	THEN all_var_elim_asm_tac1);
a(∃_tac⌜(k, d)⌝ THEN asm_rewrite_tac[×_def]);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LEMMA_T⌜k + 1 ≤ n⌝ (fn th => ante_tac th THEN PC_T1 "lin_arith" prove_tac[]));
a(once_rewrite_tac[square_≤_mono_thm]);
a(LIST_DROP_NTH_ASM_T [2, 4] (MAP_EVERY ante_tac)
	THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN rewrite_tac[divides_def]
	THEN REPEAT strip_tac THEN rename_tac[]
	THEN asm_rewrite_tac[]);
a(∃_tac⌜k'*(k+1)^2⌝ THEN PC_T1 "lin_arith" prove_tac[]);
val ⦏recip_primes_div_estimate_thm1⦎ = save_pop_thm "recip_primes_div_estimate_thm1";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀n d⦁
	0 < n ∧ 0 < d
⇒	{m | 1 ≤ m ∧ m ≤ n ∧ d Divides m} ∈ Finite
∧	#{m | 1 ≤ m ∧ m ≤ n ∧ d Divides m} = n Div d⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN rewrite_tac[one_≤_lemma]);
a(strip_asm_tac(∀_elim⌜n Div d⌝range_finite_size_thm));
a(POP_ASM_T (once_rewrite_thm_tac o eq_sym_rule));
a(bc_thm_tac bijection_finite_size_thm);
a(∃_tac⌜λk⦁(k+1)*d⌝ THEN asm_rewrite_tac[divides_def]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T (strip_asm_tac o once_rewrite_rule[times_comm_thm]));
a(all_fc_tac[times_cancel_thm]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(strip_asm_tac(∀_elim⌜k⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN1 (all_asm_ante_tac THEN rewrite_tac[]));
a(∃_tac⌜i⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n = n Div d * d + n Mod d⌝
	THEN1 (bc_thm_tac div_mod_thm
		THEN REPEAT strip_tac));
a(lemma_tac⌜n Mod d < d⌝
	THEN1 (bc_thm_tac mod_less_thm
		THEN REPEAT strip_tac));
a(lemma_tac ⌜d*(i + 1) < d*(n Div d + 1)⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(swap_nth_asm_concl_tac 1 THEN POP_ASM_T ante_tac);
a(rewrite_tac[¬_less_thm]);
a(STRIP_T (strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(all_var_elim_asm_tac1);
a(LEMMA_T⌜x' + 1 ≤ n Div d⌝ (strip_asm_tac o
	rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜n = n Div d * d + n Mod d⌝ ante_tac
	THEN1 (bc_thm_tac div_mod_thm
		THEN REPEAT strip_tac));
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(STRIP_T once_rewrite_thm_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "5" *** *)
a(∃_tac⌜x' + 1⌝ THEN REPEAT strip_tac);
val ⦏divisors_finite_size_thm⦎ = save_pop_thm "divisors_finite_size_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀Q n⦁
	Q ∈ Finite
∧	(∀q⦁q ∈ Q ⇒ 0 < q)
∧	0 < n
⇒	{m | 1 ≤ m ∧ m ≤ n ∧ ∃q⦁q ∈ Q ∧ q Divides m} ∈ Finite
∧	#{m | 1 ≤ m ∧ m ≤ n ∧ ∃q⦁q ∈ Q ∧ q Divides m} ≤ Σ Q (λq⦁n Div q)⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN rewrite_tac[one_≤_lemma]);
a(DROP_NTH_ASM_T 2 ante_tac THEN finite_induction_tac⌜Q⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]⌜{x|F}={}⌝,
	empty_finite_thm, size_empty_thm, ind_sum_ℕ_def]);
(* *** Goal "2" *** *)
a(STRIP_T(strip_asm_tac o ∀_elim⌜q⌝));
(* *** Goal "3" *** *)
a(strip_tac);
a(ALL_FC_T rewrite_tac[ind_sum_ℕ_def]);
a(LEMMA_T ⌜
	{m|0 < m ∧ m ≤ n ∧ (∃ q⦁ q ∈ {x} ∪ Q ∧ q Divides m)} =
	{m| 1 ≤ m ∧ m ≤ n ∧ x Divides m} ∪
	{m| 0 < m ∧ m ≤ n ∧ (∃ q⦁ q ∈ Q ∧ q Divides m)}⌝
	rewrite_thm_tac
	THEN1 (rewrite_tac[one_≤_lemma]
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(bc_thm_tac (pc_rule1 "lin_arith" prove_rule[]
	⌜∀p; m n k:ℕ⦁(p ∧ m ≤ n) ∧ n ≤ k ⇒ p ∧ m ≤ k⌝)
	THEN ∃_tac⌜
	#{m| 1 ≤ m ∧ m ≤ n ∧ x Divides m} +
	#{m| 0 < m ∧ m ≤ n ∧ (∃ q⦁ q ∈ Q ∧ q Divides m)}⌝
	THEN strip_tac);
(* *** Goal "3.1" *** *)
a(bc_thm_tac ∪_finite_size_≤_thm THEN REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜x⌝);
a(all_fc_tac[divisors_finite_size_thm]);
(* *** Goal "3.2" *** *)
a(bc_thm_tac (pc_rule1 "lin_arith" prove_rule[]
	⌜∀a b c d:ℕ⦁a = c ∧ b ≤ d ⇒ a + b ≤ c + d⌝)
	THEN REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜x⌝);
a(all_fc_tac[divisors_finite_size_thm]);
val ⦏recip_primes_div_estimate_thm2⦎ = save_pop_thm "recip_primes_div_estimate_thm2";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀n P Q⦁
	0 < n
∧	P ⊆ Prime
∧	P ∈ Finite
∧	Q = {q | q ≤ n^2 ∧ q ∈ Prime ∧ ¬q ∈ P}
⇒	Q ∈ Finite
∧	n^2 ≤ n * 2 ^ #P + Σ Q (λ q⦁ n^2 Div q)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac ⌜Q ∈ Finite⌝ THEN1 bc_thm_tac ⊆_finite_thm);
(* *** Goal "1" *** *)
a(∃_tac⌜{m | 1 ≤ m ∧ m ≤ n^2}⌝
	THEN asm_rewrite_tac[range_finite_size_thm1]);
a(LEMMA_T⌜∀q⦁q ∈ Prime ⇔ q ∈ Prime ∧ 1 ≤ q⌝ once_rewrite_thm_tac
	THEN1 (rewrite_tac[one_≤_lemma]
		THEN REPEAT strip_tac THEN all_fc_tac[prime_0_less_thm]));
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(bc_thm_tac ≤_trans_thm THEN1 ∃_tac⌜#{m | 1 ≤ m ∧ m ≤ n^2}⌝
	THEN REPEAT strip_tac
	THEN1 rewrite_tac[range_finite_size_thm1]);
a(bc_thm_tac(prove_rule[]⌜∀A m⦁A ∈ Finite ∧ #A ≤ m ⇒ #A ≤ m⌝));
a(LEMMA_T ⌜{m|1 ≤ m ∧ m ≤ n ^ 2} =
	{m|1 ≤ m ∧ m ≤ n ^ 2 ∧ (∀ p⦁ p ∈ Prime ∧ p Divides m ⇒ p ∈ P)} ∪
	{m|1 ≤ m ∧ m ≤ n ^ 2 ∧ (∃ q⦁ q ∈ Q ∧ q Divides m)}⌝
	rewrite_thm_tac
	THEN1 (asm_rewrite_tac[] THEN PC_T1 "sets_ext1" prove_tac[]));
(* *** Goal "2.1" *** *)
a(∃_tac⌜p⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜0 < x⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_fc_tac[divides_≤_thm]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∀ q⦁ q ∈ Q ⇒ 0 < q⌝
	THEN1 (all_var_elim_asm_tac1
		THEN REPEAT strip_tac
		THEN all_fc_tac[prime_0_less_thm]));
a(lemma_tac⌜0 < n^2⌝
	THEN1 (rewrite_tac[ℕ_exp_eq_0_thm, 
		pc_rule1"lin_arith" prove_rule[]
		⌜∀m⦁0 < m ⇔ ¬m = 0⌝]
		THEN contr_tac THEN all_var_elim_asm_tac1));
a(POP_ASM_T (fn th =>
	all_fc_tac[recip_primes_div_estimate_thm1]
	THEN asm_tac th));
a(DROP_NTH_ASM_T 9 (fn th =>
	all_fc_tac[recip_primes_div_estimate_thm2]
	THEN asm_tac th));
a(bc_thm_tac (pc_rule1 "lin_arith" prove_rule[]
	⌜∀p; m n k:ℕ⦁(p ∧ m ≤ n) ∧ n ≤ k ⇒ p ∧ m ≤ k⌝)
	THEN ∃_tac⌜
	#{m|1 ≤ m ∧ m ≤ n ^ 2 ∧ (∀ p⦁ p ∈ Prime ∧ p Divides m ⇒ p ∈ P)}+
	#{m|1 ≤ m ∧ m ≤ n ^ 2 ∧ (∃ q⦁ q ∈ Q ∧ q Divides m)}⌝
	THEN strip_tac);
(* *** Goal "2.2.1" *** *)
a(bc_thm_tac ∪_finite_size_≤_thm THEN REPEAT strip_tac);
(* *** Goal "2..2" *** *)
a(bc_thm_tac (pc_rule1 "lin_arith" prove_rule[]
	⌜∀a b c d:ℕ⦁a ≤ c ∧ b ≤ d ⇒ a + b ≤ c + d⌝)
	THEN REPEAT strip_tac);
val ⦏recip_primes_div_estimate_thm3⦎ = save_pop_thm "recip_primes_div_estimate_thm3";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀P Q⦁
	P ⊆ Prime
∧	P ∈ Finite
∧	Q = {q | q ≤ (2 ^ (2 * #P + 2)) ∧ q ∈ Prime ∧ ¬q ∈ P}
⇒	Q ∈ Finite
∧	(2 ^ (2 * #P + 1)) ≤ Σ Q (λ q⦁ (2 ^ ( 2 * #P + 2)) Div q)
⌝);
a(REPEAT ∀_tac);
a(LEMMA_T ⌜2 ^ (2 * #P + 2) = (2 ^ (# P + 1)) ^ 2⌝
	rewrite_thm_tac
	THEN1 (rewrite_tac[ℕ_exp_ℕ_exp_thm]
		THEN conv_tac(MAP_C anf_conv)
		THEN REPEAT strip_tac));
a(⇒_tac THEN lemma_tac⌜0 < 2 ^ (#P + 1)⌝
	THEN1 (rewrite_tac[ℕ_exp_eq_0_thm, 
		pc_rule1"lin_arith" prove_rule[]
		⌜∀m⦁0 < m ⇔ ¬m = 0⌝]));
a(all_fc_tac[recip_primes_div_estimate_thm3]);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(LEMMA_T ⌜
	(2 ^ (# P + 1)) ^ 2 = 
	2 ^ (# P + 1) * 2 ^ # P + 2 ^ (2 * # P + 1)⌝
	rewrite_thm_tac);
a(rewrite_tac[ℕ_exp_ℕ_exp_thm, ℕ_exp_times_thm]);
a(conv_tac(MAP_C anf_conv));
a(LEMMA_T ⌜∀m⦁ 2 * 2 ^ m  = 2 ^(m+1)⌝ rewrite_thm_tac
	THEN1 (rewrite_tac[ℕ_exp_def] THEN PC_T1 "lin_arith" prove_tac[]));
a(conv_tac(MAP_C anf_conv) THEN strip_tac);
val ⦏recip_primes_div_estimate_thm4⦎ = save_pop_thm "recip_primes_div_estimate_thm4";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀A :'a SET; f : 'a → ℕ⦁
	A ∈ Finite
⇒	ℕℝ (Σ A f) = Σ A  (λx⦁ℕℝ (f x))
⌝);
a(REPEAT strip_tac);
a(finite_induction_tac ⌜A⌝ THEN1 rewrite_tac[ind_sum_def, ind_sum_ℕ_def]);
a(ALL_FC_T rewrite_tac[ind_sum_def, ind_sum_ℕ_def]);
a(asm_rewrite_tac[ℕℝ_plus_homomorphism_thm]);
val ⦏ℕℝ_ind_sum_thm⦎ = save_pop_thm "ℕℝ_ind_sum_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀A :'a SET; f g : 'a → ℝ⦁
	A ∈ Finite
∧	(∀x⦁x ∈ A ⇒ f x ≤ g x)
⇒	Σ A f ≤ Σ A g
⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(finite_induction_tac ⌜A⌝ THEN1 rewrite_tac[ind_sum_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[ind_sum_def]);
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜x⌝));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏ind_sum_≤_mono_thm⦎ = save_pop_thm "ind_sum_≤_mono_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m n⦁
	0 < n
⇒	ℕℝ (m Div n) ≤ ℕℝ m * ℕℝ n ⋏-⋏1
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < ℕℝ n⌝ THEN1 asm_rewrite_tac[ℕℝ_less_thm]);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀a b:ℝ⦁a ≤ b ⇔ ¬ b < a⌝] THEN contr_tac);
a(LEMMA_T⌜ℕℝ n * ℕℝ m * ℕℝ n ⋏-⋏1 < ℕℝ n * ℕℝ (m Div n)⌝ ante_tac
	THEN1 all_fc_tac[ℝ_times_mono_thm]);
a(lemma_tac⌜¬ℕℝ n = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rewrite_tac[∀_elim⌜ℕℝ m⌝ ℝ_times_order_thm,
	ℕℝ_times_homomorphism_thm1]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(rewrite_tac[ℕℝ_less_thm]);
a(LEMMA_T⌜m = m Div n * n + m Mod n⌝ ante_tac
	THEN1 (bc_thm_tac div_mod_thm
		THEN REPEAT strip_tac));
a(PC_T1 "lin_arith" prove_tac[]);
val ⦏ℕℝ_div_≤_thm⦎ = save_pop_thm "ℕℝ_div_≤_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀P Q⦁
	P ⊆ Prime
∧	P ∈ Finite
∧	Q = {q | q ≤ (2 ^ (2 * #P + 2)) ∧ q ∈ Prime ∧ ¬q ∈ P}
⇒	Q ∈ Finite
∧	1/2 ≤ Σ Q (λ q⦁ ℕℝ q ⋏-⋏1)
⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN all_fc_tac[recip_primes_div_estimate_thm4]
	THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀a b:ℝ⦁a ≤ b ⇔ ¬ b < a⌝] THEN contr_tac);
a(lemma_tac⌜ℕℝ 0 < ℕℝ (2^(2 * # P + 2))⌝
	THEN1 rewrite_tac[ℕℝ_less_thm,
		pc_rule1"lin_arith" prove_rule[]
		⌜∀m⦁0 < m ⇔ ¬m = 0⌝,
		ℕ_exp_eq_0_thm]);
a(LEMMA_T ⌜ℕℝ (2 ^ (2 * # P + 2)) * Σ Q (λ q⦁ ℕℝ q ⋏-⋏1) < ℕℝ (2 ^ (2 * # P + 2)) * 1 / 2⌝
	ante_tac THEN1 all_fc_tac[ℝ_times_mono_thm]);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀a b:ℝ⦁a < b ⇔ ¬ b ≤ a⌝]);
a(bc_thm_tac ℝ_≤_trans_thm
	THEN1 ∃_tac⌜Σ Q (λk⦁ℕℝ((λ q⦁ 2 ^ (2 * # P + 2) Div q)k))⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ALL_FC_T pure_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) ℕℝ_ind_sum_thm]);
a(conv_tac(LEFT_C (rewrite_conv[pc_rule1"lin_arith"prove_rule[]⌜∀m⦁2*m+2 = (2*m+1)+1⌝])));
a(once_rewrite_tac[ℕ_exp_def]);
a(rewrite_tac[ℕℝ_times_homomorphism_thm,
	∀_elim⌜ℕℝ (2 ^ (2 * # P + 1))⌝ ℝ_times_order_thm]);
a(asm_rewrite_tac[ℕℝ_≤_thm]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) ind_sum_const_times_thm]);
a(bc_thm_tac ind_sum_≤_mono_thm THEN REPEAT strip_tac);
a(rewrite_tac[]);
a(bc_tac [ℕℝ_div_≤_thm, prime_0_less_thm]);
a(all_var_elim_asm_tac1);
val ⦏recip_primes_div_estimate_thm5⦎ = save_pop_thm "recip_primes_div_estimate_thm5";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜
	(∀n⦁{p | p ∈ Prime ∧ p ≤ n} ∈ Finite)
∧	(∀m⦁∃n⦁
	ℕℝ m ≤ Σ {p | p ∈ Prime ∧ p ≤ n} (λp⦁ ℕℝ p ⋏-⋏1))
⌝);
a(once_rewrite_tac[taut_rule⌜∀p q⦁p ∧ q ⇔ p ∧ (p ⇒ q)⌝]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜{m | m < n + 1}⌝
	THEN (rewrite_tac[range_finite_size_thm,
		pc_rule1"lin_arith" prove_rule[]
		⌜∀m⦁m ≤ n ⇔ m < n + 1⌝]
		THEN PC_T1 "sets_ext1" prove_tac[]));
(* *** Goal "2" *** *)
a(lemma_tac⌜∀m⦁∃n⦁
	1/2 * ℕℝ m ≤ Σ {p | p ∈ Prime ∧ p ≤ n} (λp⦁ ℕℝ p ⋏-⋏1)⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝);
(* *** Goal "2.1.1" *** *)
a(∃_tac⌜0⌝ THEN rewrite_tac[]);
a(LEMMA_T⌜∀p⦁¬(p ∈ Prime ∧ p = 0)⌝ rewrite_thm_tac
	THEN1 (contr_tac THEN all_fc_tac[prime_0_less_thm]
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(rewrite_tac[ind_sum_def, pc_rule1 "sets_ext" prove_rule[]⌜{x|F} = {}⌝]);
(* *** Goal "2.1.2" *** *)
a(DROP_NTH_ASM_T 2 (strip_asm_tac o ∀_elim⌜n⌝));
a(lemma_tac⌜{p|p ∈ Prime ∧ p ≤ n} ⊆ Prime⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(lemma_tac⌜∃Q⦁ Q = {q|q ≤ 2 ^ (2 * # {p|p ∈ Prime ∧ p ≤ n} + 2) ∧ q ∈ Prime ∧ ¬ q ∈ {p|p ∈ Prime ∧ p ≤ n}}⌝
	THEN1 prove_∃_tac);
a(all_fc_tac[recip_primes_div_estimate_thm5]);
a(all_asm_ante_tac THEN rewrite_tac[taut_rule
	⌜∀q⦁q ∈ Prime ∧ ¬(q ∈ Prime ∧ q ≤ n) ⇔
		q ∈ Prime ∧ ¬q ≤ n⌝]
	THEN REPEAT strip_tac);
a(∃_tac⌜2 ^ (2 * # {p|p ∈ Prime ∧ p ≤ n} + 2)⌝);
a(LEMMA_T⌜{p|p ∈ Prime ∧ p ≤ 2 ^ (2 * # {p|p ∈ Prime ∧ p ≤ n} + 2)} = 
	{p|p ∈ Prime ∧ p ≤ n} ∪ Q⌝
	rewrite_thm_tac
	THEN1 (asm_rewrite_tac[] THEN
		PC_T1 "sets_ext1" asm_prove_tac[]));
(* *** Goal "2.1.2.1" *** *)
a(cases_tac⌜Q = {}⌝);
(* *** Goal "2.1.2.1.1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 4
	THEN asm_rewrite_tac[ind_sum_def]);
(* *** Goal "2.1.2.1.2" *** *)
a(POP_ASM_T (PC_T1 "sets_ext" strip_asm_tac));
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.2.2" *** *)
a(rewrite_tac[ℕℝ_plus_homomorphism_thm,
	ℝ_times_plus_distrib_thm]);
a(ALL_FC_T rewrite_tac[ind_sum_∪_thm]);
a(LEMMA_T⌜{p|p ∈ Prime ∧ p ≤ n} ∩ Q = {}⌝
	(fn th => rewrite_tac[th, ind_sum_def])
	THEN1 (asm_rewrite_tac[] THEN
		PC_T1 "sets_ext1" prove_tac[]));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(POP_ASM_T (ante_tac o ∀_elim⌜2 * m⌝));
a(rewrite_tac[ℕℝ_times_homomorphism_thm,
	ℝ_times_assoc_thm1]);
val ⦏recip_primes_div_thm⦎ = save_pop_thm "recip_primes_div_thm";
=TEX
%%%%
%%%%
%%%% COPRIMALITY
%%%%
%%%%

=SML
set_goal([], ⌜ ∀m n⦁
		m Coprime n
	⇔	∀p⦁ p ∈ Prime ∧ p Divides m ⇒ ¬p Divides n ⌝);
a(rewrite_tac[coprime_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(swap_nth_asm_concl_tac 3 THEN REPEAT strip_tac THEN
	∃_tac⌜p⌝ THEN swap_nth_asm_concl_tac 3
	THEN asm_rewrite_tac[prime_def]);
(* *** Goal "2" *** *)
a(cases_tac⌜i = 0⌝ THEN1
	(all_var_elim_asm_tac1
		THEN all_asm_ante_tac
		THEN rewrite_tac[divides_0_thm]
		THEN contr_tac
		THEN all_var_elim_asm_tac1
		THEN swap_nth_asm_concl_tac 1
		THEN REPEAT strip_tac
		THEN ∃_tac⌜2⌝
		THEN rewrite_tac[divides_0_thm, prime_2_thm]));
a(swap_nth_asm_concl_tac 4 THEN REPEAT strip_tac);
a(lemma_tac⌜1 < i⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_fc_tac[prime_divisor_thm]);
a(∃_tac⌜p⌝ THEN ALL_FC_T asm_rewrite_tac[divides_trans_thm]);
val ⦏coprime_prime_thm⦎ = save_pop_thm "coprime_prime_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜ ∀m n⦁
		m Coprime n
	⇔	(0 < m ∨ 0 < n) ∧ Gcd m n = 1  ⌝);
a(REPEAT ∀_tac THEN rewrite_tac[coprime_def]);
a(CASES_T⌜¬(0 < m ∨ 0 < n)⌝ asm_tac THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(lemma_tac⌜m = 0 ∧ n = 0⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN all_var_elim_asm_tac1);
a(asm_rewrite_tac[divides_0_thm] THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(ante_tac(all_∀_elim gcd_def) THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
a(DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[divides_1_thm]);
val ⦏coprime_gcd_thm⦎ = save_pop_thm "coprime_gcd_thm";
=TEX
%%%%
%%%% REAL INTEGRAL DOMAINS
%%%%
=SML
set_goal([], ⌜Universe ∈ RealID⌝);
a(rewrite_tac[real_i_d_def]);
val ⦏ℝ_real_i_d_thm⦎ = save_pop_thm "ℝ_real_i_d_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀V⦁ V ⊆ RealID ⇒ ⋂V ∈ RealID⌝);
a(PC_T1 "sets_ext1" rewrite_tac[real_i_d_def]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]);
val ⦏⋂_real_i_d_thm⦎ = save_pop_thm "⋂_real_i_d_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜ℤ ∈ RealID⌝);
a(rewrite_tac[ℤ_def]);
a(bc_thm_tac ⋂_real_i_d_thm THEN rewrite_tac[]);
val ⦏ℤ_real_i_d_thm⦎ = save_pop_thm "ℤ_real_i_d_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜ℤ = {x | ∃i⦁x = ℤℝ i}⌝);
a(PC_T1 "sets_ext1" rewrite_tac[ℤ_def, real_i_d_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(swap_nth_asm_concl_tac 1 THEN REPEAT strip_tac);
a(∃_tac ⌜{x | ∃i⦁x = ℤℝ i}⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1);
(* *** Goal "1.1" *** *)
a(∃_tac⌜ℕℤ 1⌝ THEN rewrite_tac[ℤℝ_ℕℤ_thm]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜i + i'⌝ THEN rewrite_tac[ℤℝ_plus_homomorphism_thm]);
(* *** Goal "1.3" *** *)
a(∃_tac⌜~i⌝ THEN rewrite_tac[ℤℝ_minus_thm]);
(* *** Goal "1.4" *** *)
a(∃_tac⌜i * i'⌝ THEN rewrite_tac[ℤℝ_times_homomorphism_thm]);
(* *** Goal "1.5" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(ℤ_induction_tac⌜i⌝);
(* *** Goal "2.1" *** *)
a(asm_rewrite_tac[ℤℝ_ℕℤ_thm]);
(* *** Goal "2.2" *** *)
a(rewrite_tac[ℤℝ_minus_thm] THEN all_asm_fc_tac[]);
(* *** Goal "2.3" *** *)
a(rewrite_tac[ℤℝ_plus_homomorphism_thm] THEN all_asm_fc_tac[]);
val ⦏ℤ_thm⦎ = save_pop_thm "ℤ_thm";
=TEX
%%%%
%%%% FIELDS
%%%%
=SML
set_goal([], ⌜Universe ∈ RealField⌝);
a(rewrite_tac[real_field_def, ℝ_real_i_d_thm]);
val ⦏ℝ_real_field_thm⦎ = save_pop_thm "ℝ_real_field_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀V⦁ V ⊆ RealField ⇒ ⋂V ∈ RealField⌝);
a(PC_T1 "sets_ext1" rewrite_tac[real_field_def,
	real_i_d_def]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]);
val ⦏⋂_real_field_thm⦎ = save_pop_thm "⋂_real_field_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜ℚ ∈ RealField⌝);
a(rewrite_tac[rat_def]);
a(bc_thm_tac ⋂_real_field_thm THEN rewrite_tac[]);
val ⦏rat_real_i_d_thm⦎ = save_pop_thm "rat_real_i_d_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜ℤ ⊆ ℚ⌝);
a(PC_T1"sets_ext1" rewrite_tac[rat_def, ℤ_def, real_field_def]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
val ⦏ℤ_⊆_rat_thm⦎ = save_pop_thm "ℤ_⊆_rat_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀A⦁ FieldOfFractions A ∈ RealField⌝);
a(REPEAT strip_tac THEN rewrite_tac[field_of_fractions_def]);
a(bc_thm_tac ⋂_real_field_thm);
a(PC_T1 "sets_ext1" prove_tac[]);
val ⦏field_of_fractions_field_thm⦎ = save_pop_thm "field_of_fractions_field_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜ℚ = FieldOfFractions ℤ⌝);
a(rewrite_tac[field_of_fractions_def, rat_def]);
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac
	THEN1 all_asm_fc_tac[]);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac
	THEN PC_T1"sets_ext1" rewrite_tac[ℤ_def, real_field_def]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
val ⦏rat_field_of_fractions_thm⦎ = save_pop_thm "rat_field_of_fractions_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀A⦁
	A ∈ RealID
⇒	FieldOfFractions A =
	{x | ∃a b⦁a ∈ A ∧ b ∈ A ∧ ¬b = ℕℝ 0 ∧ x = a * b ⋏-⋏1}⌝);
a(PC_T1 "sets_ext1" rewrite_tac[real_i_d_def, field_of_fractions_def,
	real_field_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜x ∈ {y | ∃ a b⦁ a ∈ A ∧ b ∈ A ∧ ¬ b = ℕℝ 0 ∧ y = a * b ⋏-⋏1}⌝
	(fn th => ante_tac th THEN rewrite_tac[]));
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1);
(* *** Goal "1.1" *** *)
a(∃_tac⌜ℕℝ 1⌝ THEN ∃_tac⌜ℕℝ 1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜a * b' + a' * b⌝ THEN ∃_tac⌜b*b'⌝);
a(asm_rewrite_tac[ℝ_times_eq_0_thm]);
a(REPEAT strip_tac
	THEN_TRY LIST_GET_NTH_ASM_T [7, 8, 9] bc_tac
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (fn th =>
	ALL_FC_T1 fc_⇔_canon
	once_rewrite_tac[conv_rule(ONCE_MAP_C (RIGHT_C eq_sym_conv))
	ℝ_times_cancel_thm] THEN asm_tac th));
a(DROP_NTH_ASM_T 2 (fn th =>
	ALL_FC_T1 fc_⇔_canon
	once_rewrite_tac[conv_rule(ONCE_MAP_C (RIGHT_C eq_sym_conv))
	ℝ_times_cancel_thm] THEN asm_tac th));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(rewrite_tac[ℝ_times_plus_distrib_thm, ℝ_times_assoc_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b c d⦁a*b ⋏-⋏1*c*d = (a*c)*(b ⋏-⋏1 *d)⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(conv_tac (RANDS_C ℝ_anf_conv) THEN strip_tac);
(* *** Goal "1.3" *** *)
a(∃_tac⌜~a⌝ THEN ∃_tac⌜b⌝ THEN 
	LIST_DROP_NTH_ASM_T [5] (ALL_FC_T asm_rewrite_tac));
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.4" *** *)
a(∃_tac⌜a*a'⌝ THEN ∃_tac⌜b*b'⌝);
a(asm_rewrite_tac[ℝ_times_eq_0_thm]);
a(LIST_DROP_NTH_ASM_T [7] (ALL_FC_T asm_rewrite_tac));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.5" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_times_eq_0_thm]));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(∃_tac⌜b⌝ THEN ∃_tac⌜a⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "1.6" *** *)
a(∃_tac⌜x⌝ THEN ∃_tac⌜ℕℝ 1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [2, 3] bc_tac
	THEN REPEAT strip_tac
	THEN DROP_NTH_ASM_T 1 bc_thm_tac
	THEN REPEAT strip_tac);
val ⦏field_of_fractions_thm⦎ = save_pop_thm "field_of_fractions_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜ℚ = {x | ∃i:ℤ; m:ℕ⦁x = ℤℝ i * ℕℝ (m+1) ⋏-⋏1}⌝);
a(rewrite_tac[rat_field_of_fractions_thm]);
a(strip_asm_tac ℤ_real_i_d_thm);
a(ALL_FC_T rewrite_tac[field_of_fractions_thm]);
a(rewrite_tac[ℤ_thm]);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(strip_asm_tac(∀_elim⌜i'⌝ℤ_cases_thm1)
	THEN all_var_elim_asm_tac1);
(* *** Goal "1.1" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[ℤℝ_ℕℤ_thm,
	ℕℝ_one_one_thm,
	pc_rule1 "lin_arith" prove_rule[]
	⌜(¬m = 0 ⇔ 1 ≤ m) ∧ ∀i⦁1 + i = i + 1⌝,
	≤_def] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(∃_tac⌜i⌝ THEN ∃_tac⌜i'⌝ THEN rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜~i⌝ THEN ∃_tac⌜m⌝ THEN rewrite_tac[ℤℝ_minus_thm,
	ℤℝ_ℕℤ_thm]);
a(lemma_tac⌜¬ℕℝ (m + 1) = ℕℝ 0⌝
	THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(ALL_FC_T rewrite_tac[ℝ_minus_recip_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜ℤℝ i⌝ THEN ∃_tac⌜ℤℝ(ℕℤ(m+1))⌝ THEN
	rewrite_tac[ℤℝ_ℕℤ_thm, ℕℝ_one_one_thm]);
a(strip_tac THEN1 prove_tac[]);
a(∃_tac⌜ℕℤ(m+1)⌝ THEN rewrite_tac[ℤℝ_ℕℤ_thm]);
val ⦏rat_thm⦎ = save_pop_thm "rat_thm";
=TEX
%%%%
%%%% 

=SML
set_goal([], ⌜
 ℚ = {x | ∃a b : ℕ⦁¬b = 0 ∧ (x = a/b ∨ x = ~(a/b))}
⌝);
a(rewrite_tac[rat_thm] THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(strip_asm_tac(∀_elim⌜i⌝ ℤ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[ℤℝ_ℕℤ_thm]);
(* *** Goal "1.1" *** *)
a(∃_tac⌜m'⌝ THEN ∃_tac⌜m+1⌝ THEN rewrite_tac[ℝ_frac_def]);
a(lemma_tac⌜¬ℕℝ(m+1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜m'⌝ THEN ∃_tac⌜m+1⌝ THEN rewrite_tac[ℝ_frac_def]);
a(lemma_tac⌜¬ℕℝ(m+1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T (strip_asm_tac o once_rewrite_rule[plus_comm_thm] o
		rewrite_rule[≤_def,
		pc_rule1 "lin_arith" prove_rule[]
		⌜¬b = 0 ⇔ 1 ≤ b⌝])
	THEN all_var_elim_asm_tac1);
a(∃_tac⌜ℕℤ a⌝ THEN ∃_tac⌜i⌝);
a(lemma_tac⌜¬ℕℝ(i+1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(rewrite_tac[ℝ_frac_def, ℤℝ_ℕℤ_thm]);
a(ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
(* *** Goal "3" *** *)
a(POP_ASM_T (strip_asm_tac o once_rewrite_rule[plus_comm_thm] o
		rewrite_rule[≤_def,
		pc_rule1 "lin_arith" prove_rule[]
		⌜¬b = 0 ⇔ 1 ≤ b⌝])
	THEN all_var_elim_asm_tac1);
a(∃_tac⌜~(ℕℤ a)⌝ THEN ∃_tac⌜i⌝);
a(lemma_tac⌜¬ℕℝ(i+1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(rewrite_tac[ℝ_frac_def, ℤℝ_ℕℤ_thm]);
a(ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN rewrite_tac[]);
val ⦏rat_thm1⦎ = save_pop_thm "rat_thm1";

=TEX
%%%%
%%%% IRRATIONALITY OF QUADRATIC SURDS

=SML
set_goal([], ⌜
	∀x y⦁ ℕℝ 0 ≤ x ∧ x^2 = y ⇒ x = Sqrt y
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 ≤ y⌝);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(lemma_tac⌜x^2 = Sqrt y^2 ∧ ℕℝ 0 ≤ Sqrt y⌝ THEN1
	(all_fc_tac [sqrt_def] THEN asm_rewrite_tac[]));
a(fc_tac[square_root_unique_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏sqrt_eq_thm⦎ = save_pop_thm "sqrt_eq_thm";
=TEX
%%%%
%%%%

The main result is proved using three lemmas.
The first lemma is the following.
It justifies the steps in the infinite descent.

=SML
set_goal([], ⌜
∀k m n⦁	0 < k ∧ m * m = k * n * n ∧ 1 < n
⇒	∃m1 n1⦁0 < n1 ∧ n1 < n ∧ m1 * m1 = k * n1 * n1
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[prime_divisor_thm1]);
a(all_fc_tac[prime_0_less_thm]);
a(lemma_tac ⌜p Divides m*m⌝ THEN1
	(asm_rewrite_tac[divides_mod_thm,
		pc_rule1"lin_arith" prove_rule[]
		⌜∀x y z⦁x*(p*y)*z = p*x*y*z⌝] THEN
			ALL_FC_T rewrite_tac[mod_clauses]));
a(fc_tac[prime_thm]);
a(LIST_DROP_NTH_ASM_T [2] fc_tac);
(* *** Goal "1" same as "2" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[divides_def]));
a(∃_tac⌜k'⌝ THEN ∃_tac⌜n'⌝ THEN all_var_elim_asm_tac1
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(contr_tac THEN1
	(lemma_tac⌜n' = 0⌝ THEN_TRY all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]));
(* *** Goal "1.2" *** *)
a(LEMMA_T ⌜2 ≤ p⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 all_fc_tac[prime_2_≤_thm]);
a(cases_tac⌜n' = 0⌝ THEN1
	(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.3" *** *)
a(bc_thm_tac times_cancel_thm);
a(∃_tac⌜p⌝ THEN REPEAT strip_tac);
a(bc_thm_tac times_cancel_thm);
a(∃_tac⌜p⌝ THEN REPEAT strip_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏quadratic_surd_lemma1⦎ = pop_thm();
=TEX
The infinite descent bottoms out at 1, from which we we conclude that if $m^2 = kn^2$ has a natural number solution with $n$ positive, then $k$ is a perfect square.

=SML
set_goal([], ⌜
∀k n m⦁	ℕℝ 0 < ℕℝ k ∧ ℕℝ 0 < ℕℝ n ∧ ℕℝ m ^ 2 = ℕℝ k * (ℕℝ n ^ 2)
⇒	∃i⦁ ℕℝ i ^ 2 = ℕℝ k
⌝);
a(rewrite_tac[ℝ_ℕ_exp_square_thm,
	ℕℝ_times_homomorphism_thm1, ℕℝ_one_one_thm, ℕℝ_less_thm]);
a(REPEAT strip_tac);
a(PC_T1 "predicates" lemma_tac
	⌜∃y⦁y ∈ { y | 0 < y ∧ ∃x⦁ x * x = k * y * y }⌝
		THEN1 (∃_tac⌜n⌝ THEN REPEAT strip_tac
			THEN ∃_tac⌜m⌝ THEN REPEAT strip_tac));
a(all_fc_tac[min_∈_thm]);
a(cases_tac⌜1 < Min { y | 0 < y ∧ ∃x⦁ x * x = k * y * y }⌝
	THEN1 all_fc_tac[quadratic_surd_lemma1]);
(* *** Goal "1" *** *)
a(PC_T1 "predicates" lemma_tac
	⌜n1 ∈ { y | 0 < y ∧ ∃x⦁ x * x = k * y * y }⌝
		THEN1 (REPEAT strip_tac THEN ∃_tac⌜m1⌝ THEN REPEAT strip_tac));
a(all_fc_tac[min_≤_thm] THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜Min { y | 0 < y ∧ ∃x⦁ x * x = k * y * y } = 1⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
val ⦏quadratic_surd_lemma2⦎ = pop_thm();
=TEX

We now have the general result that rational square roots of prime numbers are integers, expressed explicitly:
=SML
set_goal([], ⌜∀k a b⦁
	¬b = 0 ∧ (a/b)^2 = ℕℝ k
⇒	∃i⦁ ℕℝ i ^ 2 = ℕℝ k
⌝);
a(REPEAT strip_tac);
a(cases_tac⌜k = 0⌝ THEN1
	(∃_tac⌜0⌝ THEN asm_rewrite_tac[ℝ_ℕ_exp_square_thm]));
a(lemma_tac⌜¬ℕℝ b = ℕℝ 0⌝ THEN1
	asm_rewrite_tac[ℕℝ_one_one_thm]);
a(swap_nth_asm_concl_tac 3);
a(rewrite_tac[ℝ_frac_def] THEN ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(contr_tac THEN LEMMA_T⌜
	(ℕℝ a * ℕℝ b ⋏-⋏1) ^ 2 * ℕℝ b ^ 2 = ℕℝ k * ℕℝ b ^ 2⌝ ante_tac
	THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜∀x y z:ℝ⦁(x*y)^2*z^2 = (x*z*y)^2⌝ rewrite_thm_tac THEN1
	(rewrite_tac[ℝ_ℕ_exp_square_thm]
		THEN PC_T1"ℝ_lin_arith" prove_tac[]));
a(ALL_FC_T rewrite_tac[ℝ_times_recip_thm]);
a(lemma_tac⌜ℕℝ 0 < ℕℝ k ∧ ℕℝ 0 < ℕℝ b⌝ THEN1
	(rewrite_tac[ℕℝ_less_thm] THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(contr_tac THEN all_fc_tac[quadratic_surd_lemma2]);
a(all_asm_fc_tac[]);
val ⦏quadratic_surd_thm1⦎ = save_pop_thm"quadratic_surd_thm1";
=TEX

The next reexpresses the result in terms of the square root function and the set ℚ (which requires us also to deal with the possibility that $a/b$ is negative).

=SML
set_goal([], ⌜
∀i⦁ ℕℝ 0 ≤ i ∧ i ∈ ℤ ∧ Sqrt i ∈ ℚ ⇒ Sqrt i ∈ ℤ
⌝);
a(rewrite_tac[rat_thm1, ℤ_thm] THEN contr_tac
	THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(all_asm_ante_tac);
a(strip_asm_tac(∀_elim⌜i'⌝ ℤ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[ℤℝ_ℕℤ_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(LEMMA_T⌜Sqrt (ℕℝ m)^2 = ℕℝ m⌝ ante_tac THEN1
	ALL_FC_T rewrite_tac[sqrt_thm]);
a(asm_rewrite_tac[] THEN contr_tac THEN
	all_fc_tac[quadratic_surd_thm1]);
a(lemma_tac⌜ℕℝ 0 ≤ ℕℝ i⌝ THEN1
	rewrite_tac[ℕℝ_≤_thm]);
a(all_fc_tac[sqrt_eq_thm]);
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜ℕℤ i⌝));
a(asm_rewrite_tac[ℤℝ_ℕℤ_thm]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜ℕℤ 0⌝ THEN rewrite_tac[ℤℝ_ℕℤ_thm]);
a(swap_nth_asm_concl_tac 3);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀x⦁ℕℝ 0 ≤ ~x ⇔ x ≤ ℕℝ 0⌝,
	ℕℝ_≤_thm]);
a(swap_nth_asm_concl_tac 1 THEN all_var_elim_asm_tac1);
a(rewrite_tac[sqrt_0_1_thm]);
(* *** Goal "2" *** *)
a(all_asm_ante_tac);
a(strip_asm_tac(∀_elim⌜i'⌝ ℤ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[ℤℝ_ℕℤ_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LEMMA_T⌜Sqrt (ℕℝ m)^2 = ℕℝ m⌝ ante_tac THEN1
	ALL_FC_T rewrite_tac[sqrt_thm]);
a(LEMMA_T⌜∀x:ℝ⦁(~x)^2 = x^2⌝ asm_rewrite_thm_tac THEN1
	(rewrite_tac[ℝ_ℕ_exp_square_thm] THEN
		PC_T1 "ℝ_lin_arith" prove_tac[]));
a(contr_tac THEN all_fc_tac[quadratic_surd_thm1]);
a(lemma_tac⌜ℕℝ 0 ≤ ℕℝ i⌝ THEN1
	rewrite_tac[ℕℝ_≤_thm]);
a(all_fc_tac[sqrt_eq_thm]);
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜ℕℤ i⌝));
a(asm_rewrite_tac[ℤℝ_ℕℤ_thm]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜ℕℤ 0⌝ THEN rewrite_tac[ℤℝ_ℕℤ_thm]);
a(swap_nth_asm_concl_tac 3);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀x⦁ℕℝ 0 ≤ ~x ⇔ x ≤ ℕℝ 0⌝,
	ℕℝ_≤_thm]);
a(swap_nth_asm_concl_tac 1 THEN all_var_elim_asm_tac1);
a(rewrite_tac[sqrt_0_1_thm]);
val ⦏quadratic_surd_thm⦎ = save_pop_thm"quadratic_surd_thm";
=TEX

=SML
set_goal([], ⌜
	¬Sqrt (ℕℝ 2) ∈ ℤ
⌝);
a(rewrite_tac[ℤ_thm] THEN contr_tac);
a(all_asm_ante_tac);
a(strip_asm_tac(∀_elim⌜i⌝ ℤ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[ℤℝ_ℕℤ_thm]
	THEN contr_tac);
(* *** Goal "1" *** *)
a(LEMMA_T⌜ℕℝ 0 ≤ ℕℝ 2⌝ asm_tac THEN REPEAT strip_tac);
a(all_fc_tac[sqrt_thm]);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[ℝ_ℕ_exp_square_thm,
	ℕℝ_times_homomorphism_thm1, ℕℝ_one_one_thm]);
a(DROP_ASMS_T discard_tac);
a(cases_tac⌜m = 0⌝ THEN1 asm_rewrite_tac[]);
a(cases_tac⌜m = 1⌝ THEN1 asm_rewrite_tac[]);
a(cases_tac⌜m = 2⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜3 ≤ m⌝ (ante_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_ASMS_T discard_tac THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜ℕℝ 0 ≤ ℕℝ 2⌝ asm_tac THEN REPEAT strip_tac);
a(all_fc_tac[sqrt_0_≤_thm, sqrt_thm]);
a(swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀x⦁ℕℝ 0 ≤ ~x ⇔ x ≤ ℕℝ 0⌝,
	ℕℝ_≤_thm]);
a(swap_nth_asm_concl_tac 1 THEN all_var_elim_asm_tac1);
a(asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
val ⦏sqrt_2_lemma⦎ = save_pop_thm"sqrt_2_lemma";
=TEX
%%%%
%%%%

And, using the fact that $\sqrt{2}$ is not an integer, we get the specific conclusion of the third proof:

=SML
set_goal([], ⌜¬Sqrt (ℕℝ 2) ∈ ℚ⌝);
a(contr_tac);
a(LEMMA_T ⌜ℕℝ 0 ≤ ℕℝ 2⌝ asm_tac THEN1 rewrite_tac[]);
a(lemma_tac ⌜ℕℝ 2 ∈ ℤ⌝ THEN1
	(rewrite_tac[ℤ_thm] THEN ∃_tac⌜ℕℤ 2⌝
		THEN rewrite_tac[ℤℝ_ℕℤ_thm]
		THEN REPEAT strip_tac));
a(all_fc_tac[quadratic_surd_thm]);
a(all_fc_tac[sqrt_2_lemma]);
val ⦏sqrt_2_irrational_thm⦎ = save_pop_thm"sqrt_2_irrational_thm";
=TEX
%%%%
%%%% WILSON'S THEOREM

=SML
set_goal([], ⌜∀p m⦁
	p ∈ Prime ∧ m < p ∧ m^2 Mod p = 1
⇒	m = 1 ∨ p = m + 1⌝);
a(rewrite_tac[ℕ_exp_clauses] THEN REPEAT strip_tac);
a(all_fc_tac[prime_0_less_thm]);
a(strip_asm_tac(∀_elim⌜m⌝ ℕ_cases_thm)
	THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(swap_nth_asm_concl_tac 1);
a(ALL_FC_T rewrite_tac[zero_div_mod_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜(i + 1) * (i + 1) = ((i + 1) * (i + 1)) Div p * p + ((i + 1) * (i + 1)) Mod p⌝
	ante_tac
	THEN1 (bc_thm_tac div_mod_thm THEN REPEAT strip_tac));
a(ALL_FC_T asm_rewrite_tac[mod_clauses]);
a(conv_tac(ONCE_MAP_C anf_conv) THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a(lemma_tac⌜p Divides i*(2+i)⌝
	THEN1 (asm_rewrite_tac[divides_mod_thm]
		THEN conv_tac(ONCE_MAP_C anf_conv)
		THEN ALL_FC_T asm_rewrite_tac[mod_clauses]));
a(lemma_tac⌜i < p⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(lemma_tac⌜i Mod p = i ∧ (i+1) Mod p = (i+1)⌝
	THEN1 (all_fc_tac[less_div_mod_thm] THEN REPEAT strip_tac));
a(lemma_tac⌜¬p Divides i ∧ ¬p Divides (i+1)⌝
	THEN1 (asm_rewrite_tac[divides_mod_thm]
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(GET_NTH_ASM_T 12 (fn th => fc_tac[rewrite_rule[prime_thm]th]));
a(POP_ASM_T (strip_asm_tac o rewrite_rule[divides_def]));
a(asm_rewrite_tac[]);
a(POP_ASM_T ante_tac);
a(cases_tac⌜k = 0⌝ THEN1 asm_rewrite_tac[] THEN strip_tac);
a(cases_tac⌜k = 1⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜2 ≤ k⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1"lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [2, 4] discard_tac THEN all_var_elim_asm_tac1);
a(i_contr_tac THEN PC_T1"lin_arith" asm_prove_tac[]);
val ⦏sqrt_1_mod_p_thm⦎ = save_pop_thm"sqrt_1_mod_p_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p⦁
	p ∈ Prime
⇒	1 < p ∧ 1^2 Mod p = 1
∧	0 < (p-1) ∧ (p-1) < p ∧ (p-1)^2 Mod p = 1⌝);
a(∀_tac THEN ⇒_tac);
a(all_fc_tac[prime_0_less_thm]);
a(POP_ASM_T (strip_asm_tac o
	once_rewrite_rule[plus_comm_thm] o
	rewrite_rule[≤_def,
		pc_rule1 "lin_arith" prove_rule[]
		⌜0 < p ⇔ 1 ≤ p⌝])
	THEN all_var_elim_asm_tac1);
a(all_fc_tac[prime_2_≤_thm]);
a(POP_ASM_T (strip_asm_tac o
	rewrite_rule[pc_rule1 "lin_arith" prove_rule[]
		⌜∀p⦁ 2 ≤ p ⇔ 1 < p⌝]));
a(asm_rewrite_tac[ℕ_exp_clauses]);
a(LEMMA_T ⌜1 < i + 1⌝ asm_tac THEN1 PC_T1"lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[less_div_mod_thm]);
a(LEMMA_T ⌜0 < i + 1⌝ asm_tac THEN1 PC_T1"lin_arith" asm_prove_tac[]);
a(ALL_FC_T once_rewrite_tac[mod_times_homomorphism_thm]);
a(LEMMA_T⌜i Mod (i+1) = ((i+1)+i) Mod (i+1)⌝ rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[mod_clauses]);
a(ALL_FC_T rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv)
	mod_times_homomorphism_thm]);
a(conv_tac(ONCE_MAP_C (LEFT_C anf_conv)));
a(LEMMA_T⌜1 + 4 * i + 4 * i * i = (4*i)*(i+1) + 1⌝
	rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" prove_tac[]);
a(ALL_FC_T rewrite_tac[mod_clauses, less_div_mod_thm]);
val ⦏sqrt_1_mod_p_thm1⦎ = save_pop_thm"sqrt_1_mod_p_thm1";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀d m n⦁
	0 < d ∧ (m + n) Mod d = m Mod d
⇒	n Mod d = 0⌝);
a(REPEAT strip_tac THEN contr_tac);
a(LEMMA_T⌜(m+n) = (m+n) Div d * d + (m+n) Mod d⌝ ante_tac
	THEN1 (bc_thm_tac div_mod_thm THEN REPEAT strip_tac)
	THEN asm_rewrite_tac[]);
a(LEMMA_T⌜m = m Div d * d + m Mod d⌝
	(fn th => conv_tac(RAND_C(LEFT_C(once_rewrite_conv [th]))))
	THEN1 (bc_thm_tac div_mod_thm THEN REPEAT strip_tac));
a(rewrite_tac[∀_elim⌜m Mod d⌝ plus_order_thm]);
a(swap_nth_asm_concl_tac 1);
a(LEMMA_T⌜(m Div d * d + n) Mod d = 0⌝ ante_tac
	THEN1 (asm_rewrite_tac[]
		THEN ALL_FC_T rewrite_tac[mod_clauses]));
a(LEMMA_T⌜(m Div d * d + n) Mod d = 0⌝ ante_tac
	THEN1 asm_rewrite_tac[]
	THEN ALL_FC_T rewrite_tac[mod_clauses]);
val ⦏plus_mod_thm⦎ = save_pop_thm"plus_mod_thm";

=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p m⦁
	p ∈ Prime ∧ ¬p Divides m
⇒	∃⋎1n⦁ n < p ∧ (m*n) Mod p = 1⌝);
a(REPEAT strip_tac);
a(all_fc_tac[prime_0_less_thm]);
a(lemma_tac⌜∀i j⦁i ≤ j ∧ j < p ∧ (m*i) Mod p = (m*j) Mod p
	⇒ i = j⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[≤_def] THEN contr_tac THEN all_var_elim_asm_tac1);
a(swap_nth_asm_concl_tac 2 THEN conv_tac(ONCE_MAP_C anf_conv));
a(conv_tac (RAND_C eq_sym_conv) THEN contr_tac);
a(all_fc_tac[plus_mod_thm]);
a(lemma_tac⌜i' < p⌝ THEN1 PC_T1"lin_arith" asm_prove_tac[]);
a(lemma_tac⌜i' Mod p = i'⌝ THEN1 all_fc_tac[less_div_mod_thm]);
a(lemma_tac⌜¬p Divides i' ∧ p Divides (i'*m)⌝
	THEN1 asm_rewrite_tac[divides_mod_thm]);
a(GET_NTH_ASM_T 11 (fn th => fc_tac[rewrite_rule[prime_thm]th]));
(* *** Goal "2" *** *)
a(lemma_tac⌜{k | k < p} = {r | ∃i⦁ i < p ∧ r = (m*i) Mod p}⌝);
(* *** Goal "2.1" *** *)
a(conv_tac eq_sym_conv THEN bc_thm_tac ⊆_size_eq_thm);
a(asm_rewrite_tac[range_finite_size_thm]
	THEN PC_T1 "sets_ext" REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(all_var_elim_asm_tac1 THEN ALL_FC_T rewrite_tac[mod_less_thm]);
(* *** Goal "2.1.2" *** *)
a(strip_asm_tac (∀_elim⌜p⌝ range_finite_size_thm));
a(POP_ASM_T (fn th => conv_tac(RIGHT_C(eq_match_conv(eq_sym_rule th)))));
a(bc_thm_tac (prove_rule[]⌜∀a b:'a SET⦁ a ∈ Finite ∧ #a = #b ⇒ #a = #b⌝));
a(bc_thm_tac (bijection_finite_size_thm));
a(∃_tac⌜λk⦁(m*k) Mod p⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(lemma_tac⌜x ≤ y ∨ y ≤ x⌝ THEN1 PC_T1"lin_arith" prove_tac[]
	THEN1 all_asm_fc_tac[]);
a(DROP_NTH_ASM_T 6 (fn th => all_fc_tac[conv_rule(ONCE_MAP_C eq_sym_conv) th]));
(* *** Goal "2.2" *** *)
a(all_fc_tac[prime_2_≤_thm]);
a(LEMMA_T ⌜1 ∈ {k | k < p}⌝ ante_tac
	THEN1 (rewrite_tac[]
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(DROP_NTH_ASM_T 2 pure_rewrite_thm_tac);
a(REPEAT strip_tac);
a(∃⋎1_tac⌜i⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(lemma_tac⌜n' ≤ i ∨ i ≤ n'⌝ THEN1 PC_T1"lin_arith" prove_tac[]
	THEN1 all_asm_fc_tac[]);
a(DROP_NTH_ASM_T 7 (fn th => all_fc_tac[conv_rule(ONCE_MAP_C eq_sym_conv) th]));
val ⦏times_mod_p_inverse_thm⦎ = save_pop_thm"times_mod_p_inverse_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p m⦁
	p ∈ Prime ∧ 0 < m ∧ m < p
⇒	∃⋎1n⦁ n < p ∧ (m*n) Mod p = 1⌝);
a(REPEAT strip_tac);
a(all_fc_tac[prime_0_less_thm]);
a(bc_thm_tac times_mod_p_inverse_thm);
a(REPEAT strip_tac THEN asm_rewrite_tac[divides_mod_thm]);
a(ALL_FC_T rewrite_tac[less_div_mod_thm]);
a(contr_tac THEN all_var_elim_asm_tac1);
val ⦏times_mod_p_inverse_thm1⦎ = save_pop_thm"times_mod_p_inverse_thm1";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p m n k⦁
	p ∈ Prime
∧	0 < m ∧ m < p
∧	0 < n ∧ n < p
∧	0 < k ∧ k < p
∧	((m*n) Mod p = 1 ∨ (n*m) Mod p = 1)
∧	((m*k) Mod p = 1 ∨ (k*m) Mod p = 1)
⇒	n = k
⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜n*m = m*n ∧ k*m = m*k⌝]);
a(REPEAT strip_tac);
a(all_fc_tac[times_mod_p_inverse_thm1]);
a(all_asm_fc_tac[] THEN asm_rewrite_tac[]);
val ⦏times_mod_p_inverse_unique_thm⦎ =
save_pop_thm"times_mod_p_inverse_unique_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p⦁
	p ∈ Prime
⇒	Π {m | 1 < m ∧ m + 1 < p} (λm⦁m) Mod p = 1⌝);
a(REPEAT strip_tac);
a(all_fc_tac[prime_0_less_thm]);
a(lemma_tac ⌜∃u⦁
	{m | 1 < m ∧ m + 1 < p} = ⋃u
∧	u = {A | ∃i j⦁1 < i ∧ i + 1 < p ∧ 1 < j ∧ j + 1 < p
		∧ ¬i = j ∧ (i*j) Mod p = 1
		∧ A = {i; j}}
∧	u ∈ Finite
∧	u ⊆ Finite
∧	(∀ a b⦁ a ∈ u ∧ b ∈ u ∧ ¬ a ∩ b = {} ⇒ a = b)	⌝ THEN1 (∃_tac⌜{A | ∃i j⦁1 < i ∧ i + 1 < p ∧ 1 < j ∧ j + 1 < p
		∧ ¬i = j ∧ (i*j) Mod p = 1
		∧ A = {i; j}}⌝
	THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(lemma_tac⌜0 < x ∧ x < p⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_fc_tac[times_mod_p_inverse_thm1]);
a(∃_tac⌜{x; n}⌝ THEN rewrite_tac[]);
a(∃_tac⌜x⌝ THEN ∃_tac⌜n⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜x = n⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1.1" *** *)
a(all_var_elim_asm_tac);
a(ante_tac(list_∀_elim[⌜p⌝, ⌜n⌝] sqrt_1_mod_p_thm));
a(asm_rewrite_tac[ℕ_exp_clauses]);
a(contr_tac THEN all_var_elim_asm_tac1);
(* *** Goal "1.1.2" *** *)
a(swap_nth_asm_concl_tac 1);
(* *** Goal "1.1.2.1" *** *)
a(swap_nth_asm_concl_tac 3);
a(cases_tac⌜n = 0⌝ THEN1 ALL_FC_T asm_rewrite_tac[zero_div_mod_thm]);
a(cases_tac⌜¬n = 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN rewrite_tac[]
	THEN swap_nth_asm_concl_tac 1);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
a(ALL_FC_T once_rewrite_tac[mod_times_homomorphism_thm]);
a(ALL_FC_T asm_rewrite_tac[less_div_mod_thm]);
(* *** Goal "1.1.2.2" *** *)
a(LEMMA_T ⌜(p - 1) ^ 2 Mod p = 1⌝ (strip_asm_tac o rewrite_rule[ℕ_exp_clauses])
	THEN1 all_fc_tac[sqrt_1_mod_p_thm1]);
a(lemma_tac⌜p = n + 1 ∧ 0 < n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]
	THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[]));
a(ante_tac(list_∀_elim[⌜n+1⌝, ⌜n⌝] times_mod_p_inverse_thm1));
a(REPEAT strip_tac);
a(lemma_tac⌜n = n'⌝ THEN1 POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
a(all_var_elim_asm_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
a(once_rewrite_tac[times_comm_thm] THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 8 ante_tac THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
(* *** Goal "1.3" *** *)
a(DROP_NTH_ASM_T 8 ante_tac THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
(* *** Goal "2" *** *)
a(strip_asm_tac(∀_elim⌜p⌝ range_finite_size_thm));
a(bc_thm_tac ⊆_finite_thm
	THEN ∃_tac⌜ℙ{i|i<p}⌝
	THEN ALL_FC_T rewrite_tac[ℙ_finite_size_thm]);
a(PC_T1"sets_ext" REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(bc_thm_tac ⊆_finite_thm
	THEN ∃_tac⌜{i|i<p}⌝
	THEN rewrite_tac[range_finite_size_thm]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(POP_ASM_T (PC_T1 "sets_ext1" strip_asm_tac));
a(LEMMA_T⌜∀t⦁(1 < t ⇒ 0 < t) ∧ (t + 1 < p ⇒ t < p)⌝
	(fn th => all_fc_tac[th])
	THEN1 PC_T1 "lin_arith" prove_tac[]);
a(all_var_elim_asm_tac1 THEN all_var_elim_asm_tac
	THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN all_var_elim_asm_tac
	THEN all_fc_tac[times_mod_p_inverse_unique_thm]);
(* *** Goal "5" *** *)
a(GET_NTH_ASM_T 5 rewrite_thm_tac
	THEN ALL_FC_T rewrite_tac[ind_prod_ℕ_⋃_thm]);
a(lemma_tac⌜1 < p⌝
	THEN1 (all_fc_tac[prime_2_≤_thm]
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(LEMMA_T⌜1 = 1 Mod p⌝ once_rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[less_div_mod_thm]);
a(LEMMA_T⌜1 = Π u (λk⦁1)⌝ once_rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[ind_prod_ℕ_k_1_thm]);
a(ALL_FC_T once_rewrite_tac[ind_prod_ℕ_mod_thm]);
a(rewrite_tac[]);
a(bc_thm_tac(prove_rule[]⌜∀a b⦁a = b ⇒ a Mod p = b Mod p⌝));
a(bc_thm_tac ind_prod_ℕ_local_thm
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(LEMMA_T⌜{i;j} = {i} ∪ {j}⌝ rewrite_thm_tac
	THEN PC_T1 "sets_ext1" prove_tac[]);
a(LEMMA_T⌜¬i ∈ {j}⌝ asm_tac
	THEN1 PC_T1 "sets_ext1" asm_rewrite_tac[]);
a(lemma_tac⌜{j} ∈ Finite⌝ THEN1 rewrite_tac[singleton_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(asm_rewrite_tac[ind_prod_ℕ_clauses]);
a(ALL_FC_T rewrite_tac[less_div_mod_thm]);
val ⦏wilson_lemma1⦎ = save_pop_thm"wilson_lemma1";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p⦁
	p ∈ Prime
⇒	Π {m| 0 < m ∧ m < p} (λ m⦁ m) Mod p = p - 1⌝);
a(REPEAT strip_tac);
a(all_fc_tac[prime_2_≤_thm]);
a(LEMMA_T ⌜{m | 0 < m ∧ m < p} =
	{1} ∪ {m | 1 < m ∧ m < p}⌝
	rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" REPEAT strip_tac
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(LEMMA_T ⌜¬1 ∈ {m | 1 < m ∧ m < p}⌝ asm_tac
	THEN1 rewrite_tac[]);
a(strip_asm_tac (∀_elim⌜p⌝ range_finite_size_thm));
a(lemma_tac⌜{m | 1 < m ∧ m < p} ⊆ {i|i < p}⌝
	THEN1 PC_T1 "sets_ext1" prove_tac[]);
a(all_fc_tac[⊆_finite_thm]);
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(LIST_DROP_NTH_ASM_T[1, 2, 3, 5] discard_tac);
a(LEMMA_T ⌜1 ≤ p⌝ (strip_asm_tac o
	once_rewrite_rule[plus_comm_thm] o
	rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(cases_tac⌜i = 1⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜∀m⦁¬(1 < m ∧ m < 2)⌝,
	pc_rule1 "sets_ext1" prove_rule[]
	⌜{x|F} = {}⌝,
	ind_prod_ℕ_def]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜{m | 1 < m ∧ m < i + 1} =
	{i} ∪ {m | 1 < m ∧ m < i}⌝
	rewrite_thm_tac
	THEN1 (PC_T1 "sets_ext1" REPEAT strip_tac
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(LEMMA_T ⌜¬i ∈ {m | 1 < m ∧ m < i}⌝ asm_tac
	THEN1 rewrite_tac[]);
a(lemma_tac⌜{m | 1 < m ∧ m < i} ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜{m| m < i}⌝
		THEN rewrite_tac[range_finite_size_thm]
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(LEMMA_T⌜0 < i + 1⌝ asm_tac THEN1 rewrite_tac[]);
a(ALL_FC_T once_rewrite_tac[mod_times_homomorphism_thm]);
a(ALL_FC_T rewrite_tac[
	rewrite_rule[](∀_elim⌜i+1⌝wilson_lemma1)]);
a(LEMMA_T⌜i < i + 1⌝ asm_tac THEN1 rewrite_tac[]);
a(ALL_FC_T rewrite_tac[less_div_mod_thm]);
val ⦏wilson_lemma2⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀n⦁
	1 < n
∧	¬n ∈ Prime
⇒	¬Π {m| 0 < m ∧ m < n} (λ m⦁ m) Mod n = n - 1⌝);
a(contr_tac);
a(LEMMA_T⌜0 < n ∧ 1 ≤ n⌝ (strip_asm_tac o
	rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜(Π {m|0 < m ∧ m < n} (λ m⦁ m) + 1) Mod n = 0⌝ ante_tac
	THEN1 (ALL_FC_T asm_rewrite_tac[mod_def]
		THEN all_var_elim_asm_tac1
		THEN rewrite_tac[]));
a(LIST_DROP_NTH_ASM_T[1, 2, 3] discard_tac);
a(all_fc_tac[prime_divisor_thm1]);
a(swap_nth_asm_concl_tac 1);
a(cases_tac⌜n' = 0⌝
	THEN1 (asm_rewrite_tac[] THEN contr_tac
		THEN all_var_elim_asm_tac1));
a(cases_tac⌜n' = 1⌝
	THEN1 (asm_rewrite_tac[] THEN contr_tac
		THEN all_var_elim_asm_tac1));
a(LEMMA_T⌜2 ≤ n'⌝ (strip_asm_tac o rewrite_rule[≤_def])
THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [2, 3] discard_tac
	THEN all_var_elim_asm_tac1);
a(swap_nth_asm_concl_tac 1);
a(cases_tac⌜n ≤ p⌝ THEN1
	(POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def])
	THEN all_var_elim_asm_tac1
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]));
a(all_fc_tac[prime_0_less_thm]);
a(lemma_tac⌜p < n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ {m|0 < m ∧ m < n} = 
	{p} ∪ {m|0 < m ∧ m < n ∧ ¬m = p}⌝
	rewrite_thm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(LEMMA_T⌜ ¬p ∈ {m|0 < m ∧ m < n ∧ ¬m = p}⌝
	asm_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜ {m|0 < m ∧ m < n ∧ ¬m = p} ∈ Finite⌝
	THEN1 (bc_thm_tac ⊆_finite_thm
		THEN ∃_tac⌜{m|m < n}⌝
		THEN rewrite_tac[range_finite_size_thm] 
		THEN1 PC_T1 "sets_ext1" prove_tac[]));
a(ALL_FC_T rewrite_tac[ind_prod_ℕ_def]);
a(contr_tac);
a(lemma_tac⌜0 < n⌝ THEN1 PC_T1 "lin_arith"asm_prove_tac[]);
a(LEMMA_T⌜n Divides (p * Π {m|0 < m ∧ m < n ∧ ¬ m = p} (λ m⦁ m) + 1)⌝ (strip_asm_tac o rewrite_rule[divides_def])
	THEN1 asm_rewrite_tac[divides_mod_thm]);
a(POP_ASM_T ante_tac THEN all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜∀i j⦁i * p * j = p* i * j⌝]);
a(contr_tac);
a(LEMMA_T⌜∀a b⦁p * a + 1 = p * b ⇒
	(p * a + 1) Mod p = (p * b) Mod p⌝
	(fn th => all_fc_tac[th])
	THEN1 (REPEAT strip_tac THEN asm_rewrite_tac[]));
a(POP_ASM_T ante_tac THEN ALL_FC_T rewrite_tac[mod_clauses]);
a(all_fc_tac[prime_2_≤_thm]);
a(lemma_tac⌜1 < p⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[less_div_mod_thm]);
val ⦏wilson_lemma3⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p⦁
	1 < p
⇒	(p ∈ Prime ⇔ (p - 1)! Mod p = p - 1)⌝);
a(∀_tac THEN ⇒_tac);
a(lemma_tac⌜0 < p⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[factorial_ind_prod_ℕ_thm1]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜∀k⦁1 ≤ k ⇔ 0 < k⌝]);
a(contr_tac THEN all_fc_tac[wilson_lemma2, wilson_lemma3]);
val ⦏wilson_thm⦎ = save_pop_thm"wilson_thm";
=TEX
%%%%
%%%%

=SML
(*
drop_main_goal();
*)
push_consistency_goal⌜Abs⋎ℕ⌝;
a(prove_∃_tac THEN REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜i'⌝ ℤ_cases_thm)
	THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(∃_tac⌜m⌝ THEN rewrite_tac[ℤ_ℕ_abs_thm]);
(* *** Goal "2" *** *)
a(∃_tac⌜m⌝ THEN rewrite_tac[ℤ_ℕ_abs_thm]);
save_consistency_thm ⌜Abs⋎ℕ⌝ (pop_thm());
val ⦏abs_ℕ_def⦎ = get_spec⌜Abs⋎ℕ⌝;
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀i m⦁ Abs⋎ℕ i = m ⇔ Abs i = ℕℤ m⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[abs_ℕ_def]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜Abs i = ℕℤ(Abs⋎ℕ i)⌝ ante_tac THEN1 rewrite_tac[abs_ℕ_def]);
a(asm_rewrite_tac[ℕℤ_one_one_thm]);
a(STRIP_T rewrite_thm_tac);
val ⦏abs_ℕ_thm⦎ = save_pop_thm"abs_ℕ_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀m⦁ Abs⋎ℕ(ℕℤ m) = m ∧ Abs⋎ℕ(~(ℕℤ m)) = m⌝);
a(rewrite_tac[abs_ℕ_thm, ℤ_ℕ_abs_thm]);
val ⦏abs_ℕ_ℕℤ_thm⦎ = save_pop_thm"abs_ℕ_ℕℤ_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀i j⦁ Abs⋎ℕ(i * j) = Abs⋎ℕ i * Abs⋎ℕ j⌝);
a(rewrite_tac[abs_ℕ_thm, ℕℤ_times_homomorphism_thm, abs_ℕ_def,
	ℤ_abs_times_thm]);
val ⦏abs_ℕ_times_thm⦎ = save_pop_thm"abs_ℕ_times_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀i⦁ 
	(ℕℤ 0 ≤ i ⇒ i = ℕℤ(Abs⋎ℕ i))
∧	(¬ℕℤ 0 ≤ i ⇒ i = ~(ℕℤ(Abs⋎ℕ i)))⌝);
a(lemma_tac ⌜∀i⦁ ℕℤ 0 ≤ i ⇒ i = ℕℤ(Abs⋎ℕ i)⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(LEMMA_T⌜∀x⦁i = x ⇔ Abs i = x⌝ rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[ℤ_abs_thm]);
a(bc_thm_tac abs_ℕ_thm THEN strip_tac);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac ⌜ℕℤ 0 ≤ ~i⌝ THEN1 PC_T1 "ℤ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(POP_ASM_T ante_tac THEN pure_rewrite_tac[
	pc_rule1 "ℤ_lin_arith" prove_rule[]⌜~i = ~(ℕℤ 1) * i⌝,
	abs_ℕ_times_thm, abs_ℕ_ℕℤ_thm]
	THEN rewrite_tac[]);
a(STRIP_T (rewrite_thm_tac o eq_sym_rule));
a(PC_T1 "ℤ_lin_arith" prove_tac[]);
val ⦏abs_ℕ_cases_thm⦎ = save_pop_thm"abs_ℕ_cases_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀i:ℤ⦁ Abs i * Abs i = i * i⌝);
a(REPEAT strip_tac
	THEN PC_T1 "basic_hol" cases_tac⌜ℕℤ 0 ≤ i⌝
	THEN asm_rewrite_tac[ℤ_abs_def]
	THEN PC_T1 "ℤ_lin_arith" prove_tac[]);
val ⦏ℤ_abs_square_thm⦎ = save_pop_thm"ℤ_abs_square_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p m⦁ p ∈ Prime ⇒ ¬p = m^2⌝);
a(rewrite_tac[ℕ_exp_clauses, prime_def] THEN contr_tac);
a(DROP_NTH_ASM_T 2 (ante_tac o list_∀_elim [⌜m⌝, ⌜m⌝]));
a(asm_rewrite_tac[] THEN swap_nth_asm_concl_tac 1
	THEN asm_rewrite_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏prime_¬_square_thm⦎ = save_pop_thm"prime_¬_square_thm";
=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀p m⦁
	p ∈ Prime
∧	p = 4*m + 1
⇒	∃a b⦁ p = a^2 + b^2
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃i j⦁ ℕℤ p = i*i + j*j⌝
	THEN1 bc_thm_tac two_squares_lemma);
(* *** Goal "1" *** *)
a(∃_tac⌜ℕℤ m⌝ THEN all_var_elim_asm_tac1);
a(asm_rewrite_tac[ℕℤ_times_homomorphism_thm,
	ℕℤ_plus_homomorphism_thm,
	ℕℤ_less_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[prime_def]);
(* *** Goal "1.2" *** *)
a(rewrite_tac[ℕℤ_plus_homomorphism_thm1, ℕℤ_times_homomorphism_thm1]);
a(LEMMA_T⌜i * i = Abs i * Abs i⌝ rewrite_thm_tac
	THEN1 rewrite_tac[ℤ_abs_square_thm]);
a(LEMMA_T⌜Abs i * Abs i = Abs (i*i)⌝ rewrite_thm_tac
	THEN1 rewrite_tac[ℤ_abs_times_thm]);
a(contr_tac THEN LEMMA_T⌜Abs⋎ℕ(i*i) = 4*m + 1⌝ ante_tac
	THEN1 asm_rewrite_tac[abs_ℕ_thm]);
a(rewrite_tac[abs_ℕ_times_thm]);
a(conv_tac(RAND_C eq_sym_conv) THEN ALL_FC_T rewrite_tac[
	rewrite_rule[ℕ_exp_clauses]
		(prime_¬_square_thm)]);
(* *** Goal "1.3" *** *)
a(lemma_tac⌜∃s⦁a = ℕℤ s⌝ THEN1 ∃_tac⌜Abs⋎ℕ a⌝
	THEN1 (	lemma_tac⌜ℕℤ 0 ≤ a⌝
	THEN1	PC_T1 "ℤ_lin_arith" asm_prove_tac[]
	THEN 	all_fc_tac[abs_ℕ_cases_thm]));
a(lemma_tac⌜∃t⦁b = ℕℤ t⌝ THEN1 ∃_tac⌜Abs⋎ℕ b⌝
	THEN1 (	lemma_tac⌜ℕℤ 0 ≤ b⌝
	THEN1	PC_T1 "ℤ_lin_arith" asm_prove_tac[]
	THEN 	all_fc_tac[abs_ℕ_cases_thm]));
a(all_var_elim_asm_tac1 THEN all_asm_ante_tac);
a(rewrite_tac[ℕℤ_plus_homomorphism_thm1,
	ℕℤ_times_homomorphism_thm1,
	prime_def, ℕℤ_one_one_thm, ℕℤ_less_thm]);
a(contr_tac THEN asm_fc_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜Abs⋎ℕ i⌝ THEN ∃_tac⌜Abs⋎ℕ j⌝
	THEN POP_ASM_T ante_tac);
a(LEMMA_T⌜i*i + j*j = ℕℤ(Abs⋎ℕ i ^ 2 + Abs⋎ℕ j ^ 2)⌝
	(fn th => rewrite_tac[th, ℕℤ_one_one_thm]));
a(rewrite_tac[ℕℤ_plus_homomorphism_thm, ℕ_exp_clauses,
	conv_rule(ONCE_MAP_C eq_sym_conv) abs_ℕ_times_thm,
	abs_ℕ_def, ℤ_abs_times_thm, ℤ_abs_square_thm]);
val ⦏two_squares_thm⦎ = save_pop_thm"two_squares_thm";
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
	val _ = output_theorems{out_file="wrk074.th.doc", theory="-"};
end;
=TEX
} %\Hide
\end{document}

=TEX
%%%%
%%%%
=IGN

