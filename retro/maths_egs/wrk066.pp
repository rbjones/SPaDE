=IGN
********************************************************************************
wrk066.doc: this file is supplementary material for the ProofPower system

Copyright (c) 2004 Lemma 1 Ltd.

This file is supplied under the GNU General Public Licence (GPL) version 2.

See the file LICENSE supplied with ProofPower source for the terms of the GPL
or visit the OpenSource web site at http://www.opensource.org/

Contact: Rob Arthan < rda@lemma-one.com >
********************************************************************************
$Id: wrk066.doc,v 1.122 2012/06/05 12:36:10 rda Exp rda $
********************************************************************************
=IGN
pp_make_database -f -p hol maths_egs
docsml wrk066
xpp wrk066.doc -d maths_egs -i wrk066 &
doctex wrk066 wrk066.th; texdvi -b wrk066; texdvi wrk066; texdvi wrk066
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

\def\SinhName{\mbox{{\sf sinh}}}
\def\Sin#1{\SinName(#1)}

\def\CoshName{\mbox{{\sf cosh}}}
\def\Cosh#1{\CoshName(#1)}

\def\ArcSinName{\mbox{{\sf arc sin}}}
\def\ArcSin#1{\ArcSinName(#1)}

\def\ArcCosName{\mbox{{\sf arc cos}}}
\def\ArcCos#1{\ArcCosName(#1)}

\def\ArcSinhName{\mbox{{\sf arc sinh}}}
\def\ArcSinh#1{\ArcSinName(#1)}

\def\ArcTanName{\mbox{{\sf arc tan}}}
\def\ArcTan#1{\ArcSinName(#1)}

\def\Abs#1{|#1|}

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

\def\Hide#1{\relax}
\makeindex
\title{Mathematical Case Studies: \\ --- \\ Basic Analysis\thanks{
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
This {\ProductHOL} script contains definitions and proofs concerning
some of the basics of analysis.
The material covered includes: polynomial functions on the real numbers,
limits of sequences, continuity of functions of real variables, differentiation,
limits of function values, uniform convergence of limits of functions,
series and power series and their use in defining the exponential,
logarithm and sine and cosine functions;
the other circular trigonometric functions and the hyperbolic trigonometric functions and a selection of the inverse functions;
definition and basic properties of the Henstock-Kurzweil gauge integral including the fundamental theorem of the calculus;
calculation of the areas of some simple plane sets.

\end{abstract}
\vfill
\begin{centering}

\bf Copyright \copyright\ : Lemma 1 Ltd 2004--\number\year \\
Reference: LEMMA1/HOL/WRK066; Current git revision: \VCVersion


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
\begin{itemize}

\item
Make systematic use of open and closed intervals in the statements
of the basic theorems on limits etc. (A start has been made on this,
recent results having been stated using intervals).

\item⇸
Consider adding a more detailed informal discussion of the extension of
Mitchell's ``axiomatic'' approach to the trigonometric functions to give the results
on periodicity.

\item
Consider adding the theory of uniform continuity.

\item
Add more results on the gauge integral (in particular, the calculational results one needs for integrals like the ones that define the Laplace transform).

\end{itemize}

\subsection*{Acknowledgments}

My thanks to Robin Chapman, Matthew Frank, Hanne Gottliebsen, John Harrison and Roger Jones for their helpful correspondence.


\bibliographystyle{plain}
\bibliography{fmu}

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
This document defines a theory
=INLINEFT
analysis
=TEX
\ giving  a formalisation in  {\ProductHOL} of the basics of analysis on the
real number line.
The subjects covered are the basic facts about:

\begin{itemize}
\item polynomial functions on the real numbers
\item limits of sequences
\item continuity of functions
\item differentiation
\item limits of function values
\item uniform convergence of limits of functions
\item series and power series
\item special functions: exponential function, natural logarithm, sine and cosine
\item L'H\^{o}pital's Rule and some applications to particular limits
\item further special functions: square root, circular and hyperbolic trigonometric functions.
\item the Henstock-Kurzweil gauge integral and the fundamental theorem of the calculus with an application to the areas of plane sets.
\end{itemize}



This is a similar enterprise  to John Harrison's HOL treatment of the calculus described in chapter 3 of his thesis \cite{Harrison96}, but was inspired  by rather different motivations.
This leads to some differences in methods  and in the choice of subject matter. In particular, I am interested in geometric and topological applications of the material, particularly the trigonometric functions and not so much in computational aspects or formalised numerical analysis.


On the one hand, the geometrical motivations mean that there is less emphasis on certain results that are important in numerical analysis (e.g., Taylor's theorem).
On the other hand, they make it more attractive to prove somewhat more general results, e.g., the result on ``differentiating under the limit sign'' that leads to the general theorem on the convergence of power series and their derivatives (Harrison proves these results for specific power series by less general methods).

Another difference of approach in comparison with Harrison's is encouraged by the {\Product} tradition of using the HOL constant specification facility to specify mathematical objects implicitly wherever that seems to accord with good mathematical practice.
For example, we prefer to specify the transcendental functions using differential equations rather than power series.
In the same spirit, Archimedes' constant, $\pi$, is characterised as the positive generator of the group of zeroes of the sine function.

The work was begun late in 2001 originally just to exercise the real number theory in {\ProductHOL} on a purely mathematical application.
That work had some success with polynomials, limits, continuity and derivatives and so on but foundered due to lack of time and a technical difficulty with the traditional textbook approach to the result on differentiating under the limit sign mentioned above.
This technical difficulty arises from the fact that, while, for simplicity, I deal only with two-sided derivatives, the usual textbook proofs involve working with functions defined on a closed interval and make use of the derivatives at the ends of the interval where they are inherently one-sided.
In fact, with hindsight, this turns out not to be a problem:
essentially the same results can be formulated in equal generality using open intervals and two-sided limits.

Motivated by some more recent work on topology and geometry, I returned to the document  late in 2003 and found the missing results not too difficult to supply.
This leads immediately to the applications in defining the basic transcendental functions.
This latter material constitutes quite a large fraction of the proof scripts (about 15\% of the current total), but the material is very straightforward and the development of the properties of these functions from their specifications via differential equations took only a few evenings' work.

Since 2003, the treatment has grown as time and inclination has permitted,often motivated by Freek Wiedijk's list of 100 challenge problems. In particular, the theory of the Henstock-Kurzweil has been developed and applied in various ways, e.g., to calculate the area of a circle. 

Undertaking this kind of work is a mathematical activity of an unusual, often entertaining, albeit sometimes frustrating nature. It is rather like preparing the material for a course or a textbook with the assistance of an amanuensis who is an {\it idiot savant} of an unusual kind. 
Firstly, he insists on and gets absolute editorial control over what purports to be a proof: every proof step is checked with complete accuracy and no lacunae slip his attention.
On the more constructive side, he is capable of amazing feats of calculation: so for example, before you start he can already (almost) infallibly decide the insolubility of a system of linear constraints.
Reducing problems to such systems becomes second nature as the work progresses.
Similarly, once rules for differentiating sums, product and so on are available, the amanuensis can readily be taught how to apply them to arbitrarily complex expressions.
He can then determine, for example, that the derivative of $\Cos{x}^2 + \Sin{x}^2$ vanishes without any work on your part at all. 

Another remarkable property of the amanuensis is that there is absolutely no need to present ideas in simple-minded ways to help him get used to them.
I imagine that many undergraduates encountering the calculus for the first time would be somewhat fazed by the definition of the set of polynomial functions as the smallest set of functions containing constants and the identity function and closed under addition and multiplication.
This is the very first definition we give (see section~\ref{Polynomials}).
I imagine most undergraduates would be completely fazed by immediately having to derive a principle of proof by induction over this set and putting that principle to work to derive useful general theory. Similarly, a lot of geometric notions and even a little topological group theory are needed to motivate the differential equations for the transcendental functions in section~\ref{SomeSpecialFunctions}, but the amanuensis does not need this:
as soon as you convince him that the definitions are consistent (by showing that the power series expansions satisfy the equations), he will  happily help you derive the usual algebraic properties, proving things like the sum rule for sine and cosine without tears.


The excellent textbooks by Rudin \cite{Rudin76} and Mitchell \cite{Mitchell69} are cited several times in the discussion.
In particular, the formal treatment of power series is based on Rudin and the ``axiomatic'' derivation of the properties of the trigonometric functions using the defining differential equations as the axioms is based on Mitchell.
I do not know of  a reference for the analogous treatment of the exponential function, and (re-)invented this for myself (along with most of the more elementary theorems).



%%%%
%%%%
%%%%
%%%%
\section{AN OVERVIEW OF THE THEORY}
In this section, we give the formal definitions of the HOL constants with which the theory deals and discuss the theorems that we will prove about them.
To keep our use of the {\Product} document preparation system simple, we simply identify the theorems by name and refer the reader to the theory listing in section~\ref{TheoryListing} on page~\pageref{TheoryListing} for the formal statements of the theorems.
There is an index to the formal definitions and the theory listing in section~\ref{INDEX} on page~\pageref{INDEX}.

This document is a {\Product} literate script. It contains all the metalanguage (ML) commands required to create a {\ProductHOL} theory (called ``analysis''), populate it with the formal definitions and prove and record all the theorems.
The proof commands are suppressed from the printed form of the document.
%The proof commands are given in section~\ref{THEOREMS} which begins on %page~\pageref{THEOREMS} and continues to the end of the document on page~\pageref{END}.
ML proof scripts are not particularly informative even to the expert eye, except when they are brought alive by replaying them interactively.

In sections~\ref{Polynomials} to~\ref{Integration} below, the various notions with which we are concerned are specified.
These sections also discuss the theorems proved.
Theorems are referenced by the names under which they are saved in the theory and an index is provided to help you find the theorems in the theory listing.

There are several ways of motivating this material and my preference is for a topological or geometric approach.
From that point of view, almost all of 
sections ~\ref{Polynomials} to~\ref{ConvergenceOfPowerSeries} can be viewed as leading towards the results on the transcendental functions in section~\ref{SomeSpecialFunctions} below.

Section~\ref{LHopital} presents l'H\^{o}pital's rule and was motivated by the need to calculate the limits that appear in the theory of the Laplace transform.
It is in any case pleasant to have the standard results about the asymptotic behaviour of $\ExpName$ and $\LogName$.

Section~\ref{Integration} presents the theory of integration following the Henstock-Kurzweil approach.
Again this was motivated by a desire to work with transforms (for which the Henstock-Kurzweil gauge integral is particularly well-suited since it gives a uniform definition for integration over both bounded and unbounded intervals).
As an application a notion of area for plane sets is defined and the areas of rectangles and circles are calculated.

The material is presented below in a bottom-up order in sections~\ref{Polynomials} to~\ref{Integration} below. 

\subsection{Technical Prelude}

First of all, we must give the the ML commands to  introduce the new theory ``analysis'' as a child of the theory ℝ of real numbers.
The parents of the theory are the theory ℝ of real numbers and the theory ``fin\_set'' which introduces the notion of finiteness (used here in the definition of compactness and in proofs about compact sets). We set up a proof context (which defines parameters to most of the proof infrastructure) by merging together:
``basic\_hol1'' for assistance with the predicate calculus, natural numbers, ordered pairs, lists etc.;
``sets\_alg''  for sets;
and ``'ℝ'' for real numbers.
The resulting proof context will automatically prove trivialities such as
=INLINEFT
Hd [1/2; 1/3] ∈ {x | x^2 < ℕℝ 1}
=TEX
, and will generally carry out useful simplifications to most problems expressed using this sort of vocabulary.
(Here `%
=INLINEFT
[1/2; 1/3]
=TEX
' is the {\ProductHOL} syntax for writing the list whose elements are $1/2$ and $1/3$ and
$Hd$ is the operator that takes the head element of a list, so that the membership assertion reduces to the true inequality $1/4 < 1$).

=IGN
open_theory "analysis" ;
=SML
force_delete_theory"analysis" handle Fail _ => ();
open_theory"ℝ";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℝ"];
new_theory"analysis";
new_parent"fin_set";
=TEX
%%%%
%%%%
%%%%
%%%%

\subsection{Polynomials}\label{Polynomials}
We define the polynomial functions on the real numbers to be the smallest set of functions containing the constant functions and the identity function and closed under (point-wise) addition and multiplication.

Here and throughout this document, we use the {\Product} Z-like notation for introducing new HOL constants.
In this notation, one gives type ascriptions for the constant or constants being defined (in this case {\it PolyFunc} which is a set of real functions of a real variable) and then a predicate giving their defining property (in this case an equation giving the value of the constant).
This maps onto a call of the primitive definitional principle {\it const\_spec}.
This principle requires an existence proof for the constants being introduced.
The {\ProductHOL} infrastructure includes a range of procedures for discharging the existence proofs and these will automatically discharge the proof obligations for most of the definitions in this document

If the existence proof cannot be discharged automatically, the actual defining property used in the call to {\it const\_spec} is a property that can trivially be proved consistent and that is logically equivalent to the desired defining property if that is consistent.
The existence proof can then be conducted under manual control at a later stage.
This has been done for all the constants in this document which are not handled automatically.
Indeed, the proof of consistency of the definitions of the transcendental functions and $\pi$ in section~\ref{SomeSpecialFunctions} below can be viewed as the {\it raison d'\^{e}tre} for the development of the differential calculus and for the theory of power series.

%%%%
%%%%
%%%%
%%%%
ⓈHOLCONST
│ ⦏PolyFunc⦎ : (ℝ → ℝ) SET
├──────
│ PolyFunc = ⋂
│	{	A
│	|	(∀c⦁ (λx⦁c) ∈ A)
│	∧	(λx⦁x) ∈ A
│	∧	(∀f g⦁f ∈ A ∧ g ∈ A ⇒ (λx⦁f x + g x) ∈ A)
│	∧	(∀f g⦁f ∈ A ∧ g ∈ A ⇒ (λx⦁f x * g x) ∈ A) }
■
We will show that every polynomial function can be represented as a (point-wise) sum, $\lambda x \bullet a_0 + a_1x + a_2 x^2 + \ldots a_n x^n$, for some list of coefficients $[a_0; a_1; a_2 \ldots; a_n]$.
The following function maps such a list of coefficients into the polynomial function it represents.
ⓈHOLCONST
│ ⦏PolyEval⦎ : ℝ LIST → (ℝ → ℝ)
├──────
│ 	(∀x⦁ PolyEval [] x = ℕℝ 0)
│∧	(∀c l x⦁ PolyEval (Cons c l) x = c + x * PolyEval l x)
■
We now define the operations on lists of coefficients that correspond to addition of polynomials \ldots
ⓈHOLCONST
│ ⦏PlusCoeffs⦎ : ℝ LIST → ℝ LIST → ℝ LIST
├──────
│ 	(∀l⦁ PlusCoeffs [] l = l)
│∧	(∀l⦁ PlusCoeffs l [] = l)
│∧	(∀c1 l1 c2 l2⦁
│	PlusCoeffs (Cons c1 l1) (Cons c2 l2) =
│	Cons (c1 + c2) (PlusCoeffs l1 l2))
■
\ldots and to multiplication of one polynomial by another.
ⓈHOLCONST
│ ⦏TimesCoeffs⦎ : ℝ LIST → ℝ LIST → ℝ LIST
├──────
│ 	(∀l⦁ TimesCoeffs [] l = [])
│∧	(∀c l1 l2⦁
│	TimesCoeffs (Cons c l1) l2 =
│	PlusCoeffs (Cons (ℕℝ 0) (TimesCoeffs l1 l2)) (Map (λx⦁c * x) l2) )
■
=TEX
The following is useful in forming a polynomial whose list of coefficients is given by a function:
%%%%
%%%%
=SML
declare_infix(310, "To");
ⓈHOLCONST
│ $⦏To⦎ : (ℕ → 'a) → ℕ → 'a LIST
├──────
│ 	(∀f⦁ f To 0 = [])
│∧	(∀f n⦁ f To (n+1) = f To n @ [f n])
■

After one or two technicalities, the main results on polynomials begins with a pattern which will appear often.
We are interested in showing that every polynomial function has a certain property, in this case the property of  being represented by a list of coefficients.
To prove this we investigate how the constant functions, the identity function, the pointwise sum of two functions and the pointwise product of two functions respect the property.
In this case, they either enjoy the property or preserve it as appropriate and the resulting theorems,
=INLINEFT
const_eval_thm
=TEX
,
=INLINEFT
id_eval_thm
=TEX
,
=INLINEFT
plus_eval_thm
=TEX
\ and
=INLINEFT
times_eval_thm
=TEX
\ record these facts.
These together with a principle of induction over the set of polynomial functions show that any polynomial function may be represented by a sequence of coefficients.

We continue to record a few more technicalities and then to prove
=INLINEFT
comp_poly_thm
=TEX
, which asserts that the functional composition of two polynomial functions is again a polynomial function.

The remaining theorems about polynomials build up to a proof that a polynomial function that is not identically zero has only finitely many roots (%
=INLINEFT
poly_roots_finite_thm
=TEX
).
This is proved using the special case of polynomial division in which the divisor is linear (which has the consequences familiarly known as the factor and remainder theorems).
ⓈHOLCONST
│ ⦏Roots⦎ : ('a → ℝ) → 'a SET
├──────
│ ∀f⦁ Roots f = {x | f x = 0.}
■

{\it En route} we get useful facts about the interaction of polynomial evaluation with list operations and also a formula for the difference of two like powers which will turn out, fortuitously, to be just what is needed to prove the convergence of geometric series much later on.

Development of algebraic theory is not a main concern at this stage so we stop at this theorem.
A later paper in this series of case studies will look at further results on roots, for example, Descartes' rule of signs.
The next step might be to develop the theory of  the degree of polynomials and of division, but that would probably be better done in general for polynomials over an arbitrary field.

Here is the complete list of the theorems discussed above.
The first two theorems result from a manually conducted proof of the consistency of the definition of
=INLINEFT
PlusCoeffs
=TEX
, which is not quite in the form that the infrastructure for automatic consistency proving can handle.
The first theorem states the consistency of the definition in the format expected by the {\Product} infrastructure.
We then adopt the convention of saving a theorem capturing the intended defining property, here 
=INLINEFT
plus_coeffs_def
=TEX
, which is derived automatically once the consistency proof has been done.

\ThmsIII{%
=GFT
PlusCoeffs_consistent
plus_coeffs_def
const_eval_thm
id_eval_thm
plus_eval_thm
const_times_eval_thm
times_eval_thm
poly_induction_thm
=TEX
}{%
=GFT
poly_func_eq_poly_eval_thm
const_poly_func_thm
id_poly_func_thm
plus_poly_func_thm
times_poly_func_thm
comp_poly_func_thm
poly_eval_append_thm
poly_eval_rev_thm
=TEX
}{%
=GFT
poly_diff_powers_thm
length_plus_coeffs_thm
poly_linear_div_thm
poly_remainder_thm
poly_factor_thm
poly_roots_finite_thm
=TEX
}

\subsection{Algebraic Results}\label{AlgebraicResults}

To deal with limits we will need a number of simple algebraic facts about the absolute value function, for example
=INLINEFT
ℝ_abs_plus_thm
=TEX
, which is the triangle inequality.
Also, for dealing with power series we need some elementary facts about the operator
=INLINEFT
x ^ m
=TEX
\ that raises a real number to a natural number power.
These facts  and miscellaneous others are collected together here with a view to moving them into the theory of reals (and, perhaps, augmenting the linear arithmetic decision procedure to deal with absolute values).
The names of the theorems are listed below:

\ThmsIII{%
=GFT
ℝ_0_≤_abs_thm
ℝ_abs_plus_thm
ℝ_abs_subtract_thm
ℝ_abs_plus_minus_thm
ℝ_abs_diff_bounded_thm
ℝ_abs_plus_bc_thm
ℝ_abs_abs_minus_thm
ℝ_abs_abs_thm
ℝ_abs_times_thm
ℝ_abs_ℝ_ℕ_exp_thm
ℝ_abs_eq_0_thm
ℝ_abs_≤_0_thm
ℝ_abs_0_thm
ℝ_abs_recip_thm
ℝ_abs_squared_thm
ℝ_abs_less_times_thm
=TEX
}{%
=GFT
ℝ_¬_0_abs_thm
ℝ_abs_≤_less_interval_thm
ℝ_less_recip_less_thm
ℝ_plus_recip_thm
ℕℝ_recip_thm
ℕℝ_0_less_recip_thm
ℕℝ_recip_not_eq_0_thm
ℝ_ℕ_exp_0_1_thm
ℝ_ℕ_exp_square_thm
ℝ_ℕ_exp_0_less_thm
ℝ_ℕ_exp_1_less_mono_thm
ℝ_ℕ_exp_1_less_mono_thm1
ℝ_≤_times_mono_thm
ℝ_ℕ_exp_¬_eq_0_thm
ℝ_ℕ_exp_plus_thm
ℝ_ℕ_exp_times_thm
=TEX
}{%
=GFT
ℝ_ℕ_exp_recip_thm
ℝ_ℕ_exp_recip_thm1
ℝ_ℕ_exp_1_≤_thm
ℝ_ℕ_exp_less_1_mono_thm
ℝ_ℕ_exp_less_mono_thm
ℝ_ℕ_exp_less_1_mono_thm1
ℝ_ℕ_exp_linear_estimate_thm
ℝ_0_≤_square_thm
ℝ_square_eq_0_thm
ℝ_bound_below_2_thm
ℝ_bound_below_3_thm
ℝ_max_2_thm
ℝ_max_3_thm
ℝ_min_2_thm
ℝ_min_3_thm
=TEX
}


\subsection{The Archimedean Property}\label{TheArchimedeanProperty}
It is a consequence of the completeness of the real numbers that they are an archimedean ordered ring:
given any $x, y > 0$ there is a natural number $m$ such that $y < mx$.
The following theorems capture this property and some consequences.
What we call the archimedean division theorem says that given $d > 0$ and $y \ge 0$, there is a natural number $q$ and a real number such that $y = qd + r$ and $0 \le r < d$.

\ThmsII{%
=GFT
ℝ_archimedean_thm
ℝ_archimedean_recip_thm
ℝ_archimedean_times_thm
=TEX
}{%
=GFT
ℝ_archimedean_division_thm
ℝ_ℕ_exp_tends_to_infinity_thm
ℝ_ℕ_exp_tends_to_0_thm
=TEX
}

\subsection{Limits of Sequences of Numbers}\label{LimitsOfSequencesOfNumbers}
%%%%
%%%%
%%%%
%%%%

We will write $s {-}{>} x$ to indicate that the sequence $s_n$, indexed by natural numbers, tends to the limit $x$ as $n$ tends to infinity.
We use real-valued functions on the natural numbers ℕ to represent such sequences.
The definition is completely standard:
%%%%
%%%%
=SML
declare_infix(200, "->");
ⓈHOLCONST
│ $⦏->⦎ : (ℕ → ℝ) → ℝ → BOOL
├──────
│∀s x⦁ s -> x ⇔ ∀e⦁ℕℝ 0 < e ⇒ ∃n⦁∀m⦁n ≤ m ⇒ Abs(s m - x) < e
■
%%%%
%%%%
%%%%
%%%%
The notions of closed and open intervals are used to make some of the results slightly more readable. The early part of the theory does not depend heavily on these notions.
Later on we will develop some elementary topological results.
The more interesting of these results, e.g., the Heine-Borel theorem depend on later definitions and results so they are collected together in section~\ref{SomeTopology} below (with one or two honourable exceptions in section~\ref{SomeClassicalTheorems} which are needed earlier on).

%%%%
%%%%
ⓈHOLCONST
│ ⦏ClosedInterval⦎ : ℝ → ℝ → ℝ SET
├──────
│ ∀x y⦁ ClosedInterval x y = {t | x ≤ t ∧ t ≤ y}
■
ⓈHOLCONST
│ ⦏OpenInterval⦎ : ℝ → ℝ → ℝ SET
├──────
│ ∀x y⦁ OpenInterval x y = {t | x < t ∧ t < y}
■

New sequences may be formed from old using the field operations.
If the original sequences converge then so do the new ones (providing we are careful to avoid dividing by zero).
The first few theorems on limits capture this observation and some consequences, e.g.,
=INLINEFT
poly_lim_seq_thm
=TEX
, which says that if $s_m$ is a sequence converging to a limit, $t$,
and $f(x)$ is a polynomial, then the sequence $f(s_m)$ converges to $f(t)$.

None of this theory would be very interesting if there were no convergent sequences, so we show that the sequence whose $m$-th term is $x + \frac{1}{m+1}$ converges to $x$ for any $x$.
This is
=INLINEFT
lim_seq_recip_ℕ_thm
=TEX
. 
Here we are using a very common and useful device to avoid talking about division by zero:
if $m$ is a natural number, then $m+1$ is a non-zero natural number and it is often easier just to state results about $m+1$ rather than have hypotheses of the form $0 < m$.

As it will turn out, sequences are very important in our approach to limiting processes generally, so we develop the necessary theory a little further here.
We show, for example,  in
=INLINEFT
lim_seq_¬_eq_thm
=TEX
\ that any real $x$ can be given as the limit of a sequence $s_m$ such that no $s_m = x$.
We also show, very importantly, in
=INLINEFT
lim_seq_unique_thm
=TEX
, that if a sequence converges to a limit then that limit is unique.
A similar uniqueness property will be derived for all of the limiting processes we investigate.

\ThmsIII{%
=GFT
const_lim_seq_thm
plus_lim_seq_thm
lim_seq_bounded_thm
times_lim_seq_thm
minus_lim_seq_thm
poly_lim_seq_thm
=TEX
}{%
=GFT
recip_lim_seq_thm
lim_seq_choice_thm
abs_lim_seq_thm
lim_seq_recip_ℕ_thm
lim_seq_¬_eq_thm
lim_seq_shift_thm
=TEX
}{%
=GFT
lim_seq_¬_eq_thm1
lim_seq_¬_0_thm
lim_seq_upper_bound_thm
lim_seq_unique_thm
lim_seq_diffs_tend_to_0_thm
=TEX
}

\subsection{Continuity}\label{Continuity}
%%%%
%%%%
%%%%
%%%%
Now we give the usual $\epsilon$-$\delta$ definition for continuity of a function, $f$ at a point $x$. Both kinds of $\epsilon$ are tied up in the {\ProductHOL} library for something else (viz. Hilbert's choice
operator and set-membership).
We therefore just use $e$ and $d$.
Continuity is formulated as an infix relation between a function and the point at which its continuity is asserted.
%%%%
%%%%
=SML
declare_infix(200, "Cts");
ⓈHOLCONST
│ $⦏Cts⦎ : (ℝ → ℝ) → ℝ → BOOL
├──────
│ ∀f x⦁	f Cts x
│ ⇔	∀e⦁ℕℝ 0 < e ⇒ ∃d⦁ℕℝ 0 < d ∧ ∀y⦁ Abs(y - x) < d ⇒ Abs(f y - f x) < e
■

As observed in \cite{Harrison96}, several notions of limit arise and it is desirable to have common ways of dealing with them. 
Harrison's approach is via the general notion of convergence nets. 
We choose the more homely notion of sequential convergence as our way around this problem.

As we shall state and prove later,  to say that $f$ is continuous at $x$ is to say that $f(y)$ tends to $f(x)$ as $y$ tends to $x$.
As the first of our theorems,
=INLINEFT
cts_lim_seq_thm
=TEX
, shows, this holds iff. for any sequence $s_m$ whose limit is $x$, we have that the sequence $f(s_m)$ tends to $f(x)$.


This approach makes the proofs of the continuity of functions formed from continuous functions
by functional composition and by applying field-operations trivial applications of analogous results on sequences.
I have not seen this useful observation made in any elementary textbook on the subject, the reasons, I suspect, being two-fold:
{\em(i)} proving these results about continuity from the definitions is considered to be a good exercise
for the student,
and, {\em(ii)},
the analogue of this approach does not work in an arbitrary topological space (although spaces in which it fails are fairly exotic).
Nonetheless, it works very well for us here, so well, in fact, that we spend the time to prove a couple of variants of the result on continuity and limits of sequences which let us restrict attention to sequences which are confined to a given neighbourhood of the point at which continuity is asserted and which avoid that point.
This immediately shows that continuity is a local property:
if two functions, $f$ and $g$, agree in some open interval containing $x$ and $g$ is continuous at $x$, then so is $f$.

At this point in the proof script, we introduce a few simple proof procedures to help with applying the results on the continuity of algebraic combinations of continuous functions.
In practice, we will want to prove that specific combinations are continuous, e.g., $1 + 2f(x)$, given the continuity of $f$.
However, it requires (a very special case of) higher-order matching to apply the theorems to the function $\lambda x \bullet 1 +2f(x)$.
The proof procedures comprise:
{\em (a)}
a conversion to help put in the necessary $\beta$-redexes, e.g., to rewrite $\lambda x \bullet 1 +2f(x)$ as $\lambda x \bullet (\lambda x \bullet 1)(x) + (\lambda x \bullet 2f(x))(x)$ so that it matches the statement of
=INLINEFT
plus_cts_thm
=TEX
; and, {\em(b)},
a tactic,
=INLINEFT
simple_cts_tac
=TEX
, which selects the right theorem to apply and uses the conversion to apply it.

This heuristic for automatically proving continuity is very useful, but the implementation is very simple-minded (for example, it does not allow the user to extend the range of functions supported).
Later on, we will give a more sophisticated analogue for calculating derivatives.
We choose to defer a more sophisticated approach to automatic continuity proving to separate work on topology, since in any case, the particular functions we are interested in in this document turn out to be continuous by dint of being differentiable.

Once the basic facts about continuity of algebraic combinations of continuous functions are in place, we prove a few theorems for later use, for example, in reasoning about compact sets.
Compact sets are defined in terms of open coverings and so it is useful to have the characterisation of continuity in terms of open sets.
Following our approach of taking sequential convergence as basic, we first characterise sequential convergence in terms of open sets and then use that characterisation to derive one for continuity.

Next we prove a uniqueness property for continuity:
namely, that if $f$ is continuous at $x$, then $f(x)$ is uniquely determined by the values $f(y)$ where $y \not= x$ ranges over any given neigbourhood of $x$.
To do this, we first show that continuity of $f$ at $x$ implies a principle for estimating $f(x)$ (%
=INLINEFT
cts_estimate_thm
=TEX
) and as a consequence a principle for showing that $f(x) = 0$ (%
=INLINEFT
cts_estimate_0_thm
=TEX
).
This latter principle applied to the difference of two functions $f$ and $g$ which are continuous and agree in some neighbourhood of $x$, except perhaps at $x$, shows that two such functions must agree at $x$, which is the uniqueness principle we want.

The final result in this section on continuity states that a function which is both continuous in the sense of Darboux (i.e., it satisfies the conclusion of the intermediate value theorem) and monotonic increasing is continuous in the usual sense.
This is preceded by a result which reduces the number of cases that need to be considered in proving the result on Darboux continuity:
it says that if $f(x)$ lies in the open interval $(a, b)$, then when you test $f$ for continuity at $x$ using open intervals, you can assume the end-points of the ``challenge'' interval, $(c, d)$ are both contained in $(a, b)$.
The result on Darboux continuity will be used to show that the natural logarithm function is continuous.

\ThmsIII{%
=GFT
cts_lim_seq_thm
cts_lim_seq_thm1
cts_lim_seq_thm2
cts_local_thm
const_cts_thm
id_cts_thm
plus_cts_thm
times_cts_thm
poly_cts_thm
ℝ_ℕ_exp_cts_thm
=TEX
}{%
=GFT
comp_cts_thm
minus_cts_thm
minus_comp_cts_thm
recip_cts_thm
recip_comp_cts_thm
ℝ_ℕ_exp_comp_cts_thm
abs_cts_thm
abs_comp_cts_thm
cts_extension_thm1
cts_extension_thm
=TEX
}{%
=GFT
open_ℝ_delta_thm
lim_seq_open_ℝ_thm
cts_open_ℝ_thm
closed_interval_closed_thm
cts_estimate_thm
cts_estimate_0_thm
cts_limit_unique_thm
cts_open_interval_thm
darboux_cts_mono_thm
darboux_cts_mono_thm1
=TEX
}
\subsection{Derivatives}\label{Derivatives}

%%%%
%%%%
%%%%
%%%%
We now turn to derivatives and give the standard $\epsilon$-$\delta$ definition for the derivative of a function, $f$ at a point $x$. 
The notion of a derivative as formulated here is really a ternary relation:
``$f$ has derivative $c$ at $x$''.
We represent this as the infix operation between $f$ and $c$ whose value is the propositional function that characterises the values $x$ for which the derivative $f$ is $c$.
%%%%
%%%%
=SML
declare_infix(200, "Deriv");
ⓈHOLCONST
│ $⦏Deriv⦎ : (ℝ → ℝ) → ℝ → ℝ → BOOL
├──────
│ ∀f c x⦁
│	(f Deriv c) x ⇔
│	∀e⦁ℕℝ 0 < e ⇒ ∃d⦁
│		ℕℝ 0 < d
│	∧	∀y⦁ Abs(y - x) < d ∧ ¬y = x ⇒ Abs((f y - f x)/(y-x) - c) < e
■


As usual, we will investigate the interaction of the field operations and functional composition with derivatives and use the results to say something about derivatives of polynomials.
In order to state the result about polynomials, we need the following definition, which gives the operation on lists of coefficients that corresponds to taking the derivative of a a polynomial function.
ⓈHOLCONST
│ ⦏DerivCoeffs⦎ : ℝ LIST → ℝ LIST
├──────
│ 	DerivCoeffs [] = []
│∧	(∀c l⦁ DerivCoeffs (Cons c l) = PlusCoeffs l (Cons (ℕℝ 0) (DerivCoeffs l)))
■

Following Harrison, we make much use of Carath\'{e}odory's characterisation of the derivative in terms of the existence of a continuous function satisfying certain conditions.
This turns all the statements about derivatives into statements about continuity which are easy to prove once the necessary witnesses are supplied.

After the results about derivatives of algebraic combinations of functions and polynomials, we show that the derivative is a local property and that the derivative is unique.
For later use, we also provide the characterisation of derivatives in terms of limits of function values.

These results are followed in the proof script by the coding of an inference rule, and a corresponding tactic that automatically calculate derivatives of algebraic combinations of functions whose derivatives are known.
Unlike the tactic for continuity, these automatic proof procedures are fairly general ---
they are parameterised by a list of theorems giving facts about the derivatives.
The algorithm used is intended to be a little more general than the one described by Harrison; in particular, the algorithm is formulated so that the chain rule can be presented as one of the theorems rather than being wired in. 

\ThmsIII{%
=GFT
caratheodory_deriv_thm
deriv_cts_thm
const_deriv_thm
id_deriv_thm
plus_deriv_thm
plus_const_deriv_thm
=TEX
}{%
=GFT
times_deriv_thm
times_const_deriv_thm
comp_deriv_thm
minus_deriv_thm
minus_comp_deriv_thm
ℝ_ℕ_exp_deriv_thm
=TEX
}{%
=GFT
recip_deriv_thm
recip_comp_deriv_thm
poly_deriv_thm
deriv_local_thm
deriv_lim_fun_thm
deriv_unique_thm
=TEX
}

Note: the statement of {\em deriv\_lim\_fun\_thm} uses the notion of the limit of a function value introduced in section~\ref{LimitsOfFunctionValues} below.

\subsection{Some Classical Theorems}\label{SomeClassicalTheorems}
%%%%
%%%%
%%%%
%%%%
We proceed to prove our selection of the classical miscellany of extremely fruitful facts about continuous and differentiable functions.
The selection was motivated both bottom-up, by picking results for their intrinsic interest, and top-down, by picking results that will be needed later.
One might expect to find l'H\^{o}pital's rule in this section, but to state it properly requires some additional notions that we prefer to define later, see section~\ref{LHopital}.

The notions of open, closed and compact sets are useful in stating some of these results.
%%%%
%%%%
ⓈHOLCONST
│ ⦏Open⋎R⦎ : ℝ SET SET
├──────
│ Open⋎R = {A | ∀t⦁t ∈ A ⇒ ∃x y⦁t ∈ OpenInterval x y ∧ OpenInterval x y ⊆ A}
■
[Note that
=INLINEFT
~
=TEX
\ below is not arithmetic negation, but the operation of complementing a set with respect to the universe of its type.]
ⓈHOLCONST
│ ⦏Closed⋎R⦎ : ℝ SET SET
├──────
│ Closed⋎R = {A | ~ A ∈ Open⋎R}
■
ⓈHOLCONST
│ ⦏Compact⋎R⦎ : ℝ SET SET
├──────
│ Compact⋎R =
│ {A | ∀ V⦁ V ⊆ Open⋎R ∧ A ⊆ ⋃V ⇒ ∃W⦁ W ⊆ V ∧ W ∈ Finite ∧ A ⊆ ⋃ W}
■

The first of our collection of ``classical'' theorems, which we call the ``curtain induction'' principle, is actually one that I have never seen stated before! However, it is very useful in proving Bolzano's principle of bisection and proving that (bounded) closed intervals are compact.
It says that if a property $P$ is such that $P(x)$ entails $P(y)$ for every $y < x$ and if for any $x$, there is a $y < x$ such that $P(y)$ entails $P(z)$ for some $z > x$, then if $P$ holds anywhere it holds everywhere.
One thinks of sliding a curtain from left to right across the real line starting at the given point where $P$ is known to hold. 
This captures the essence of one kind of supremum argument in a fairly neat way.

In general, when dealt with fully formally, reasoning about suprema is more slippery than one might think --- a problem that is slightly exacerbated by some small infelicities in the quantifier structure of some of the theorems about suprema in the theory ℝ.
We therefore do very little direct reasoning about suprema in the proofs.
The problems with the statements about suprema in the theory ℝ are purely technical and could be remedied (they just sometimes fail to work nicely with some of the standard proof procedures).
However, the alternative approaches adopted here work so much better that I have felt little pressure to fix them.

With the curtain induction principle and one or two other lemmas, e.g., that the union of a finite chain of sets is actually a member of the chain, we can then reel off the fairly standard proofs of
Bolzano's bisection principle,
the fact that continuous functions are bounded and attain their maximum values in closed intervals (more generally in compact sets),
the intermediate value theorem,
the mean value theorem etc.

The mean value theorem appears here in three guises.
{\em cauchy\_mean\_value\_thm} is the general statement about two functions $f$ and $g$ continuous in a closed interval $[a, b]$ and differentiable on the open interval $(a, b)$ that Cauchy proved as his mean value theorem.
This is the result we need later to prove l'H\^{o}pital's rule.
{\em mean\_value\_thm} is the usual statement about a single
function $f$ satisfying the same conditions as in {\em cauchy\_mean\_value\_thm}.
Finally {\em mean\_value\_thm1} is the weaker variant
where $f$ is required to be differentiable on $[a, b]$ which is often useful in practice (because that is the hypothesis one has to hand).
In each of these mean value theorems, our statement of the theorem is what is obtained from the traditional statement by cross-multiplying to eliminate division in favour of multiplication.
This is convenient in practice and brings out a symmetry in {\em cauchy\_mean\_value\_thm} (which is actually slightly more general as a result).

By contrast with Harrison's approach, later on, when we need explicit numerical estimates, for example, in demonstrating the existence of $\pi$, we tend to use theorems like the mean value theorem, rather than obtaining numerical estimates from power series.
{\em deriv\_linear\_estimate\_thm} is an example of this kind of estimation.


\ThmsIII{%
=GFT
curtain_induction_thm
bisection_thm
closed_interval_compact_thm
finite_chain_thm
cts_compact_maximum_thm
cts_maximum_thm
cts_abs_bounded_thm
=TEX
}{%
=GFT
intermediate_value_thm
local_min_thm
local_max_thm
rolle_thm
cauchy_mean_value_thm
mean_value_thm
=TEX
}{%
=GFT
mean_value_thm1
deriv_0_thm1
deriv_0_thm
deriv_0_thm2
deriv_0_less_thm
deriv_linear_estimate_thm
=TEX
}

\subsection{Excursus: Cantor's Theorem}\label{ExcursusCantorsTheorem}
The next block of theorems is an excursion.
We prove Cantor's theorem that the reals are uncountable.
The proof is via nested intervals (and generalises to show that any perfect set in a metric space is uncountable; see Rudin \cite{Rudin76}).
This material does feed in, in spirit, if not in actual use of the theorems, to the theory of Cauchy sequences.

\ThmsII{%
=GFT
ℝ_mono_inc_seq_thm
ℝ_mono_dec_seq_thm
nested_interval_bounds_thm
=TEX
}{%
=GFT
nested_interval_diag_thm
nested_interval_intersection_thm
ℝ_uncountable_thm
=TEX
}

\subsection{Some Topology}\label{SomeTopology}

In this section we show that the set of open and closed sets as we have defined them do indeed satisfy the rules for the open and closed sets of a a topological space.
We then provide a selection of additional examples of open and closed sets.
More interestingly, we prove that compact sets are closed and contain their maximum and minimum elements (if they are non-empty).
The empty set is compact, but the whole real line is not.
Closed subsets of compact sets are compact.
A set is compact iff. it is closed and bounded (the Heine-Borel theorem).
Finally, ℝ is topologically connected, i.e., it cannot be represented as the union of two disjoint open sets.

\ThmsII{%
=GFT
∩_open_interval_thm
∩_closed_interval_thm
⋃_open_ℝ_thm
∪_open_ℝ_thm
∩_open_ℝ_thm
⋂_closed_ℝ_thm
∩_closed_ℝ_thm
∪_closed_ℝ_thm
open_interval_open_thm
complement_open_interval_thm
=TEX
}{%
=GFT
complement_closed_interval_thm
half_infinite_intervals_open_thm
half_infinite_intervals_closed_thm
empty_universe_open_closed_thm
compact_closed_thm
compact_min_max_thm 
closed_⊆_compact_thm
empty_universe_compact_thm
heine_borel_thm
ℝ_connected_thm
=TEX
}

\subsection{Cauchy Sequences}\label{CauchySequences}

Up to this point, we have generally only been able to show that particular sequences converge when a formula for the limit is known. In this section we prove that a sequence is convergent iff. it is a Cauchy sequence.
The argument is the standard one:
that a convergent sequence is necessarily a Cauchy sequence is a straightforward consequence of the definition of the limit of a sequence;
conversely, a Cauchy sequence is bounded and hence has a $\LimSup$ and a $\LimInf$, and by the Cauchy property, these two must be equal, and their common value is the limit of the sequence.
Rather than define the notions of $\LimSup$ and $\LimInf$ as constants in the theory, we simply give theorems that assert the existence of these values.

{\em En passant}, we prove one or two useful results about monotonic increasing and decreasing sequences.

\ThmsIII{%
=GFT
lim_seq_cauchy_seq_thm
fin_seq_bounded_thm
cauchy_seq_bounded_above_thm
cauchy_seq_bounded_below_thm
=TEX
}{%
=GFT
lim_seq_mono_inc_sup_thm
lim_seq_mono_inc_thm
lim_seq_mono_dec_thm
lim_sup_thm
=TEX
}{%
=GFT
lim_inf_thm
cauchy_seq_lim_seq_thm
lim_seq_⇔_cauchy_seq_thm
=TEX
}

\subsection{Limits of Function Values}\label{LimitsOfFunctionValues}
We will write $(f {-}{-}{>} c)x$ to indicate that $f(t)$ tends to the limit $c$ as $t$ tends to $x$:
%%%%
%%%%
=SML
declare_infix(205, "-->");
ⓈHOLCONST
│ $⦏-->⦎ : (ℝ → ℝ) → ℝ → ℝ → BOOL
├──────
│∀f c x⦁
│	(f --> c) x
│ ⇔	∀e⦁ℕℝ 0 < e
│	⇒	∃d⦁ℕℝ 0 < d ∧ ∀y⦁ Abs(y - x) < d ∧ ¬y = x ⇒ Abs(f y - c) < e
■

As usual, we prove the standard facts about the interaction between limits of function values and the field operations.
These are all proved using a characterisation of the function value notion of limit in terms of limits of sequences.
We then show that limits of function values are unique if they exist and give two results about limits of function values and functional composition:
the first of these is the obvious one: if $f$ tends to $t$ at $x$ and $g$ is continuous at $t$, then $\lambda x \bullet g(f x)$ tends to $g(t)$ at $x$;
the second is less obvious: if $f$ is continuous at $x$ and one-to-one on some open interval containing $x$, and if $g$ tends to $t$ at $f(x)$, then $\lambda x \bullet g(f x)$ tends to $t$ at $x$.
I have not seen the latter result in the textbooks, but it seems to be needed to show that  if $g$ is right-inverse to $f$ in some open interval $(a, b)$ and if $f$ has derivative $c \not= 0$ at $g(x)$ for $x$ in $(a, b)$, then $g$ has derivative $\frac{1}{c}$ at $x$.
This is needed later to calculate the derivative of the natural logarithm function.

\ThmsIII{%
=GFT
lim_fun_lim_seq_thm
const_lim_fun_thm
id_lim_fun_thm
plus_lim_fun_thm
times_lim_fun_thm
recip_lim_fun_thm
=TEX
}{%
=GFT
comp_lim_fun_thm
comp_lim_fun_thm1
poly_lim_fun_thm
lim_fun_upper_bound_thm
lim_fun_unique_thm
=TEX
}{%
=GFT
lim_fun_local_thm
deriv_lim_fun_thm1
comp_lim_fun_thm2
cts_lim_fun_thm
inverse_deriv_thm
=TEX
}

\subsection{Limits of Sequences of Functions}\label{LimitsOfSequencesOfFunctions}
We write $(u {-}{-}{-}{>} h) X$ to indicate that the sequence of functions $u_n$, indexed by natural numbers, tends uniformly to the limit function $h$ on the set $X$ as $n$ tends to infinity. 
%%%%
%%%%
=SML
declare_infix(205, "--->");
ⓈHOLCONST
│ $⦏--->⦎ : (ℕ → ℝ → ℝ) → (ℝ → ℝ) → ℝ SET → BOOL
├──────
│∀u h X⦁
│	(u ---> h) X
│ ⇔	∀e⦁ℕℝ 0 < e ⇒ ∃n⦁∀m y⦁ n ≤ m ∧ y ∈ X ⇒ Abs(u m y - h y) < e
■

We prove a small selection of results about algebraic combinations of uniform limits of sequences of functions, just covering constants, addition and multiplication
The proofs are done, essentially, by copy-and-paste reuse of the analogous results for sequences of values.
Note that we could have defined the notion of the limit of a sequence of values as a special case of a limit of a sequence of functions (namely as a limit of a sequence of constant functions).
However, it seems clearer not to do this (and some facts about sequences of values do not hold in general, e.g., if $f_n$ converges uniformly in $X$ as $n$ tends to $\infty$, $\frac{1}{f_n}$ is not uniformly convergent in general).

We then show that (uniformly) convergent sequences of functions are Cauchy sequences and, more interestingly, that sequences of functions that are uniformly Cauchy are uniformly convergent.
This is followed by our two big theorems on uniform convergence based on Rudin \cite{Rudin76}: the first of these is a version of Rudin's Theorem 7.11, which is an interchange theorem relating our three notions of limit.
More precisely, our formulation says that if $u_m$ converges uniformly to $f$ on some set of the form $(a, b) \backslash \{x\}$ for $x$ in the open interval $(a, b)$ and if for each $m$ $u_m(y)$ converges to $s_m$ as $y$ tends to $x$, then $f(y)$ converges to some limit $c$ as $y$ tends to $x$ and $s_m$ converges to that same value $c$ as $m$ tends to $\infty$.
Rudin states and proves this in greater generality, but we just do the case that is needed for the the second big theorem, namely Rudin's Theorem 7.17.

The second big theorem says, in essence, that under suitable conditions, the derivative of a limit of
a sequence of functions exists and may be calculated as the limit of the derivatives of the
functions in the sequence.
In our formulation, the theorem says that if, a sequence of functions $du_m$ converges uniformly to some function $df$ on an open interval $(a, b)$ and each $du_m$ is the derivative of some function $u_m$ throughout $(a, b)$, and if the sequence of values $u_m(x_0)$ is convergent for some $x_0$ in $(a, b)$, then the sequence of functions $u_m$ is uniformly convergent to a function $f$ in $(a, b)$ whose derivative is given by $df$ throughout $(a, b)$.
This is the key result that justifies ``differentiation under the summation sign'' for convergent power series.

Our formulation of the result on uniform convergence and derivatives differs from the standard one (as given in Rudin) in using open intervals rather than closed ones.
It is traditional to state results about uniform convergence for closed intervals, or more generally for compact sets.
Unfortunately, to get this to work requires some special treatment of the end-points of the interval (see Rudin's Definition 5.1 for the sort of things that go on).
We prefer to stick with the single notion of a two-sided derivative.
This does mean that some results might have to be stated as holding for all open intervals (or sets) contained in some closed interval (or compact set) rather than holding on the closed interval or compact set.
However, this has not arisen in practice, and there is no real loss of generality:
any function that is, say, differentiable, on a closed interval $[a, b]$ can be extended to a differentiable function on an open interval $(A, B)$ containing $[a, b]$ and our way of formulating the kind of results in question will then apply to $(A, B)$.

It is instructive to compare the formal treatment of these two big theorems with their treatment as in Rudin:
the formal versions make it much more evident that these results are pure existence theorems, with proofs that conjure up witnesses out of the air using the Cauchy condition and use uniqueness properties of limits to show that these witnesses satisfy the requirements.
The traditional mathematical notation, in contrast, gives an illusion of ``constructiveness'', as if notations like $\lim_{n \rightarrow \infty} f_n'(x)$ denoted things that exist {\em a priori}.

It is also noteworthy that these two theorems and the root test for convergence of power series allow one to develop the theory of the transcendental functions via power series without using integration.
As noted by Hanne Gottliebsen \cite{Gottliebsen01}, many text books bypass these theorems using results about integration to prove that power series can be differentiated term by term. As shown here, this is not necessary if you prove the more general results.

\ThmsII{%
=GFT
const_unif_lim_seq_thm
plus_unif_lim_seq_thm
bounded_unif_limit_thm
times_unif_lim_seq_thm
unif_lim_seq_bounded_thm
unif_lim_seq_⊆_thm
unif_lim_seq_shift_thm
unif_lim_seq_cts_thm
=TEX
}{%
=GFT
unif_lim_seq_cauchy_seq_thm
cauchy_seq_unif_lim_seq_thm
unif_lim_seq_pointwise_lim_seq_thm
unif_lim_seq_pointwise_unique_thm
unif_lim_seq_unique_thm
lim_fun_lim_seq_interchange_thm
unif_lim_seq_deriv_estimate_thm
unif_lim_seq_deriv_thm
=TEX
}

\subsection{Series and Power Series}\label{SeriesAndPowerSeries}
The {\em series} defined by a sequence of real terms is, to all intents and purposes, the sequence of partial sums of the sequence:
%%%%
%%%%
%%%%
%%%%
ⓈHOLCONST
│ ⦏Series⦎ : (ℕ → ℝ) → (ℕ → ℝ)
├──────
│	(∀s⦁ Series s 0 = ℕℝ 0)
│ ∧	(∀s n⦁ Series s (n+1) = Series s n + s n)
■
The {\em power series} defined by a sequence of real coefficients is, in a similar vein, the sequence of polynomial functions whose coefficients are given by leading subsequences of the sequence:
%%%%
%%%%
%%%%
%%%%
ⓈHOLCONST
│ ⦏PowerSeries⦎ : (ℕ → ℝ) → (ℕ → ℝ → ℝ)
├──────
│ ∀s n⦁ PowerSeries s n = PolyEval (s To n)
■
\subsubsection{Elementary Properties}\label{PowerSeriesElementaryProperties}
We first prove a few elementary properties of series and power series.

\ThmsIII{%
=GFT
power_series_series_thm
series_power_series_thm
power_series_0_arg_thm
series_power_limit_0_thm
plus_series_thm
=TEX
}{%
=GFT
series_0_thm
const_times_series_thm
lim_seq_ℕℝ_recip_eq_0_thm
lim_seq_ℝ_ℕ_exp_eq_0_thm
series_shift_thm
=TEX
}{%
=GFT
lim_series_shift_thm
lim_series_shift_∃_thm
lim_series_bounded_thm
=TEX
}

\subsubsection{Geometric Series}\label{PowerSeriesGeometricSeries}
We next show that the geometric series $\Sigma x^n$ has radius of convergence $1$, using the result on the polynomial $x^n - y^n$ previously proved (as {\em poly\_diff\_powers\_thm}) to give the explicit formula for the limit.

\ThmsII{%
=GFT
geometric_sum_thm
geometric_series_thm
=TEX
}{%
=GFT
geometric_series_series_thm
geometric_series_thm1
=TEX
}

\subsubsection{Convergence Tests}\label{PowerSeriesConvergenceTests}
We now give the standard convergence tests for series and power series.
The first two results are a good example of a case where our {\em idiot savant} has no need of spoon feeding:
the Weierstrass test for uniform convergence of the sum of a series of functions has the comparison test for convergence of series of values as an immediate corollary of the special case when the functions are constant.
There is no point in presenting the comparison test first (as is invariably done in the text books).

Our formulation of the root test for the convergence of a series is somewhat non-standard.
This test is usually couched in terms of $\LimSup\sqrt[n]{\Abs{s_n}}$, but we have chosen not to introduce the theory of $n$-th roots at this point in the development, nor to define a constant for the notion of {\em limes superior}.
However, the usual proof of the root test immediately derives from the usual statement the fact that a series for which  $\LimSup\sqrt[n]{\Abs{s_n}}$, exists and is less than $1$ is majorised in absolute value by a convergent geometric series.
We just make that our condition:
this appears to be entirely equivalent to the standard definition (and states the result in terms of what you generally have to prove to show the $\LimSup$ in question exists as required).
With this formulation, the test will actually work up to a multiplicative constant, which can sometimes ease the burden of proof (see the statement of {\em root\_test\_thm}).

We then give the ratio test, firstly  in its most general form which says that a series $s_n$ of non-zero terms will converge if the ratios $\Abs{\frac{s_{n+1}}{s_n}}$ are bounded above by some $b < 1$ for all large enough $n$. 
We then give the more commonly stated form which requires these ratios to converge to a limit less than $1$, which is strictly less general, but useful if you have to hand facts about the limits in question.

\ThmsII{%
=GFT
weierstrass_test_thm
comparison_test_thm
simple_root_test_thm
=TEX
}{%
=GFT
root_test_thm
ratio_test_thm1
ratio_test_thm
=TEX
}

\subsubsection{Convergence of Power Series}\label{ConvergenceOfPowerSeries}
We now give the main result on convergent power series which says that if a power series $\Sigma c_n x^n$ converges pointwise in absolute value for $x = B$ for some positive $B$, then for any positive $b < B$, the power series converges (viewed as a sequence of functions) uniformly for $x$ in the open interval $(-b, b)$ and is differentiable on that interval with a derivative given as the limit of the result of differentiating the power series term by term (the existence of this limit and the uniform convergence to it being part of the conclusion of the theorem).

After a few lemmas which break out some important steps on the main result, we present the main result in several guises, including a corollary about second derivatives that will be useful for the sine and cosine functions.

\ThmsII{%
=GFT
power_series_convergence_thm
power_series_deriv_coeffs_thm
power_series_deriv_lemma1
power_series_deriv_lemma2
power_series_scale_arg_thm
power_series_scale_coeffs_thm
=TEX
}{%
=GFT
power_series_deriv_lim_seq_convergence_thm
power_series_deriv_convergence_thm
power_series_main_thm
power_series_main_thm1
power_series_main_thm2
power_series_main_thm3
=TEX
}


\subsection{Some Special Functions}\label{SomeSpecialFunctions}
%%%%
%%%%
%%%%
%%%%
In this section, we define the transcendental functions,
$\ExpName$,
$\LogName$,
$\SinName$ and
$\CosName$.
For geometric applications, it seems most natural to specify $\ExpName$, $\SinName$ and $\CosName$ by differential equations.
We will use power series to provide witnesses to the consistency of these specifications (i.e., to provide solutions to the differential equations).
We will then rely on the differential equations to derive the main properties of the functions (including the fact that $\ExpName$ is one-to-one, which justifies a specification of $\LogName$ as its left inverse).
 

Before defining the transcendental functions, we introduce the factorial function, which we will need to give the terms of the power series that provide the witnesses . 
We make this a postfix operator with precedence higher than all the binary arithmetic operators.
%%%%
%%%%
=SML
declare_postfix(330, "!");
ⓈHOLCONST
│ 	⦏$!⦎ : ℕ → ℕ
├──────
│	0 ! = 1
│ ∧	(∀m⦁(m+1)! = (m+1)*m!)
■

Using the factorial function, we can state Taylor's theorem.
While this theorem is not used in our approach to the transcendental functions, it is proved here for completeness, using one or two lemmas about the factorial function and a generalisation to $n$-th derivatives of Rolle's theorem.

\ThmsIII{%
=GFT
factorial_linear_estimate_thm
factorial_0_less_thm
=TEX
}{%
=GFT
factorial_times_recip_thm
gen_rolle_thm
=TEX
}{%
=GFT
taylor_thm
=TEX
}

=GFT
=TEX
\subsubsection{The Exponential Function}\label{TheExponentialFunction}

As promised, we define the exponential function by a differential equation with an initial condition.
%%%%
%%%%
ⓈHOLCONST
│ 	⦏Exp⦎ : ℝ → ℝ
├──────
│	Exp (ℕℝ 0) = ℕℝ 1
│ ∧	(∀x⦁ (Exp Deriv Exp x) x)
■

The first block of theorems lead up to the consistency of the above definition using the usual power series to provide the witness.
Then we give a uniqueness property for the exponential function and develop its usual algebraic properties
(viz., that $\ExpName$ is a strictly order-preserving homomorphism from the group of all real numbers under addition to the group of positive real numbers under multiplication).

We develop the properties of $\ExpName$ using an ``axiomatic'' approach along the lines of that given by Mitchell \cite{Mitchell69} for the sine and cosine functions.
I am grateful to John Harrison for pointing out a considerable simplification to an earlier version of this argument.

Assume we have a function $e$ satisfying the differential equations and initial conditions specified for $\ExpName$.
I.e., $e(0) = 1$, $e$ is everywhere differentiable, and the derivative $e'(x)$ is equal to $e(x)$ for all x.
For arbitrary $y$, put  $q_y(x) = e(x+y) \times e(-x)$, then $q_y$ is everywhere differentiable with $q_y'(x) = 0$ and so $q_y$ is constant. 
Since $q_y(0) = e(y)$, we must have $e(x+y) \times e(-x) = e(y)$ for all $x$ and $y$.
Putting $y=0$, this gives that $e(x) \not= 0$ with
$e(x)^{-1}=e(-x)$ for all $x$.
So $e(x+y) = e(x) \times q_y(x) = e(x)\times e(y)$ for all $x$ and $y$.
Since $e(0)$ is positive and $e(x) \not= 0$ for any $x$, by the intermediate value theorem, $e(x)$ is always positive.

The above shows that $\ExpName$ is indeed a homomorphism from the group of all real numbers under addition to the group of real numbers under multiplication.
That this homomorphism is order-preserving follows from
{\em deriv\_0\_less\_thm} and the differential equation for $\ExpName$, which we now know implies that the derivative of $\ExpName$ is everywhere positive.

\ThmsIII{%
=GFT
factorial_linear_estimate_thm
factorial_0_less_thm
factorial_times_recip_thm
exp_series_convergence_thm
exp_consistency_thm
Exp_consistent
=TEX
}{%
=GFT
exp_def
exp_unique_thm
exp_cts_thm
exp_¬_eq_0_thm
exp_minus_thm
exp_0_less_thm
=TEX
}{%
=GFT
exp_plus_thm
exp_clauses
exp_less_mono_thm
exp_power_series_thm
=TEX
}

\subsubsection{The Natural Logarithm Function}\label{TheNaturalLogarithmFunction}
The natural logarithm function is defined as the left inverse of the exponential function.
%%%%
%%%%
ⓈHOLCONST
│ 	⦏Log⦎ : ℝ → ℝ
├──────
│	∀x⦁ Log (Exp x) = x
■

We know enough about $\ExpName$ to show that it does indeed have a left inverse (which amounts to showing that it is one-to-one, which follows since it is strictly order-preserving).
From this follow standard algebraic facts about $\LogName$ as well as the fact that it is continuous and a calculation of its derivative.

\ThmsIII{%
=GFT
Log_consistent
log_def
exp_one_one_thm
exp_ℝ_ℕ_exp_thm
=TEX
}{%
=GFT
exp_0_less_onto_thm
exp_log_thm
log_less_mono_thm
log_cts_thm
=TEX
}{%
=GFT
log_deriv_thm
log_clauses
ℝ_ℕ_exp_exp_log_thm
=TEX
}

\subsubsection{The Sine and Cosine Functions}\label{TheSineAndCosineFunctions}
The sine and cosine functions are defined by differential equations and initial conditions.
%%%%
%%%%
ⓈHOLCONST
│ 	⦏Sin⦎ ⦏Cos⦎ : ℝ → ℝ
├──────
│	Sin(ℕℝ 0) = ℕℝ 0
│ ∧	Cos(ℕℝ 0) = ℕℝ 1
│ ∧	(∀x⦁ (Sin Deriv Cos x) x)
│ ∧	(∀x⦁ (Cos Deriv ~(Sin x)) x)
■

Using $\LogName$ and $\ExpName$, we can now easily derive some facts about roots, particularly square roots, that we will need to reason about the sine and cosine functions.
The existence of roots could be proved by more elementary means using the intermediate value theorem, but now we have $\LogName$ and $\ExpName$, it is much easier to use them instead.
We also need some facts about even and odd numbers etc. to work with the terms of the power series for sine and cosine.
We can then show using the power series that the definitions of sine and cosine are consistent, that they are uniquely specified by the definitions and so that they are equal to the expected power series expansions.
(The series for cosine is not in a particularly tidy form --- it is just what drops out from differentiating the series for sine term by term --- but this could easily be remedied.)
We then begin to develop their basic properties using the ``axiomatic'' approach following Mitchell \cite{Mitchell69}).

\ThmsII{%
=GFT
positive_root_thm
square_root_thm
square_root_thm1
square_root_unique_thm
square_square_root_mono_thm
sin_series_convergence_thm
even_odd_thm
mod_2_div_2_thm
mod_2_cases_thm
mod_2_0_ℝ_ℕ_exp_thm
mod_2_1_ℝ_ℕ_exp_thm
power_series_even_thm
power_series_odd_thm
=TEX
}{%
=GFT
sin_deriv_coeffs_thm
sin_cos_consistency_thm
Sin_consistent
sin_def
sin_cos_cts_thm
cos_squared_plus_sin_squared_thm
sin_cos_unique_lemma1
sin_cos_unique_lemma2
sin_cos_unique_thm
sin_cos_power_series_thm
sin_cos_plus_thm
sin_cos_minus_thm
=TEX
}

\subsubsection{The Number $\pi$}\label{TheNumberPi}

Finally, we define Archimedes' constant, the positive generator of the group of roots of the sine function:
%%%%
%%%%
ⓈHOLCONST
│ 	⦏ArchimedesConstant⦎ : ℝ
├──────
│	ℕℝ 0 < ArchimedesConstant
│ ∧	∀x⦁ Sin x = ℕℝ 0
│ 	⇔	(∃ m⦁ x = ℕℝ m * ArchimedesConstant)
│	∨	(∃m⦁ x = ~(ℕℝ m *ArchimedesConstant))
■
Archimedes' constant is, of course, almost always known by another name:
=SML
declare_alias("π", ⌜ArchimedesConstant⌝);
=TEX

We continue to develop the properties of sine and cosine via the axiomatic approach.
Much of this part of the work amounts to a consistency proof for the above definition of $\pi$.

\ThmsIII{%
=GFT
sin_0_group_thm
sin_eq_cos_sin_cos_twice_thm
sum_squares_abs_bound_thm
sum_squares_abs_bound_thm1
abs_sin_abs_cos_≤_1_thm
cos_positive_estimate_thm
=TEX
}{%
=GFT
sin_positive_estimate_thm
cos_greater_root_2_thm
cos_squared_eq_half_thm
sin_eq_cos_exists_thm
sin_positive_zero_thm
ℝ_discrete_subgroup_thm
=TEX
}{%
=GFT
pi_consistency_thm
ArchimedesConstant_consistent
π_def
ℕℝ_plus_1_times_bound_thm
ℕℝ_0_less_¬_ℕℝ_times_π_thm
=TEX
}

\subsubsection{Periodicity of the Sine and Cosine Functions}\label{PeriodicityOfTheSineAndCosineFunctions}
We conclude the axiomatic development of the properties of sine and cosine by proving their periodic behaviour and finally, with a view to later geometric applications, show that any numbers $x$ and $y$ with $x^2 + y^2 = 1$ are equal to $\Cos{z}$ and $\Sin{z}$ respectively for some, unique, $z$ in the interval $[0, 2\pi)$.

\ThmsII{%
=GFT
sin_¬_eq_0_thm
sin_0_π_0_less_thm
sin_cos_π_thm
sin_cos_π_over_2_thm
sin_cos_plus_π_over_2_thm
cos_¬_eq_0_thm
cos_eq_0_thm
sin_cos_plus_π_thm
=TEX
}{
=GFT
sin_cos_plus_2_π_thm
sin_cos_2_π_thm
sin_cos_plus_even_times_π_thm
sin_cos_even_times_π_thm
sin_cos_period_thm
sin_cos_onto_unit_circle_thm
sin_cos_onto_unit_circle_thm1
=TEX
}


=TEX
\subsection{L'H\^{o}pital's Rule}\label{LHopital}
In this section, we will state and prove (several formulations of) L'H\^{o}pital's rule, which 
states that under appropriate conditions, if the ratio of two derivatives $f'(y)/g'(y)$ has a limit
then so does $f(y)/g(y)$ and the two limits are equal.
This result is most naturally stated and proved using one-sided limits rather than the two-sided limits we have been using to date.
A two-sided reformulation is a trivial consequence of the one-sided one.
Moreover, one wants to apply the theorems to limits at infinity (e.g., to evaluate the definite integrals that define the Laplace transform).
In preparation for this, the next few subsections introduce the required new notions.

\subsubsection{Right-hand Limits of Function Values}

=TEX
We will write $(f {+}{\#}{-}{>} c) x$
to indicate that $f(y)$ tends to $c$ as $y$ tends to $x$ from the right:
=SML
declare_infix(205, "+#->");
ⓈHOLCONST
│ $⦏+#->⦎ : (ℝ → ℝ) → ℝ  → ℝ → BOOL
├──────
│∀f c a⦁
│	(f +#-> c) a
│ ⇔	∀e⦁ℕℝ 0 < e ⇒ ∃b⦁a < b ∧ ∀x⦁a < x ∧ x < b ⇒ Abs(f x - c) < e
■
As normal, we give a sequential convergence characterisation of this notion of limit and use it to calculate the right-hand limits of the usual algebraic combinations of functions.
We also show that the right-hand limit at $x$ of $f$ is $f(x)$ if $f$ is continuous at $x$
({\em cts\_lim\_right\_thm}) and show that two-sided limits may be characterised using one-sided limits
({\em lim\_fun\_lim\_right\_thm}).

\ThmsII{%
=GFT
lim_right_lim_seq_thm
lim_fun_lim_right_thm
const_lim_right_thm
id_lim_right_thm
plus_lim_right_thm
=TEX
}{%
=GFT
times_lim_right_thm
poly_lim_right_thm
recip_lim_right_thm
lim_right_unique_thm
cts_lim_right_thm
=TEX
}

\subsubsection{Limits of Function Values at $+\infty$}

We will write $f {-}{+}{\#}{>} c$
to indicate that $f(y)$ tends to $c$ as $y$ tends to $+\infty$:
=SML
declare_infix(205, "-+#>");
ⓈHOLCONST
│ $⦏-+#>⦎ : (ℝ → ℝ) → ℝ  → BOOL
├──────
│∀f c⦁
│	f -+#> c
│ ⇔	∀e⦁ℕℝ 0 < e ⇒ ∃b⦁∀x⦁b < x ⇒ Abs(f x - c) < e
■
As ever, we give a sequential convergence characterisation of this notion of limit and use it to calculate the limits at infinity of various functions.
We also show how a limit at infinity can be expressed in terms of a limit at 0 and {\it vice versa}.

\ThmsII{%
=GFT
lim_infinity_lim_seq_thm
lim_infinity_lim_right_thm
lim_right_lim_infinity_thm
const_lim_infinity_thm
id_lim_infinity_thm
=TEX
}{%
=GFT
plus_lim_infinity_thm
times_lim_infinity_thm
poly_lim_infinity_thm
recip_lim_infinity_thm
lim_infinity_unique_thm
=TEX
}

(Note on the symbols: `%
=INLINEFT
#
=TEX
' in the arrows means $\infty$; `%
=INLINEFT
+#-
=TEX
' is then intended to suggest a passage along the real line to a point starting at $+\infty$
and `%
=INLINEFT
-+#
=TEX
' a passage in the opposite direction.)

\subsubsection{Divergence to $\infty$ at $+\infty$}

We will write $f {-}{+}{\#}{>}{+}{\#}$
to indicate that $f(y)$ diverges to $+\infty$ as $y$ tends to $+\infty$:

=SML
declare_postfix(200, "-+#>+#");
ⓈHOLCONST
│ $⦏-+#>+#⦎ : (ℝ → ℝ) → BOOL
├──────
│∀f⦁ f -+#>+# ⇔ ∀x⦁ ∃b⦁ ∀y⦁ b < y ⇒ x < f y
■


\ThmsII{%
=GFT
div_infinity_pos_thm
const_plus_div_infinity_thm
id_div_infinity_thm
plus_div_infinity_thm
const_times_div_infinity_thm
times_div_infinity_thm
power_div_infinity_thm
=TEX
}{%
=GFT
less_div_infinity_thm
bounded_deriv_div_infinity_thm
exp_div_infinity_thm
log_div_infinity_thm
div_infinity_times_recip_thm
div_infinity_lim_right_thm
div_infinity_lim_infinity_thm
=TEX
}

\subsubsection{Formulations of l'H\^{o}pital's rule}

We are now ready to formulate l'H\^{o}pital's rule.
In all the formulations this deals with two functions $f$ and $g$ such that the ratio $f'(y)/g'(y)$ has a limit.

The first formulation is for right-hand limits
under the following conditions: for some $b > a$, $f$ and $g$ must be continuous in the half-closed interval $[a, b)$; $f$ and $g$ must differentiable in the open interval $(a, b)$; the derivative $g'(y)$ must not vanish in $(a, b)$ while $f(a) = f(b) = 0$.
The second formulation is as the first but stated for two-sided limits rather than right-hand limits and has similar conditions.
The third formulation is for limits at $+\infty$
under the following condition: for some $a$, $f$ and $g$ must be differentiable in the half-closed interval $(a, \infty)$; and the derivative $g'(y)$ must not vanish in $(a, \infty)$.

A variant of Rolle's theorem is used to show that, under these conditions, $g(y)$ does not vanish in a suitable open interval --- this is rolled up in the Cauchy mean value theorem in the textbook proofs, but our `symmetric' formulation of the latter theorem means that we need to establish this separately.
A couple of lemmas about the continuity and derivatives of the function $f(-x)$ are also handy in deducing the second formulation of the rule from the first.

\ThmsII{%
=GFT
rolle_thm1
l'hopital_lim_right_thm
cts_comp_minus_thm
=TEX
}{
=GFT
deriv_comp_minus_thm
l'hopital_lim_fun_thm
l'hopital_lim_infinity_thm
=TEX
}


\subsubsection{Some Applications}

We now put l'H\^{o}pital's rule to work.
The first application is a simple general result saying (in effect) that under suitable conditions limits of function values and derivatives commute.

Then we calculate some specific limits:
$x/\Sin{x}$ as $x$ tends to 0 (0);
$x^m/\Exp{x}$ and $\Log{x}/x$ as $x$ tends to $+\infty$ (both 0); 
$\Log{x}/x$ as $x$ tends to $+\infty$ (1);
$\Log{x}/(x-1)$  as $x$ tends to $1$ (and, hence, $\Log{1+x}/x$ as $x$ tends to $0$) (1);
and, finally, $(1+x)^{1/x} = \Exp{\Log{1+x}/x}$ as $x$ tends to 
$0$ ($e = \Exp{1}$), which leads to the famous result that $e$ is the limit as $n$ tends to infinity of $(1+1/n)^{n}$.

\ThmsII{%
=GFT
cts_deriv_deriv_thm
lim_fun_id_over_sin_thm
lim_infinity_recip_exp_thm
lim_infinity_id_over_exp_thm
lim_infinity_power_over_exp_thm
=TEX
}{
=GFT
lim_infinity_log_over_id_thm
lim_fun_log_over_id_minus_1_thm
lim_fun_log_1_plus_over_id_thm
lim_fun_e_thm
lim_seq_e_thm
=TEX
}
\subsection{Further Functions}\label{FurtherFunctions}
\subsubsection{Inverse Functions}
We have already dealt with the construction of one inverse function, namely $\LogName$ as the inverse of $\ExpName$.
The methods used were a little {\em ad hoc} and exploited some of the very nice particular properties of $\ExpName$.

We now develop some simple theory for dealing with the inverses of invertible continuous functions.
We provide a selection of simple theorems that support some common cases. Later sections will apply the theorems to functions such as the square root function, $\ArcSinName$ and $\ArcSinhName$.
The cases we deal with here cover functions
which are ({\em total\_inverse\_thm}) or which can be adapted to be
({\em closed\_half\_infinite\_inverse\_thm}, 
{\em closed\_interval\_inverse\_thm}) order-preserving bijections from the whole real line to itself.
In all of these cases, the inverse is or can be chosen to be everywhere continuous.
In applications this lets us specify an inverse of a continuous function defined over a closed interval, say, to be continuous at the end-points of its interval of definition.

\ThmsII{
=GFT
ℝ_less_mono_⇔_thm
ℝ_less_mono_⇔_≤_thm
ℝ_less_mono_one_one_thm
total_inverse_cts_thm
total_inverse_thm
=TEX
}{
=GFT
closed_half_infinite_inverse_thm1
closed_half_infinite_inverse_thm
cond_cts_thm
cond_cts_thm1
closed_interval_inverse_thm
=TEX
}

\subsubsection{The Square Root Function}

The square root function is an example of an inverse function defined on a closed half-infinite interval.
Note that we can and do specify it to be continuous (in our two-sided sense of the word) throughout the interval of definition.
This information is redundant in the interior of the interval, but not at the end-point.
The extra detail can be very useful in applications (cf. the statement of numerous theorems such as the mean value theorem which require continuity but not differentiability at the end-points of an interval).

ⓈHOLCONST
│ ⦏Sqrt⦎ : ℝ → ℝ
├──────
│ ∀x⦁ ℕℝ 0 ≤ x ⇒ ℕℝ 0 ≤ Sqrt x ∧ (Sqrt x) ^ 2 = x ∧ Sqrt Cts x
■
We prove a selection of theorems about the square root function.
Many of these are needed later for dealing with the derivatives of trigonometric functions etc.

\ThmsIII{
=GFT
sqrt_def
sqrt_square_thm
square_sqrt_thm
square_times_thm
sqrt_times_thm
=TEX
}{%
=GFT
square_recip_thm
sqrt_pos_thm
sqrt_recip_thm
sqrt_exp_log_thm
sqrt_deriv_thm
=TEX
}{%
=GFT
id_over_sqrt_thm
sqrt_1_minus_sin_squared_thm
sqrt_1_minus_cos_squared_thm
=TEX
}

\subsubsection{More Trigonometric Functions}
The standard definitions of the remaining trigonometric functions in terms of $\SinName$ and $\CosName$ are given in table~\ref{tan_etc}.

\begin{table}[htb]
\begin{center}
{\footnotesize\begin{tabular}{l@{}l}
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Tan⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Tan x = Sin x * Cos x ⋏-⋏1
■
\end{minipage} &
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Cotan⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Cotan x = Cos x * Sin x ⋏-⋏1
■
\end{minipage} \\
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Sec⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Sec x = Cos x ⋏-⋏1
■
\end{minipage} &
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Cosec⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Cosec x = Sin x ⋏-⋏1
■
\end{minipage} \\
\end{tabular}}
\end{center}
\caption{Further Trigonometric Functions}
\label{tan_etc}
\end{table}

We provide theorems giving the derivatives of all of these functions.
Apart from a little algebraic manipulation, the derivatives are all dealt with automatically by the tactic described in section~\ref{Derivatives}.


\ThmsIII{
=GFT
tan_deriv_thm
cotan_deriv_thm
=TEX
}{%
=GFT
sec_deriv_thm
=TEX
}{%
=GFT
cosec_deriv_thm
=TEX
}

We now define the inverse of the sine function, $\ArcSinName$.
It is an example of an inverse defined over a closed interval.
The defining property below is somewhat redundant, but as the theorems about inverse functions that support the consistency proof deliver all this information readily,
it is convenient to include it in the defining property.
As with the square root function, we take the function to be continuous at the end-points of its interval of definition.

ⓈHOLCONST
│ ⦏ArcSin⦎ : ℝ → ℝ
├──────
│	(∀x⦁ Abs x ≤ 1/2 * π ⇒ ArcSin (Sin x) = x)
│ ∧	(∀x⦁ Abs x ≤ ℕℝ 1 ⇒ Sin(ArcSin x) = x ∧ ArcSin Cts x)
■

After proving the consistency of the definition, we prove some lemmas which just provide the various parts of the definition in separate packaging and one or two simple algebraic properties of $\ArcSinName$.
These are then used to calculate its derivative.

\ThmsII{
=GFT
ArcSin_consistent
arc_sin_def
sin_arc_sin_thm
=TEX
}{%
=GFT
abs_arc_sin_thm
arc_sin_sin_thm
cos_arc_sin_thm
=TEX
}{%
=GFT
arc_sin_1_minus_1_thm
arc_sin_deriv_thm
=TEX
}

For use in applications, we also define the inverse of the cosine function, $\ArcCosName$ and prove some elementary theorems about it.
 

ⓈHOLCONST
│ ⦏ArcCos⦎ : ℝ → ℝ
├──────
│	(∀x⦁ ℕℝ 0 ≤ x ∧ x ≤ π ⇒ ArcCos (Cos x) = x)
│ ∧	(∀x⦁ Abs x ≤ ℕℝ 1 ⇒ Cos(ArcCos x) = x ∧ ArcCos Cts x)
■
\ThmsII{
=GFT
ArcCos_consistent
arc_cos_def
=TEX
}{%
=GFT
cos_arc_cos_thm
abs_arc_cos_thm
=TEX
}{%
=GFT
arc_cos_cos_thm
cos_arc_cos_thm
=TEX
}

\subsubsection{Hyperbolic Trigonometric Functions}
Table~\ref{sinh_etc} presents the standard definitions of the six hyperbolic trigonometric functions in terms of $\ExpName$.

\begin{table}[htb]
\begin{center}
{\footnotesize\begin{tabular}{l@{}l}
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Sinh⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Sinh x = 1/2 * (Exp x - Exp (~x))
■
\end{minipage} &
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Cosh⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Cosh x = 1/2 * (Exp x + Exp (~x))
■
\end{minipage} \\
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Tanh⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Tanh x = Sinh x * Cosh x ⋏-⋏1
■
\end{minipage} &
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Cotanh⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Cotanh x = Cosh x * Sinh x ⋏-⋏1
■
\end{minipage} \\
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Sech⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Sech x = Cosh x ⋏-⋏1
■
\end{minipage} &
\begin{minipage}[t]{0.48\hsize}
ⓈHOLCONST
│ ⦏Cosech⦎ : ℝ → ℝ
├──────
│ ∀x⦁ Cosech x = Sinh x ⋏-⋏1
■
\end{minipage}
\end{tabular}}
\end{center}
\caption{The Hyperbolic Trigonometric Functions}\label{HyperbolicTrigonometicFunctions}
\label{sinh_etc}
\end{table}


As with the circular trigonometric functions, we provide theorems giving the derivatives of all these functions (together with one or two algebraic properties needed to calculate the derivatives).
Again, apart from a little algebraic manipulation, the derivatives are all dealt with automatically by the tactic described in section~\ref{Derivatives}.

\ThmsII{
=GFT
sinh_deriv_thm
cosh_deriv_thm
cosh_0_less_thm
=TEX
}{%
=GFT
cosh_non_0_thm
sinh_non_0_thm
cosh_squared_minus_sinh_squared_thm
=TEX
}{%
=GFT
tanh_deriv_thm
cotanh_deriv_thm
sech_deriv_thm
=TEX
}

We also introduce the inverse, $\ArcSinhName$, of $\SinhName$.
It is an inverse function of the simplest type, since the domain and range of $\SinhName$ are the whole real line.
As with the square root and $\ArcSinName$ functions, the method of proving the definition consistent gives us the continuity of the function for free.

ⓈHOLCONST
│ ⦏ArcSinh⦎ : ℝ → ℝ
├──────
│	∀x⦁ ArcSinh (Sinh x) = x ∧ Sinh(ArcSinh x) = x ∧ ArcSinh Cts x
■

After proving the consistency of the definition, we derive a couple of algebraic properties and use them to calculate the derivative.

\ThmsIII{
=GFT
ArcSinh_consistent
arc_sinh_def
=TEX
}{%
=GFT
sqrt_1_plus_sinh_squared_thm
cosh_arc_sinh_thm
=TEX
}{%
=GFT
arc_sinh_deriv_thm
=TEX
}


\subsection{Integration}\label{Integration}
The Henstock-Kurzweil approach to the integral calculus is very well-suited to our needs.
In addition to the advantages listed by John Harrison \cite{Harrison96}, I note that: {\em(i)}
the Henstock-Kurzweil gauge integral is not restricted to functions with a bounded range and can naturally be formulated so that  integrals over bounded and unbounded intervals fall under a single definition;
{\em(ii)} the fundamental theorem of the calculus for the gauge integral can accommodate an antiderivative that ``fails'' at some points of the interval of integration.

Both these points are illustrated by the example $\int_{x=-1}^{+1}dx/\sqrt{1 - x^2}$. The fundamental theorem for the gauge integral shows this to be equal to $[\ArcSin{x}]_{-1}^{+1} = \pi$ even though at the points $-1$ and $+1$ the antiderivative $\ArcSin{x}$ is not differentiable and the integrand $1/\sqrt{1 - x^2}$ tends to $+\infty$.
This integral would be much more complicated to deal with under the Riemann theory.

\subsubsection{The Henstock-Kurzweil Gauge Integral Defined}

We now define the Henstock-Kurzweil gauge integral, see, e.g., the book by Kurtz and Swartz~\cite{Kurtz04}.
Our approach is to take integrals over the whole line as fundamental and to define integrals over subsets such as intervals as a derived notion.

The Henstock-Kurzweil theory deals with estimates to the putative value of an integral defined over what we call, following Kurtz and Swartz, {\em tagged partitions} (also called ``tagged divisions'' in the literature). A tagged partition of an interval comprises a (finite) contiguous sequence of closed intervals, $[I_0, I_1], [I_1, I_2], \ldots, [I_n, I_{n+1}]$ together with sample points, $t_0 \in [I_0, I_1], t_1 \in [I_1, I_2], \ldots, t_n \in [I_n, I_{n+1}]$.
We represent the sequence of intervals by the real-valued sequence giving the end-points (and for simplicity, we require each interval to have a non-empty interior). This leads to the following definition:

ⓈHOLCONST
│ ⦏TaggedPartition⦎ : ((ℕ → ℝ) × (ℕ → ℝ) × ℕ) SET
├──────
│∀t I n⦁	(t, I, n) ∈ TaggedPartition
│ ⇔	(∀m⦁ m < n ⇒ I m < I (m+1))
│ ∧	(∀m⦁ m < n ⇒ t m ∈ ClosedInterval (I m) (I (m+1)))
■


The {\em Riemann sum} associated with a real-valued function and a tagged partition is then the estimate given by taking the sums of the values at the sample points each weighted by the length of the corresponding sample interval.
Recalling that {\em Series} is the function that maps a sequence, $s_m$, to its sequence of partial sums $\sum_{n = 0}^{m-1}s_n$, we capture this as follows:

ⓈHOLCONST
│ ⦏RiemannSum⦎ : (ℝ → ℝ) → ((ℕ → ℝ) × (ℕ → ℝ) × ℕ) → ℝ
├──────
│∀f t I n⦁	RiemannSum f (t, I, n) = Series (λm⦁ f(t m) * (I(m+1) - I m)) n
■
The Riemann integral of a function $f$ over an interval $[a, b]$ is given by a limit as $\delta > 0$ tends to zero of
Riemann sums of $f$ formed over tagged partitions that cover the interval and whose mesh (maximum length of interval) is bounded by $\delta$.
The Henstock-Kurzweil theory generalises this limiting process to take into account local behaviour of $f$.
A local bound on the interval lengths in a tagged partition is given by what is called a {\em gauge}, which we define to be a function that maps each real number $x$ to one of its open neighbourhoods.

ⓈHOLCONST
│ ⦏Gauge⦎ : (ℝ → ℝ SET) SET
├──────
│∀G⦁ G ∈ Gauge ⇔ ∀x⦁ G x ∈ Open⋎R ∧ x ∈ G x
■

Note: the theory is not affected if gauges are restricted to open intervals rather than arbitrary open neighbourhoods or even intervals that are symmetric about the point in question (in which case a gauge reduces, essentially, to a positive function giving the radii of the symmetric intervals).
However, it seems best to have as much freedom as one can in designing gauges (since that is the crux of many of the proofs).

A tagged partition is {\em fine} with respect to a gauge if each of its interval is contained in the open set that the gauge associates with the corresponding tag.
=SML
declare_postfix(330, "Fine");
ⓈHOLCONST
│ ⦏$Fine⦎ : (ℝ → ℝ SET) → ((ℕ → ℝ) × (ℕ → ℝ) × ℕ) SET
├──────
│∀t I n G⦁
│	(t, I, n) ∈ G Fine
│ ⇔	(∀m⦁ m < n ⇒ ClosedInterval (I m) (I (m+1)) ⊆ G(t m))
■
 
We now define the gauge integral of a function over the whole real line. A function $f$ has integral $c$  iff. for any positive $e$, there is a gauge $G$ and real values $a < b$, such that any Riemann sum of $f$ over a $G$-fine tagged partition that covers the interval $[a, b]$ is within $e$ of $c$.
When this is the case, we write
=INLINEFT
f Int⋎R c
=TEX
, which corresponds to the informal statement that the integral $\int_{x=-\infty}^{+\infty}f(x)dx$ exists and is equal to $c$.

=SML
declare_infix(200, "Int⋎R");
=TEX
ⓈHOLCONST
│ $⦏Int⋎R⦎ : (ℝ→ ℝ) → ℝ → BOOL
├──────
│∀f c⦁
│	(f Int⋎R c)
│ ⇔	∀e⦁ ℕℝ 0 < e ⇒
│	∃G a b⦁	G ∈ Gauge ∧ a < b
│	∧ ∀t I n⦁	(t, I, n) ∈ TaggedPartition
│		∧	I 0 < a ∧ b < I n ∧ (t, I, n) ∈ G Fine
│		⇒	Abs(RiemannSum f (t, I, n) - c) < e
■
(Those familiar with the theory formulated over a bounded interval $[a, b]$, should think of our partitions as modelling a partition of the extended real line $[-\infty, +\infty]$ with the function $f$ extended to have the value 0 at $\pm\infty$ and with the sample points in the half-infinite intervals restricted to lie at $\pm\infty$, so that those intervals make no contribution to the Riemann sums.
We will prove ({\em bounded\_int\_thm}) that our definition agrees with the other formulation for integrals over bounded intervals.)

To define integrals over bounded intervals, we use the notion of characteristic function, which we can conveniently define polymorphically rather than just for sets of real numbers.

ⓈHOLCONST
│ ⦏CharFun⦎ : 'a SET → 'a → ℝ
├──────
│∀A x⦁ CharFun A x = if x ∈ A then ℕℝ 1 else ℕℝ 0
■
=SML
declare_alias("χ", ⌜CharFun⌝);
=TEX
We now define the gauge integral of $f$ over a set $A$ to be the integral over the whole real line of the function defined to agree with $f$ on $A$ and to be identically zero off $A$.
$A$ will, of course, often be an interval,
in which case the formal notation
=INLINEFT
(f Int c) (ClosedInterval a b)
=TEX
\ corresponds to the informal statement that the integral
$\int_{x=a}^{b}f(x)dx$ exists and is equal to $c$.

=SML
declare_infix(200, "Int");
=TEX
ⓈHOLCONST
│ $⦏Int⦎ : (ℝ→ ℝ) → ℝ → ℝ SET → BOOL
├──────
│∀f c A⦁ (f Int c) A ⇔ (λx⦁ χ A x * f x) Int⋎R c
■

\subsubsection{Properties of the Integral}

The development of the theory begins with some generalities about gauges.
One says that one gauge, $G1$, refines another, $G2$, if $G1(x) \subseteq G2(x)$, for every $x$ (which means that $G1$-fineness implies $G2$-fineness).
Any 2 gauges have a greatest common refinement given by intersection of their values.
New gauges can be formed from old by composing them with a reflection, a translation or a dilation.

\ThmsII{
=GFT
gauge_∩_thm
gauge_o_minus_thm
gauge_o_plus_thm
gauge_o_times_thm
=TEX
}{%
=GFT
gauge_refinement_thm
gauge_refine_3_thm
fine_refinement_thm
=TEX
}

What I call the {\em chosen tag theorem} is very useful in designing gauges to achieve special effects: it says that for any real number $a$, there is a gauge $G$ such that  any tagged partition which is $G$-fine has $a$ as the sample point in any of its intervals that contains $a$. We also have an analogous theorem for a finite set of chosen tags.
We then have a theorem which asserts the existence of the ``uniform'' gauges that characterise the Riemann integral.

Finally in this block we have Cousin's lemma, which says that, if a gauge $G$ and $a \le b$ are given, then there exists a $G$-fine tagged partition beginning at $a$ and ending at $b$.
The proof is very neat via Bolzano's principle of bisection.

\ThmsII{
=GFT
chosen_tag_thm
chosen_tags_thm
=TEX
}{%
=GFT
riemann_gauge_thm
cousin_lemma
=TEX
}

We need to develop some elementary theory to deal with Riemann sums, tagged partitions and so on. This is given in the following block of lemmas, showing, for example, that the Riemann sum operation is linear in its function argument.
The last of these lemmas captures the fact that a given point can occur as the sample point in at most two of the intervals in a tagged partititon (and if it does occur in two, then the two are consecutive).

\ThmsIII{
=GFT
riemann_sum_induction_thm
series_induction_thm1
ℝ_abs_series_thm
riemann_sum_induction_thm1
riemann_sum_plus_thm
riemann_sum_const_times_thm
riemann_sum_minus_thm
riemann_sum_local_thm
riemann_sum_o_minus_thm
riemann_sum_o_times_thm
=TEX
}{%
=GFT
partition_reverse_clauses
tagged_partition_append_thm
fine_append_thm
riemann_sum_0_thm
riemann_sum_append_thm
riemann_sum_¬_0_thm
partition_mono_thm
tag_mono_thm
tag_upper_bound_thm
=TEX
}{%
=GFT
tag_lower_bound_thm
subpartition_thm
subpartition_fine_thm
riemann_sum_local_thm1
riemann_sum_0_≤_thm
tag_unique_thm
partition_cover_thm
partition_cover_thm1
riemann_sum_χ_singleton_thm
=TEX
}

Now we can start proving basic facts about the gauge integral.
Our first few lemmas show that it is a linear operator .
We then prove that integrals are unique when they exist.
This follows from Cousin's lemma and linearity

\ThmsIII{
=GFT
int_ℝ_plus_thm
int_ℝ_minus_thm
=TEX
}{%
=GFT
int_ℝ_0_thm
int_ℝ_const_times_thm
=TEX
}{%
=GFT
int_ℝ_diff_0_thm
int_ℝ_unique_thm
=TEX
}

There are then some results mainly about functions with integral 0, but beginning with the fact that integration is weakly order-preserving (taking the pointwise ordering of functions).
If a non-negative function, $f$, is dominated by a function, $g$, and if $g$ is integrable with integral 0, then so is $f$.
The characteristic functions of singleton sets are integrable with integral 0, and, hence, so are all functions with finite support.


\ThmsIII{
=GFT
int_ℝ_0_≤_thm
int_ℝ_≤_thm
int_ℝ_0_dominated_thm
=TEX
}{%
=GFT
int_ℝ_χ_singleton_lemma
int_ℝ_χ_singleton_thm
=TEX
}{%
=GFT
int_ℝ_singleton_support_thm
int_ℝ_finite_support_thm
=TEX
}

The next few theorems are about sets of measure 0, i.e., sets $A$ such that the characteristic function $\chi_A$ is integrable with integral 0.
The set of sets of measure 0 is downwards closed and forms a join semilattice.

\ThmsII{
=GFT
int_ℝ_χ_0_⊆_thm
int_ℝ_χ_0_∩_thm
=TEX
}{%
=GFT
χ_∪_∩_thm
int_ℝ_χ_0_∪_thm
=TEX
}


The first few lemmas in the next block show (in various useful guises) that the integral is not affected by the value of the function at a selected point.
So for example, integration over a closed interval, $[a, b]$ is equivalent to integration over the corresponing open interval, $(a, b)$
We then investigate how the integral is transformed under linear change of variables.
The remaining results here show that our definition of the integral over a closed interval agrees with the more normal one (defined in terms of tagged partitions that precisely cover the interval).

\ThmsII{%
=GFT
int_half_infinite_interval_thm
chosen_value_thm
int_interval_thm
int_ℝ_o_minus_thm
int_ℝ_o_plus_thm
int_ℝ_o_times_thm
=TEX
}{%
=GFT
int_ℝ_support_bounded_below_thm
int_support_bounded_below_lemma
int_bounded_below_thm
int_ℝ_bounded_support_thm
bounded_int_thm
bounded_int_local_thm
=TEX
}

\subsubsection{The Fundamental Theorem of the Calculus}

We move on to prove the fundamental theorem of the calculus saying that if $sf$ has derivative $f$ in some open interval $(a, b)$ and if $sf$ is continuous at $a$ and $b$ then $f$ is integrable on $[a, b]$ with integral equal to $sf(b) - sf(a)$ (this is {\em int\_deriv\_thm} below, the other variants corresponding to the common cases where $sf$ is differentiable at one or both of the end-points of the intervals).

The key lemma in the result is the so-called {\em straddle theorem}. We use this to prove the result in the case where $sf$ is required to be differentiable at $a$, but not at $b$, the other cases being easy consequences of that case.
In outline, the proof uses the straddle lemma to show that the fundamental theorem holds over $[a, x]$ for all $x$ in $(a, b)$ and then the continuity of $sf$ at $b$ to show that the integral over $[a, b]$ exists and is equal to the limit of the integrals over $[a, x]$ as $x$ tends to $b$ which gives the desired result.
In fact, the fundamental theorem of the calculus can be made to accommodate countably many points of failure in the antiderivative, but the argument is a little harder and we have not yet needed the full strength of the result.

\ThmsIII
{%
=GFT
straddle_thm
straddle_gauge_thm
=TEX
}{%
=GFT
int_deriv_thm2
int_deriv_thm3
=TEX
}{%
=GFT
int_deriv_thm
int_deriv_thm1
=TEX
}


Armed with the fundamental theorem, we calculate the integrals of some example integrands: the characteristic function of an interval; the example $1/\sqrt{1 - x^2}$ mentioned at the beginning of this section; and the reciprocal function.


\ThmsIII{%
=GFT
int_ℝ_χ_interval_thm
=TEX
}{%
=GFT
int_example_thm
=TEX
}{%
=GFT
int_recip_thm
=TEX
}

We put the last of these theorems to work to show that the harmonic series $s_i = 1/m$ is divergent: the theorem says that if $0 < a < b$, then $\int_a^b(1/x)dx = \Log{b} - \Log{a}$.
Since $1/x \le 1/a$ throughout this interval we have that $\Log{b} - \Log{a} \le  \int_a^b(1/a)dx = (b-a)/a$.
Thus for positive integer $m$, taking $a = m$, $b = m +1$, we have that $\Log{m+1} - \Log{m} \le 1/m$. Adding these inequalities for $1 \le m \le n$, gives that $\Log{n} \le \sum_{m=1}^n 1/m$ and so the latter sequence of partial sums must diverge as $n$ tends to $\infty$.
The following block of theorems implement this argument.

\ThmsIII{%
=GFT
log_minus_log_estimate_thm
=TEX
}{%
=GFT
harmonic_series_estimate_thm
=TEX
}{%
=GFT
harmonic_series_divergent_thm
=TEX
}



\subsubsection{Application: Areas of Plane Sets}
The standard Lebesgue measure on the real line can be defined using the gauge integral, the measure of a set, $A$, being the integral, $\int_{x=-\infty}^{\infty}\chi_A(x)dx$, of its characteristic function.
Analogously, we may define the {\em area} of a plane set $A$, to be given by the following double integral\footnote{
The resulting notion is slightly less general than the standard Lebesgue measure on the plane, but bounded Lebesgue measurable sets which fail to have an area in this sense are quite exotic.
In any case, the definition matches the standard and time-honoured way of calculating areas in practice.
}:
\[
\int_{x=-\infty}^{+\infty}\int_{y=-\infty}^{+\infty}\chi_{A}(x, y)dydx = \int_{x=-\infty}^{+\infty}\int_{y=-\infty}^{+\infty}\chi_{\{y | (x, y) \in A\}}(y)dydx
\]

In the formal treatment, we will write `%
=INLINEFT
A Area c
=TEX
' to indicate that the plane set $A$ has area $c$, as given by the above double integral, if it exists.
The following definition captures this using the ``curried'' form of the integrand given on the right-hand side of the equation above.
The function $sf$ in the definition gives the inner integral.

=SML
declare_infix(200, "Area");
=TEX
ⓈHOLCONST
│ $⦏Area⦎ : (ℝ × ℝ) SET → ℝ → BOOL
├──────
│∀A c⦁ (A Area c) ⇔ ∃sf⦁ sf Int⋎R c ∧ (∀x⦁ χ {y | (x, y) ∈ A} Int⋎R sf x)
■


We first prove some generalities which are useful in calculations and which help to verify that we have given the definition correctly.
Firstly, and very importantly, the area of a set is unique if it is defined; 
areas are invariant under translations;
under a dilation with scale factors $d \not= 0$ along the $x$-axis and $e \not= 0$ along the $y$-axis, areas are multiplied by $|d| \times |e|$;
the area of the empty set is $0$;
if $A$ and $B$ have areas, then $A \cup B$ has an area iff. $A \cap B$ does and in that case the four areas are related by the inclusion/exclusion principle (the two directions of the bi-implication are given as separate theorems below).

\ThmsIII{
=GFT
area_unique_thm
area_translate_thm
area_dilate_thm
=TEX
}{%
=GFT
area_dilate_thm1
area_empty_thm
=TEX
}{%
=GFT
area_∪_thm
area_∩_thm
=TEX
}

We now calculate some specific areas.
The area of a rectangle of width $w$ and height $h$ is $w\times h$.
The proof implements the following evaluation of the double integral giving the area:
\[
\int_{x=-\infty}^{+\infty}\int_{y=-\infty}^{+\infty}\chi_{\{y | x \in [0, w] \land y \in [0, h]\}}(y)dydx =
\int_{x=0}^{w}\int_{y=0}^{h}1\,dydx =
\int_{x=0}^{w}h\,dydx = w \times h
\]


\ThmsII{%
=GFT
area_rectangle_thm
=TEX
}{}

We next calculate the area bounded by a circle of radius $r$, i.e., the area of the set of points $(x, y)$ such that $\sqrt{x^2+y^2} \le r$.
We proceed in a sequence of lemmas implementing the following argument:
first consider the case $r = 1$, so that the set we are interested in is bounded by the graphs of the functions $\sqrt{1 - x^2}$ and $-\sqrt{1 - x^2}$ between the end-points $x=-1$ and $x=1$.
The inner integral in the double integral giving the area is therefore equal to $2\sqrt{1 - x^2}$:
\[
\int_{x=-\infty}^{+\infty}\int_{y=-\infty}^{+\infty}\chi_{\{y | \sqrt{x^2+y^2}\le 1\}}(y)dydx =
\int_{x=-1}^{+1}2\sqrt{1 - x^2}dx
\]

The substitution $x = \sin{\theta}$ suggests the antiderivative $x\sqrt{1-x^2} + \ArcSin{x}$ for the integrand $2\sqrt{1 - x^2}$.
Subject to a little algebraic simplification, this may be verified mechanically for $x$ in the open interval $(-1, 1)$.
As the antiderivative is continuous throughout $[-1, 1]$, we can apply the fundamental theorem of the calculus\footnote{
The antiderivative can be adjusted to be valid at the end-points of the integral too, but
proving that involves additional effort and the proof is not routine. The gauge integral comes into its own here in saving us work.
} to conclude that
\[
\int_{x=-1}^{+1}2\sqrt{1 - x^2}dx = \left[x\sqrt{1-x^2} + \ArcSin{x}\right]_{x=-1}^{+1} = (0 + \pi/2) - (0 - \pi/2) = \pi.
\]


That the area bounded by a circle of radius $r$ is $\pi r^2$ now follows from what we have proved about the behaviour of areas under dilations (given that the set in question is the image of the set bounded by the unit circle under a dilation with scale factor $r$ in both directions).

\ThmsIII{%
=GFT
area_circle_lemma1
area_circle_lemma2
area_circle_lemma3
=TEX
}{%
=GFT
area_circle_lemma4
area_circle_int_thm
area_unit_circle_thm
=TEX
}{%
=GFT
circle_dilate_thm
area_circle_thm
=TEX
}

Using this notion of area, we can calculate probabilities of events parametrised by pairs of real numbers:
Ii $S \subseteq \R \times \R$ is a sample space with area $s \not= 0$ say, and $X \subseteq S$ has area $x$, then the probability that an event in $S$ belongs to $X$ is $x/s$.
In this way, we may state and prove the Buffon needle theorem: 
this says that if a needle of unit length is dropped at random onto the plane, then the probability that the needle crosses one of the lines $y = m$ with $m \in \Z$ is $2/\pi$.

We take as the parameters {\em(i)}, the angle, $\theta$, between the needle and the horizontal, and, {\em(ii)}, the distance, $d$, between the uppermost end of the needle and the line $y = m$ immediately below it.
So $S$ is the set $[0, \pi] \times [0, 1]$ and $X$ comprises those $(\theta, d) \in S$ such that the line segment between $(0, d)$ and $(\Cos{\theta}, d - \Sin{\theta})$ crosses the $x$-axis.
$X$ and $S$ have areas $2$ and $\pi$ respectively which gives the stated probability of $2/\pi$.
The proofs of the theorems named below implement this argument with the calculation of the area of $X$ as a separate lemma.

\ThmsII{
=GFT
buffon_needle_lemma
=TEX
}{%
=GFT
buffon_needle_thm
=TEX
}

\newpage

%%%%
%%%%
%%%%
%%%%
\appendix
{\let\Section\section
\def\section#1{\Section{#1}\label{TheoryListing}}
\include{wrk066.th}
}  %\let

\twocolumn[\section*{INDEX}\label{INDEX}]
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
%%%%
%%%%
\subsection{The Definitions and Their Consistency}
%%%%
%%%%
%%%%
%%%%
We give bindings for the definitions and discharge the easy consistency
proof obligations.
The consistency of the definitions of the transcendental functions will depend on
most of the theory that we develop.
%%%%
%%%%
=SML
val ⦏poly_func_def⦎ = get_spec⌜PolyFunc⌝;
val ⦏poly_eval_def⦎ = get_spec⌜PolyEval⌝;
=TEX
Here is the only easy consistency proof obligation, which just arises
because the definition of {\it PlusCoeffs} is not quite in the
form that the existence prover for recursive definitions over
the natural numbers expects.
%%%%
%%%%
=SML
push_consistency_goal⌜PlusCoeffs⌝;
a(lemma_tac⌜∃ac⦁
 	(∀l⦁ ac [] l = l)
∧	(∀c1 : ℝ; l1⦁
	ac (Cons c1 l1) [] = Cons c1 l1
∧	(∀c2 l2⦁ ac (Cons c1 l1) (Cons c2 l2) =
	Cons (c1 + c2) (ac l1 l2)))
⌝ THEN1 prove_∃_tac);
a(∃_tac ⌜ac⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(list_induction_tac⌜l⌝ THEN asm_rewrite_tac[]);
val _ = save_consistency_thm ⌜PlusCoeffs⌝ (pop_thm());

val ⦏plus_coeffs_def⦎ = save_thm("plus_coeffs_def", get_spec⌜PlusCoeffs⌝);
val ⦏times_coeffs_def⦎ = get_spec⌜TimesCoeffs⌝;
val ⦏deriv_coeffs_def⦎ = get_spec⌜DerivCoeffs⌝;
val ⦏to_def⦎ = get_spec⌜$To⌝;
val ⦏roots_def⦎ = get_spec⌜Roots⌝;
val ⦏series_def⦎ = get_spec⌜Series⌝;
val ⦏power_series_def⦎ = get_spec⌜PowerSeries⌝;
val ⦏lim_seq_def⦎ = get_spec⌜$->⌝;
val ⦏lim_fun_def⦎ = get_spec⌜$-->⌝;
val ⦏unif_lim_seq_def⦎ = get_spec⌜$--->⌝;
val ⦏cts_def⦎ = get_spec⌜$Cts⌝;
val ⦏deriv_def⦎ = get_spec⌜$Deriv⌝;
val ⦏closed_interval_def⦎ = get_spec⌜ClosedInterval⌝;
val ⦏open_interval_def⦎ = get_spec⌜OpenInterval⌝;
val ⦏open_ℝ_def⦎ = get_spec⌜Open⋎R⌝;
val ⦏closed_ℝ_def⦎ = get_spec⌜Closed⋎R⌝;
val ⦏compact_ℝ_def⦎ = get_spec⌜Compact⋎R⌝;
val ⦏factorial_def⦎ = get_spec⌜$!⌝;
val ⦏lim_infinity_def⦎ = get_spec ⌜$-+#>⌝;
val ⦏lim_right_def⦎ = get_spec ⌜$+#->⌝;
val ⦏div_infinity_def⦎ = get_spec ⌜$-+#>+#⌝;
=TEX
=SML
val ⦏tan_def⦎ = get_spec ⌜Tan⌝;
val ⦏cotan_def⦎ = get_spec ⌜Cotan⌝;
val ⦏sec_def⦎ = get_spec ⌜Sec⌝;
val ⦏cosec_def⦎ = get_spec ⌜Cosec⌝;
val ⦏sinh_def⦎ = get_spec ⌜Sinh⌝;
val ⦏cosh_def⦎ = get_spec ⌜Cosh⌝;
val ⦏tanh_def⦎ = get_spec ⌜Tanh⌝;
val ⦏cotanh_def⦎ = get_spec ⌜Cotanh⌝;
val ⦏sech_def⦎ = get_spec ⌜Sech⌝;
val ⦏cosech_def⦎ = get_spec ⌜Cosech⌝;
val ⦏χ_def⦎ = get_spec ⌜χ⌝;
val ⦏gauge_def⦎ = get_spec ⌜Gauge⌝;
val ⦏tagged_partition_def⦎ = get_spec ⌜TaggedPartition⌝;
val ⦏tagged_partition_def⦎ = get_spec ⌜TaggedPartition⌝;
val ⦏fine_def⦎ = get_spec ⌜$Fine⌝;
val ⦏riemann_sum_def⦎ = get_spec ⌜RiemannSum⌝;
val ⦏int_ℝ_def⦎ = get_spec ⌜$Int⋎R⌝;
val ⦏int_def⦎ = get_spec ⌜$Int⌝;
val ⦏area_def⦎ = get_spec ⌜$Area⌝;
=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Lemmas about Lists and Sets}
=TEX
We also need a few general lemmas about lists:
%%%%
%%%%
=SML
set_goal([], ⌜
	(∀l1 l2 : 'a LIST⦁ Length(l1 @ l2) = Length l1 + Length l2)
∧	(∀l:'a LIST⦁ Length(Rev l) = Length l)
⌝);
a(once_rewrite_tac[taut_rule⌜∀p q⦁ p ∧ q ⇔ p ∧ (p ⇒ q)⌝]);
a(∧_tac THEN1 (REPEAT strip_tac THEN list_induction_tac⌜l1:'a LIST⌝ THEN
	asm_rewrite_tac[rev_def, length_def, append_def] THEN PC_T1 "lin_arith" prove_tac[]));
a(REPEAT strip_tac THEN list_induction_tac⌜l:'a LIST⌝ THEN
	asm_rewrite_tac[rev_def, length_def] THEN PC_T1 "lin_arith" prove_tac[]);
val ⦏length_rev_append_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	∀l: 'a LIST⦁ Length l = 0 ⇔ l = []
⌝);
a(REPEAT strip_tac THEN_TRY asm_rewrite_tac[length_def]);
a(strip_asm_tac (∀_elim⌜l⌝list_cases_thm));
a(all_var_elim_asm_tac1 THEN all_asm_ante_tac THEN rewrite_tac[length_def]);
val ⦏length_eq_0_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	∀l1 l2 l3:'a LIST⦁ (l1 @ l2) @ l3 = l1 @ l2 @ l3
⌝);
a(REPEAT strip_tac THEN list_induction_tac⌜l1:'a LIST⌝ THEN
	asm_rewrite_tac[append_def]);
val ⦏append_assoc_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	∀l⦁ [] @ l = l ∧ l @ [] = l
⌝);
a(rewrite_tac[append_def]
	THEN REPEAT strip_tac THEN list_induction_tac⌜l:'a LIST⌝ THEN
	asm_rewrite_tac[append_def]);
val ⦏append_empty_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	∀l1 l2 ⦁ Rev (l1 @ l2) = Rev l2 @ Rev l1
⌝);
a(REPEAT strip_tac THEN list_induction_tac⌜l1:'a LIST⌝ THEN
	asm_rewrite_tac[rev_def, append_def, append_assoc_thm, append_empty_thm]);
val ⦏rev_append_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	∀l1 l2 ⦁ l1 @ l2 = [] ⇔ l1 = [] ∧ l2 = []
⌝);
a(∀_tac THEN list_induction_tac⌜l1: 'a LIST⌝ THEN asm_rewrite_tac[append_def]);
val ⦏append_eq_empty_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	∀l ⦁ Rev l = [] ⇔ l = []
⌝);
a(∀_tac THEN list_induction_tac⌜l: 'a LIST⌝ THEN asm_rewrite_tac[append_eq_empty_thm, rev_def]);
val ⦏rev_eq_empty_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	∀l ⦁ Rev(Rev l) = l
⌝);
a(∀_tac THEN list_induction_tac⌜l: 'a LIST⌝ THEN
	asm_rewrite_tac[rev_def, rev_append_thm, append_empty_thm, append_def]);
val ⦏rev_rev_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	∀c n⦁ Rev ((λm⦁ c) To n) = (λm⦁ c) To n
⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝ THEN
	asm_rewrite_tac[rev_def, to_def, rev_append_thm]);
a(rewrite_tac[append_def]);
a(POP_ASM_T discard_tac THEN induction_tac⌜n:ℕ⌝ THEN
	asm_rewrite_tac[to_def, append_def]);
a(LEMMA_T ⌜∀c l1 l2⦁ Cons c (l1 @ l2) = Cons c l1 @ l2⌝ asm_rewrite_thm_tac);
a(REPEAT strip_tac THEN list_induction_tac ⌜l1:'a LIST⌝
	THEN asm_rewrite_tac[append_def]);
val ⦏rev_const_to_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	(∀f n⦁ Length(f To n) = n)
⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝ THEN
	asm_rewrite_tac[length_rev_append_thm, length_def, to_def]);
val ⦏length_to_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	(∀f:'a → 'b; l⦁ Length(Map f l) = Length l)
⌝);
a(REPEAT strip_tac THEN list_induction_tac⌜l:'a LIST⌝ THEN
	asm_rewrite_tac[length_def, map_def]);
val ⦏length_map_thm⦎ = pop_thm();
=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Polynomials}
%%%%
%%%%
%%%%
%%%%
Now we will show that any polynomial can be represented by a list of coefficients.
The first part of the proof follows a pattern which will be repeated several times.
First we prove something for constant functions, then for the identity functions,
then for sums and products possibly on the assumption that the ``something'' holds for
the operands. In this case ``something'' is the existence of a list of
coefficients that represent a function, which we give explicitly for later use.

Constants \ldots
%%%%
%%%%
=SML

val ⦏const_eval_thm⦎ = save_thm ( "const_eval_thm", (
set_goal([], ⌜∀c⦁(λx⦁c) = PolyEval [c]⌝);
a(rewrite_tac[poly_eval_def]);
pop_thm()
));

=TEX
\ldots identity function \ldots
%%%%
%%%%
=SML

val ⦏id_eval_thm⦎ = save_thm ( "id_eval_thm", (
set_goal([], ⌜(λx⦁x) = PolyEval [ℕℝ 0; ℕℝ 1]⌝);
a(rewrite_tac[poly_eval_def]);
pop_thm()
));

=TEX
\ldots sums \ldots
%%%%
%%%%
=SML

val ⦏plus_eval_thm⦎ = save_thm ( "plus_eval_thm", (
set_goal([], ⌜∀l1 l2⦁
	(λx⦁PolyEval l1 x + PolyEval l2 x) =
	PolyEval (PlusCoeffs l1 l2)⌝);
a(strip_tac);
a(list_induction_tac⌜l1⌝ THEN rewrite_tac[plus_coeffs_def, poly_eval_def]);
a(REPEAT strip_tac);
a(list_induction_tac⌜l2⌝ THEN rewrite_tac[plus_coeffs_def, poly_eval_def]);
a(DROP_NTH_ASM_T 2 (rewrite_thm_tac o conv_rule (BINDER_C eq_sym_conv)));
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
\ldots and products, which in this case require a little lemma first:
%%%%
%%%%
=SML

val ⦏const_times_eval_thm⦎ = save_thm ( "const_times_eval_thm", (
set_goal([], ⌜∀c l⦁(λx⦁c * PolyEval l x) = PolyEval (Map (λy⦁c * y) l)⌝);
a(REPEAT strip_tac);
a(list_induction_tac⌜l⌝ THEN rewrite_tac[map_def, poly_eval_def]);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_eval_thm⦎ = save_thm ( "times_eval_thm", (
set_goal([], ⌜∀l1 l2⦁
	(λx⦁PolyEval l1 x * PolyEval l2 x) =
	PolyEval (TimesCoeffs l1 l2)⌝);
a(strip_tac);
a(list_induction_tac⌜l1⌝ THEN
	rewrite_tac[times_coeffs_def, poly_eval_def, plus_coeffs_def]);
a(REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[]));
a(rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv) plus_eval_thm,
	conv_rule (ONCE_MAP_C eq_sym_conv) const_times_eval_thm,
	poly_eval_def]);
a(conv_tac (RANDS_C ℝ_anf_conv));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
We can now show that the set of all polynomial functions is the
range of the polynomial evaluation function. I.e., a function
is polynomial iff. it can be represented by a list of coefficients.
We prove the two inclusions separately:
%%%%
%%%%
=SML
set_goal([], ⌜{f | ∃l⦁ f = PolyEval l} ⊆ PolyFunc⌝);
a(pure_rewrite_tac[poly_func_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN list_induction_tac⌜l⌝);
(* *** Goal "1" *** *)
a(list_spec_nth_asm_tac 4 [⌜ℕℝ 0⌝]);
a(LEMMA_T ⌜PolyEval [] = (λx⦁ ℕℝ 0)⌝ asm_rewrite_thm_tac
	THEN1 rewrite_tac[poly_eval_def]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(LEMMA_T ⌜PolyEval (Cons x l) = (λt⦁ (λu⦁x) t + (λv⦁ (λw⦁w)v * PolyEval l v)t)⌝
	pure_rewrite_thm_tac THEN1 rewrite_tac[poly_eval_def]);
a(GET_NTH_ASM_T 3 bc_thm_tac THEN strip_tac THEN1 asm_rewrite_tac[]);
a(GET_NTH_ASM_T 2 bc_thm_tac THEN strip_tac THEN asm_rewrite_tac[]);
val ⦏poly_eval_⊆_poly_thm⦎ = pop_thm ();
=TEX
For the reverse inclusion, and for later use, it is convenient
to prove an induction theorem for polynomials and use it
to derive an induction tactic:
%%%%
%%%%
=SML

val ⦏poly_induction_thm⦎ = save_thm ( "poly_induction_thm", (
set_goal([], ⌜∀p⦁
		(∀c⦁p(λx⦁c))
	∧	(p(λx⦁x))
	∧	(∀f g⦁p f ∧ p g ⇒  p(λx⦁f x + g x))
	∧	(∀f g⦁p f ∧ p g ⇒ p(λx⦁f x * g x))
	⇒	(∀h⦁ h ∈ PolyFunc ⇒ p h)
⌝);
a(rewrite_tac[poly_func_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(PC_T1 "sets_ext1" POP_ASM_T (strip_asm_tac o ∀_elim ⌜{h | p h}⌝)
	THEN1 asm_prove_tac[] THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
Now the tactic, which expects a term of the form $f \in \mbox{\it PolyFunc}$ to
be in the assumptions (where $f$ is the induction variable).
%%%%
%%%%
=SML
fun ⦏poly_induction_tac⦎ (tm : TERM) : TACTIC = (
	if not (is_var tm andalso type_of tm =: ⓣℝ → ℝ⌝)
	then term_fail "poly_induction_tac" 999001 [tm]
	else ( fn(asms, conc) =>
	let	val asm = find asms (fn t =>  
			let	val (x, s) = dest_bin_op "" 0 "∈" t;
			in	x =$ tm andalso s =$ ⌜PolyFunc⌝
			end	handle Fail _ => false)
			handle Fail _ => fail "poly_induction_tac" 999002 [];
	in	if not (is_free_in tm conc)
			then term_fail "poly_induction_tac" 999003 [tm]
		else if any (asms drop (fn t => t =$ asm)) (is_free_in tm)
			then term_fail "poly_induction_tac" 999004 [tm]
		else	(asm_ante_tac asm THEN gen_induction_tac1 poly_induction_thm) (asms, conc)
	end
	)
);
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜PolyFunc ⊆ {f | ∃l⦁ f = PolyEval l}⌝);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(poly_induction_tac⌜x⌝);
(* *** Goal "1" *** *)
a(ante_tac const_eval_thm THEN prove_tac[]);
(* *** Goal "2" *** *)
a(ante_tac id_eval_thm THEN prove_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜PlusCoeffs l l'⌝ THEN pure_asm_rewrite_tac[plus_eval_thm] THEN strip_tac);
(* *** Goal "4" *** *)
a(∃_tac⌜TimesCoeffs l l'⌝ THEN pure_asm_rewrite_tac[times_eval_thm] THEN strip_tac);
val ⦏poly_⊆_poly_eval_thm⦎ = pop_thm ();
=TEX
%%%%
%%%%
=SML

val ⦏poly_func_eq_poly_eval_thm⦎ = save_thm ( "poly_func_eq_poly_eval_thm", (
set_goal([], ⌜PolyFunc = {f | ∃l⦁ f = PolyEval l}⌝);
a(rewrite_tac[poly_⊆_poly_eval_thm, poly_eval_⊆_poly_thm,
	pc_rule1 "sets_ext1" prove_rule[] ⌜∀a b⦁a = b ⇔ a ⊆ b ∧ b ⊆ a⌝]);
pop_thm()
));

=TEX
For convenience, it is useful to have the theorems that say that the
different kinds of polynomial construction do lead to polynomial functions:
%%%%
%%%%
=SML

val ⦏const_poly_func_thm⦎ = save_thm ( "const_poly_func_thm", (
set_goal([], ⌜∀c⦁(λx⦁c) ∈ PolyFunc⌝);
a(pure_rewrite_tac[const_eval_thm, poly_func_eq_poly_eval_thm]);
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏id_poly_func_thm⦎ = save_thm ( "id_poly_func_thm", (
set_goal([], ⌜(λx⦁x) ∈ PolyFunc⌝);
a(pure_rewrite_tac[id_eval_thm, poly_func_eq_poly_eval_thm]);
a(PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_poly_func_thm⦎ = save_thm ( "plus_poly_func_thm", (
set_goal([], ⌜∀f g⦁ f ∈ PolyFunc ∧ g ∈ PolyFunc ⇒ (λx⦁f x + g x) ∈ PolyFunc⌝);
a(pure_rewrite_tac[poly_func_eq_poly_eval_thm] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN pure_rewrite_tac[plus_eval_thm]
	THEN PC_T1 "predicates" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_poly_func_thm⦎ = save_thm ( "times_poly_func_thm", (
set_goal([], ⌜∀f g⦁ f ∈ PolyFunc ∧ g ∈ PolyFunc ⇒ (λx⦁f x * g x) ∈ PolyFunc⌝);
a(pure_rewrite_tac[poly_func_eq_poly_eval_thm] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN pure_rewrite_tac[times_eval_thm]
	THEN PC_T1 "predicates" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏comp_poly_func_thm⦎ = save_thm ( "comp_poly_func_thm", (
set_goal([], ⌜∀f g⦁ f ∈ PolyFunc ∧ g ∈ PolyFunc ⇒ (λx⦁f(g x)) ∈ PolyFunc⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(intro_∀_tac(⌜g⌝, ⌜g⌝) THEN poly_induction_tac⌜f⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[const_poly_func_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[η_axiom]);
(* *** Goal "3" *** *)
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
a(rewrite_tac[] THEN ALL_FC_T (MAP_EVERY ante_tac) [plus_poly_func_thm]);
a(rewrite_tac[] THEN taut_tac);
(* *** Goal "4" *** *)
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
a(rewrite_tac[] THEN ALL_FC_T (MAP_EVERY ante_tac) [times_poly_func_thm]);
a(rewrite_tac[] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏poly_eval_append_thm⦎ = save_thm ( "poly_eval_append_thm", (
set_goal([], ⌜
	∀l1 l2 x⦁ PolyEval (l1 @ l2) x = PolyEval l1 x + x^Length l1 * PolyEval l2 x
⌝);
a(REPEAT strip_tac THEN list_induction_tac⌜l1:ℝ LIST⌝ THEN
	asm_rewrite_tac[rev_def, poly_eval_def, length_def, ℝ_ℕ_exp_def, append_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
We are now going to prove various identities for polynomials.
The following result gives the rule for evaluating a polynomial starting with the
leading term.
%%%%
%%%%
=SML

val ⦏poly_eval_rev_thm⦎ = save_thm ( "poly_eval_rev_thm", (
set_goal([], ⌜
	(∀x⦁ PolyEval (Rev []) x = ℕℝ 0)
∧	(∀c l x⦁ PolyEval (Rev (Cons c l)) x = c*x^Length l + PolyEval (Rev l) x)
⌝);
a(REPEAT strip_tac THEN1 rewrite_tac[rev_def, poly_eval_def]);
a(intro_∀_tac(⌜c⌝, ⌜c⌝) THEN list_induction_tac⌜l⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[rev_def, poly_eval_def, length_def, ℝ_ℕ_exp_def, append_def]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
a(rewrite_tac[rev_def, poly_eval_def, length_def, ℝ_ℕ_exp_def, append_def,
	poly_eval_append_thm, length_rev_append_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
The following is the identity for the difference of two like powers:
\[
(x-y)(x^n + yx^{n-1} + \ldots + y^jx^{n-j} + \ldots y^n) = x^{n+1} - y^{n+1}
\]
%%%%
%%%%
=SML

val ⦏poly_diff_powers_thm⦎ = save_thm ( "poly_diff_powers_thm", (
set_goal([], ⌜
	∀n x y⦁ (x - y)*PolyEval (Rev((λm⦁y^m) To (n+1))) x = x^(n+1) - y^(n+1)
⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝);
(* *** Goal "1" *** *)
a(pure_rewrite_tac[to_def, ℝ_ℕ_exp_def, append_def, poly_eval_def, rev_def]);
a(rewrite_tac[]);
(* *** Goal "2" *** *)
a(pure_once_rewrite_tac[to_def, ℝ_ℕ_exp_def]);
a(pure_asm_rewrite_tac[rev_append_thm, rev_def, poly_eval_append_thm,
	append_empty_thm, ℝ_times_plus_distrib_thm, length_def, ℝ_ℕ_exp_def,
	∀_elim⌜x * ℕℝ 1⌝ ℝ_times_order_thm]);
a(rewrite_tac[poly_eval_def, ℝ_ℕ_exp_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏length_plus_coeffs_thm⦎ = save_thm ( "length_plus_coeffs_thm", (
set_goal([], ⌜
	∀l1 l2⦁ Length(PlusCoeffs l1 l2) = if Length l2 < Length l1 then Length l1 else Length l2
⌝);
a(∀_tac THEN list_induction_tac⌜l1:ℝ LIST⌝ THEN1 rewrite_tac[length_def, plus_coeffs_def]);
a(REPEAT strip_tac THEN list_induction_tac⌜l2:ℝ LIST⌝ THEN
	 asm_rewrite_tac[length_def, plus_coeffs_def]);
a(cases_tac⌜Length l2 < Length l1⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The following is the special case of polynomial division in which the divisor
is linear. In this special case, we do not need the notion of the degree of
a polynomial to state the result (which is very fortunate, since we plan to
use this in deriving the theory of polynomial degrees). In informal notation
the result is that if $f$ is any polynomial (the one whose coefficient
list is given by $l1$ in the formal statement), then there is another polynomial
$g$ (the one whose coefficients are given by $l2$ in the formal statement)
with a shorter list of coefficients and such that $f(x) = (x-a)g(x) + r$
for some real number $r$.

The proof below follows a slightly different pattern from the text book
proof, which works by induction on the degree of the dividend (to divide
$f = a_{n+1}x^{n+1} + a_{n}x^{n} + \ldots + a_0$ by $x - c$, one has
$f - a_nx^{n}(x-c) = g$ where $g$ has degree less than that of $f$ and
one proceeds by induction on the degrees). Here, we use list induction
on the list of coefficients (reversed, i.e., leading coefficient first).
If $f =a_{n+1}x^n + a_{n}x^{n} + \ldots + a_0$, then by a list induction,
we can write $h = a_{n}x^{n} + \ldots + a_0$ as $(x-c)h_1 + r_1$
where the list of coefficients for $h_1$ is shorter than that for
$h$ and we can write $a_{n+1}x^{n+1}$ as $a_{n+1}(x - c)(x^n + cx^{n-1} + \ldots + c^n) + a_{n+1}c^{n+1}$, by the identity for the difference of two like powers. Adding
these representations for $h$ and $a_{n+1}x^{n+1}$ gives the required representation
for $f$. There is not much to choose between the two approaches except that this one
involves less fiddling around with lists of coefficients given the tools we have to hand.

%%%%
%%%%
=SML

val ⦏poly_linear_div_thm⦎ = save_thm ( "poly_linear_div_thm", (
set_goal([], ⌜
	∀l1 c⦁ ¬l1 = []
⇒	∃l2 r⦁
		Length l2 < Length l1 
	∧	(λx⦁ PolyEval l1 x) = (λx⦁ (x - c)*PolyEval l2 x + r)
⌝);
a(lemma_tac⌜
	∀l1 c⦁ ¬l1 = []
⇒	∃l2 r⦁
		Length l2 < Length l1 
	∧	(λx⦁ PolyEval (Rev l1) x) = (λx⦁ (x - c)*PolyEval l2 x + r)⌝);
(* *** Goal "1" *** *)
a(REPEAT ∀_tac THEN list_induction_tac⌜l1 : ℝ LIST⌝ THEN1 rewrite_tac[]);
(* *** Goal "1.1" *** *)
a(all_var_elim_asm_tac1 THEN REPEAT strip_tac);
a(∃_tac⌜[]⌝ THEN ∃_tac⌜x⌝ THEN
	rewrite_tac[length_def, rev_def, poly_eval_def, append_empty_thm]);
(* *** Goal "1.2" *** *)
a(pure_rewrite_tac[poly_eval_rev_thm]);
a(REPEAT strip_tac);
a(lemma_tac⌜∃m⦁m + 1 = Length l1⌝ THEN1
	(GET_NTH_ASM_T 3 ante_tac THEN rewrite_tac[less_def, ≤_def]
	THEN REPEAT strip_tac THEN ∃_tac⌜Length l2 + i⌝
	THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(∃_tac⌜PlusCoeffs(Map (λt⦁x*t) (Rev ((λ j⦁ c ^ j) To (m + 1)))) l2⌝
	THEN ∃_tac⌜x*c^(m+1) + r⌝);
a(REPEAT strip_tac THEN1
	asm_rewrite_tac[length_to_thm, length_plus_coeffs_thm,
		length_rev_append_thm, length_def, length_map_thm]);
a(pure_rewrite_tac (map (conv_rule (ONCE_MAP_C eq_sym_conv))
		[const_times_eval_thm, plus_eval_thm]));
a(GET_NTH_ASM_T 3 (pure_rewrite_thm_tac o rewrite_rule[]));
a(PC_T1 "predicates" rewrite_tac[]);
a(pure_asm_rewrite_tac[∀_elim⌜x⌝ℝ_times_order_thm,
	ℝ_times_plus_distrib_thm, poly_diff_powers_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜¬Rev l1 = []⌝ THEN1 asm_rewrite_tac[rev_eq_empty_thm]);
a(list_spec_nth_asm_tac 3 [⌜Rev l1⌝, ⌜c⌝]);
a(DROP_NTH_ASM_T 2 (asm_tac o rewrite_rule[length_rev_append_thm]));
a(DROP_NTH_ASM_T 2 (asm_tac o rewrite_rule[rev_rev_thm]));
a(∃_tac ⌜l2⌝ THEN ∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The so-called remainder theorem is just the above theorem with the explicit formula $f(c)$ for the remainder.
%%%%
%%%%
=SML

val ⦏poly_remainder_thm⦎ = save_thm ( "poly_remainder_thm", (
set_goal([], ⌜∀l1 c⦁
	¬l1 = []
⇒	∃l2⦁
		Length l2 < Length l1 
	∧	(λx⦁ PolyEval l1 x) = (λx⦁ (x - c)*PolyEval l2 x + PolyEval l1 c)
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[poly_linear_div_thm]);
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜c⌝));
a(∃_tac⌜l2⌝ THEN asm_rewrite_tac[]);
a(POP_ASM_T (ante_tac o ∀_elim⌜c⌝));
a(rewrite_tac[]);
a(STRIP_T rewrite_thm_tac);
pop_thm()
));

=TEX
The so-called factor theorem is the special case when the remainder vanishes:
%%%%
%%%%
=SML

val ⦏poly_factor_thm⦎ = save_thm ( "poly_factor_thm", (
set_goal([], ⌜∀l1 c⦁
	¬l1 = []
∧	PolyEval l1 c = ℕℝ 0
⇒	∃l2⦁
		Length l2 < Length l1 
	∧	(λx⦁ PolyEval l1 x) = (λx⦁ (x - c)*PolyEval l2 x)
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[poly_remainder_thm]);
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜c⌝));
a(∃_tac⌜l2⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
We can now prove that a polynomial which is not identically zero has only finitely many
roots:
%%%%
%%%%
=SML

val ⦏poly_roots_finite_thm⦎ = save_thm ( "poly_roots_finite_thm", (
set_goal([], ⌜∀f c⦁
	f ∈ PolyFunc
∧	¬f c = ℕℝ 0
⇒	Roots f ∈ Finite
⌝);
a(rewrite_tac[roots_def]
	THEN lemma_tac⌜∀m l c⦁ Length l ≤ m ∧ ¬PolyEval l c = ℕℝ 0
⇒	{ x | PolyEval l x = ℕℝ 0 } ∈ Finite
⌝);
(* *** Goal "1" *** *)
a(∀_tac THEN induction_tac⌜m:ℕ⌝ THEN1 REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(POP_ASM_T ante_tac THEN all_fc_tac[length_eq_0_thm] THEN asm_rewrite_tac[poly_eval_def]);
(* *** Goal "1.2" *** *)
a(REPEAT ∀_tac THEN ⇒_tac);
a(cases_tac⌜Length l ≤ m⌝ THEN1
	(GET_NTH_ASM_T 4 bc_thm_tac THEN asm_prove_tac[]));
a(lemma_tac ⌜Length l = m + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(lemma_tac⌜¬l = []⌝ THEN1
	(contr_tac THEN all_var_elim_asm_tac1 THEN all_asm_ante_tac
	THEN rewrite_tac[length_def]));
a(cases_tac ⌜{x|PolyEval l x = ℕℝ 0} = {}⌝ THEN1 asm_rewrite_tac[empty_finite_thm]);
a(POP_ASM_T (PC_T1 "sets_ext"  strip_asm_tac));
a(cases_tac⌜x = c⌝ THEN1 all_var_elim_asm_tac);
a(strip_asm_tac(rewrite_rule[] (list_∀_elim[⌜l⌝, ⌜x⌝] poly_linear_div_thm)));
a(TOP_ASM_T (ante_tac o ∀_elim⌜x⌝) THEN conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(GET_NTH_ASM_T 4 rewrite_thm_tac THEN  strip_tac THEN all_var_elim_asm_tac1);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[]));
a(lemma_tac⌜Length l2 ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜{x|PolyEval l x = ℕℝ 0} = {x} ∪ {x|PolyEval l2 x = ℕℝ 0}⌝ rewrite_thm_tac);
(* *** Goal "1.2.1" *** *)
a(rename_tac [] THEN DROP_NTH_ASM_T 2 rewrite_thm_tac);
a(PC_T1 "sets_ext1" rewrite_tac[ℝ_times_eq_0_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁a + ~ b = ℕℝ 0 ⇔ a = b⌝]);
(* *** Goal "1.2.2" *** *)
a(bc_thm_tac singleton_∪_finite_thm);
a(GET_NTH_ASM_T 11 bc_thm_tac THEN REPEAT strip_tac);
a(∃_tac⌜c⌝ THEN contr_tac);
a(DROP_NTH_ASM_T  10 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext" rewrite_tac[poly_func_eq_poly_eval_thm] THEN
	REPEAT ∀_tac THEN ⇒_tac);
a(asm_rewrite_tac[] THEN GET_NTH_ASM_T 3 bc_thm_tac);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a(∃_tac⌜c⌝ THEN ∃_tac⌜Length l⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Lemmas about Real Arithmetic}
%%%%
%%%%
%%%%
%%%%
\subsubsection{Lemmas about the Absolute Value Function}
%%%%
%%%%
%%%%
%%%%
We will need a number of facts about absolute values etc.
=TEX
Absolute values are non-negative:
=TEX
%%%%
%%%%
=SML

val ⦏ℝ_0_≤_abs_thm⦎ = save_thm ( "ℝ_0_≤_abs_thm", (
set_goal([], ⌜∀x:ℝ⦁ ℕℝ 0 ≤ Abs x⌝);
a(REPEAT strip_tac THEN rewrite_tac[ℝ_abs_def]);
a(cases_tac ⌜ℕℝ 0 ≤ x⌝
	THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Next, the triangle inequality:
%%%%
%%%%
=SML

val ⦏ℝ_abs_plus_thm⦎ = save_thm ( "ℝ_abs_plus_thm", (
set_goal([], ⌜∀x y:ℝ⦁ Abs(x + y) ≤ Abs x + Abs y⌝);
a(REPEAT strip_tac THEN rewrite_tac[ℝ_abs_def]);
a(MAP_EVERY cases_tac [⌜ℕℝ 0 ≤ x⌝, ⌜ℕℝ 0 ≤ y⌝, ⌜ℕℝ 0 ≤ x + y⌝]
	THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
\ldots and the triangle inequality for subtraction:
%%%%
%%%%
=SML

val ⦏ℝ_abs_subtract_thm⦎ = save_thm ( "ℝ_abs_subtract_thm", (
set_goal([], ⌜∀x y:ℝ⦁ Abs(x - y) ≤ Abs x + Abs y⌝);
a(REPEAT strip_tac THEN rewrite_tac[ℝ_abs_def]);
a(MAP_EVERY cases_tac [⌜ℕℝ 0 ≤ x⌝, ⌜ℕℝ 0 ≤ y⌝, ⌜ℕℝ 0 ≤ x + ~y⌝]
	THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));


val ⦏ℝ_abs_plus_minus_thm⦎ = save_thm ("ℝ_abs_plus_minus_thm", rewrite_rule[]ℝ_abs_subtract_thm);
=TEX
\ldots and again in a formulation that is nice for back-chaining:
%%%%
%%%%
=SML

val ⦏ℝ_abs_diff_bounded_thm⦎ = save_thm ( "ℝ_abs_diff_bounded_thm", (
set_goal([], ⌜∀x y z:ℝ⦁ ℕℝ 0 < z ⇒ (Abs (x + ~y) < z ⇔ y + ~z <  x ∧ x < y + z)⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN cases_tac⌜ℕℝ 0 ≤ x + ~y⌝ THEN
	asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_abs_plus_bc_thm⦎ = save_thm ( "ℝ_abs_plus_bc_thm", (
set_goal([], ⌜∀x y z:ℝ⦁ Abs x ≤ Abs (y + z) ⇒ Abs x ≤ Abs y + Abs z⌝);
a(REPEAT strip_tac THEN bc_thm_tac ℝ_≤_trans_thm);
a(∃_tac⌜Abs(y + z)⌝ THEN asm_rewrite_tac[ℝ_abs_plus_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_abs_abs_minus_thm⦎ = save_thm ( "ℝ_abs_abs_minus_thm", (
set_goal([], ⌜∀x y:ℝ⦁ Abs (Abs x - Abs y) ≤ Abs (x - y)⌝);
a(REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜x - y⌝, ⌜y⌝]ℝ_abs_plus_thm) THEN rewrite_tac[ℝ_plus_assoc_thm]);
a(strip_tac THEN lemma_tac ⌜Abs x + ~(Abs y) ≤ Abs (x + ~y)⌝ THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ante_tac(list_∀_elim[⌜y - x⌝, ⌜x⌝]ℝ_abs_plus_thm) THEN rewrite_tac[ℝ_plus_assoc_thm]);
a(strip_tac THEN LEMMA_T ⌜Abs y + ~(Abs x) ≤ Abs (~(~y + x))⌝ ante_tac THEN1
	(rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(rewrite_tac[ℝ_abs_minus_thm, pc_rule1 "ℝ_lin_arith" prove_rule[]⌜~y + x = x + ~y⌝]);
a(strip_tac THEN conv_tac(LEFT_C (once_rewrite_conv[ℝ_abs_def])));
a(cases_tac⌜ℕℝ 0 ≤ Abs x + ~(Abs y)⌝ THEN asm_rewrite_tac[] THEN_TRY
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The absolute value function is idempotent:
=TEX
%%%%
%%%%
=SML

val ⦏ℝ_abs_abs_thm⦎ = save_thm ( "ℝ_abs_abs_thm", (
set_goal([], ⌜∀x:ℝ⦁ Abs(Abs x) = Abs(x)⌝);
a(REPEAT strip_tac);
a(conv_tac (LEFT_C (once_rewrite_conv[ℝ_abs_def])));
a(rewrite_tac [ℝ_0_≤_abs_thm]);
pop_thm()
));

=TEX
Absolute values commute with multiplication:
%%%%
%%%%
=SML

val ⦏ℝ_abs_times_thm⦎ = save_thm ( "ℝ_abs_times_thm", (
set_goal([], ⌜∀x y:ℝ⦁ Abs(x * y) = Abs x * Abs y⌝);
a(lemma_tac ⌜∀x y:ℝ⦁ ℕℝ 0 ≤ x ∧ ℕℝ 0 ≤ y ⇒ Abs(x * y) = Abs x * Abs y⌝
	THEN REPEAT strip_tac THEN1 (all_fc_tac[ℝ_0_≤_0_≤_times_thm]
		THEN asm_rewrite_tac[ℝ_abs_def]));
a(cases_tac⌜ℕℝ 0 ≤ x⌝ THEN cases_tac⌜ℕℝ 0 ≤ y⌝ THEN1 all_asm_fc_tac[]);
(* *** Goal "1" *** *)
a(lemma_tac⌜ℕℝ 0 ≤ ~y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_ASM_FC_T (MAP_EVERY ante_tac)[]);
a(LEMMA_T ⌜x* ~y = ~(x*y)⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(rewrite_tac[ℝ_abs_minus_thm] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(lemma_tac⌜ℕℝ 0 ≤ ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_ASM_FC_T (MAP_EVERY ante_tac)[]);
a(LEMMA_T ⌜~x * y = ~(x*y)⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(rewrite_tac[ℝ_abs_minus_thm] THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(lemma_tac⌜ℕℝ 0 ≤ ~x ∧ ℕℝ 0 ≤ ~y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_ASM_FC_T (MAP_EVERY ante_tac)[]);
a(LEMMA_T ⌜~x * ~y = (x*y)⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(rewrite_tac[ℝ_abs_minus_thm] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
Absolute values commute with powers:
%%%%
%%%%
=SML

val ⦏ℝ_abs_ℝ_ℕ_exp_thm⦎ = save_thm ( "ℝ_abs_ℝ_ℕ_exp_thm", (
set_goal([], ⌜∀x:ℝ; m:ℕ⦁ Abs(x ^ m) = Abs x ^ m⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝
	THEN asm_rewrite_tac[ℝ_ℕ_exp_def, ℝ_abs_times_thm]);
pop_thm()
));

=TEX
Only 0 has absolute value 0:
%%%%
%%%%
=SML

val ⦏ℝ_abs_eq_0_thm⦎ = save_thm ( "ℝ_abs_eq_0_thm", (
set_goal([], ⌜∀x⦁ Abs x = ℕℝ 0 ⇔ x = ℕℝ 0⌝);
a(strip_tac THEN rewrite_tac[ℝ_abs_def]);
a(cases_tac⌜ℕℝ 0 ≤ x⌝ THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
Only 0 has a non-positive absolute value:
%%%%
%%%%
=SML

val ⦏ℝ_abs_≤_0_thm⦎ = save_thm ( "ℝ_abs_≤_0_thm", (
set_goal([], ⌜∀x⦁ Abs x ≤ ℕℝ 0 ⇔ x = ℕℝ 0⌝);
a(strip_tac THEN rewrite_tac[ℝ_abs_def]);
a(cases_tac⌜ℕℝ 0 ≤ x⌝ THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_abs_0_thm⦎ = save_thm ( "ℝ_abs_0_thm", (
set_goal([], ⌜Abs (ℕℝ 0) = ℕℝ 0⌝);
a(rewrite_tac[]);
pop_thm()
));

=TEX
Absolute values commute with reciprocal:
%%%%
%%%%
=SML

val ⦏ℝ_abs_recip_thm⦎ = save_thm ( "ℝ_abs_recip_thm", (
set_goal([], ⌜∀x⦁ ¬x = ℕℝ 0 ⇒ Abs (x ⋏-⋏1) = (Abs x) ⋏-⋏1⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜Abs(x * x ⋏-⋏1) = ℕℝ 1⌝ ante_tac THEN1
	(ALL_FC_T rewrite_tac[ℝ_times_recip_thm]));
a(rewrite_tac[ℝ_abs_times_thm] THEN strip_tac);
a(lemma_tac⌜¬Abs x = ℕℝ 0⌝THEN1 asm_rewrite_tac[ℝ_abs_eq_0_thm]);
a(LEMMA_T⌜(Abs x * (Abs x) ⋏-⋏1) * Abs(x ⋏-⋏1) = (Abs x)⋏-⋏1⌝ ante_tac THEN1
	asm_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b c:ℝ⦁(a*b)*c = b*a*c⌝]);
a(ALL_FC_T rewrite_tac[ℝ_times_recip_thm]);
pop_thm()
));

=TEX
Squares of absolute values are equal to squares:
%%%%
%%%%
=SML

val ⦏ℝ_abs_squared_thm⦎ = save_thm ( "ℝ_abs_squared_thm", (
set_goal([], ⌜∀x:ℝ⦁ Abs x ^ 2 = x ^ 2⌝);
a(REPEAT strip_tac);
a(pure_rewrite_tac[prove_rule[]⌜2 = (0 + 1) + 1⌝, ℝ_ℕ_exp_def]);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) ℝ_abs_times_thm]);
a(LEMMA_T ⌜ℕℝ 0 ≤ x * x⌝ (fn th => rewrite_tac[ℝ_abs_def, th]));
a(cases_tac⌜ℕℝ 0 ≤ x ⌝ THEN1
	(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN REPEAT strip_tac));
a(lemma_tac⌜ℕℝ 0 ≤ ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜ℕℝ 0 ≤ ~x * ~x ⌝ THEN1
	(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN REPEAT strip_tac));
a(POP_ASM_T ante_tac THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
A monotonicity property for absolute values and multiplication:
%%%%
%%%%
=SML

val ⦏ℝ_abs_less_times_thm⦎ = save_thm ( "ℝ_abs_less_times_thm", (
set_goal([], ⌜∀x t y u:ℝ⦁ Abs x < t ∧ Abs y < u ⇒ Abs x * Abs y < t*u⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜x⌝ ℝ_0_≤_abs_thm));
a(strip_asm_tac (∀_elim⌜y⌝ ℝ_0_≤_abs_thm));
a(lemma_tac⌜ℕℝ 0 < t ∧ ℕℝ 0 < u⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac ⌜Abs x = ℕℝ 0⌝ THEN1 
	(all_fc_tac[ℝ_0_less_0_less_times_thm] THEN asm_rewrite_tac[]));
a(cases_tac ⌜Abs y = ℕℝ 0⌝ THEN1 
	(all_fc_tac[ℝ_0_less_0_less_times_thm] THEN asm_rewrite_tac[]));
a(lemma_tac ⌜ℕℝ 0 < Abs x ∧ ℕℝ 0 < Abs y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_less_trans_thm);
a(∃_tac⌜Abs x * u⌝ THEN REPEAT strip_tac
	THEN1 bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
a(once_rewrite_tac[ℝ_times_comm_thm]
	THEN bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
Non-zero numbers have positive absolute values:
%%%%
%%%%
=SML

val ⦏ℝ_¬_0_abs_thm⦎ = save_thm ( "ℝ_¬_0_abs_thm", (
set_goal([], ⌜∀x⦁ ¬x = ℕℝ 0 ⇔ ℕℝ 0 < Abs x⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 ≤ Abs x⌝ THEN1 rewrite_tac[ℝ_0_≤_abs_thm]);
a(lemma_tac⌜¬ Abs x = ℕℝ 0⌝ THEN1 asm_rewrite_tac[ℝ_abs_eq_0_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀a x b d:ℝ⦁a < x ∧ x < b ∧ ℕℝ 0 < d
⇒	∃c⦁ℕℝ 0 < c ∧ c < d ∧ ∀y⦁Abs(y + ~x) < c ⇒ a < y ∧ y < b⌝);
a(REPEAT strip_tac);
a(∃_tac⌜ (1/2)*
	if	x + ~ a ≤ b + ~ x ∧ x + ~ a ≤ d
	then	x + ~ a
	else if	d ≤ x + ~ a ∧ d ≤ b + ~x
	then	d
	else	b + ~ x ⌝ THEN REPEAT_UNTIL is_⇒ strip_tac
	THEN_TRY(cases_tac⌜ℕℝ 0 ≤ y +  ~x⌝ THEN asm_rewrite_tac[ℝ_abs_def]) THEN
	cases_tac⌜x + ~ a ≤ b + ~ x ∧ x + ~ a ≤ d⌝ THEN
	cases_tac ⌜d ≤ x + ~ a ∧ d ≤ b + ~x⌝ THEN_TRY
	asm_rewrite_tac[] THEN_TRY
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏axbd_thm⦎ = pop_thm ();
=TEX
\subsection{Other Algebraic Lemmas}
Reciprocal of positive reals is order reversing:
%%%%
%%%%
=SML

val ⦏ℝ_less_recip_less_thm⦎ = save_thm ( "ℝ_less_recip_less_thm", (
set_goal([], ⌜∀x y:ℝ⦁ ℕℝ 0 < x ∧ x < y ⇒ y ⋏-⋏1 < x ⋏-⋏1⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜y ⋏-⋏1 * x ⋏-⋏1 * x < y ⋏-⋏1 * x ⋏-⋏1 * y⌝);
(* *** Goal "1" *** *)
a(all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(REPEAT (bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac));
(* *** Goal "2" *** *)
a(lemma_tac⌜¬x = ℕℝ 0 ∧ ¬y = ℕℝ 0⌝ THEN1
	(LIST_GET_NTH_ASM_T [3, 4] (MAP_EVERY ante_tac) THEN
		PC_T1 "ℝ_lin_arith" prove_tac[]));
a(DROP_NTH_ASM_T 3 ante_tac);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜
	y ⋏-⋏1 * x ⋏-⋏1 * x = y ⋏-⋏1 * (x * x ⋏-⋏1)
∧	y ⋏-⋏1 * x ⋏-⋏1 * y = x ⋏-⋏1 * (y * y ⋏-⋏1)⌝]);
a(ALL_FC_T rewrite_tac[ℝ_times_recip_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_abs_≤_less_interval_thm⦎ = save_thm ( "ℝ_abs_≤_less_interval_thm", (
set_goal([], ⌜∀x y⦁
		(Abs x ≤ y ⇔ x ∈ ClosedInterval (~y) y)
	∧	(Abs x < y ⇔ x ∈ OpenInterval (~y) y)
⌝);
a(REPEAT ∀_tac);
a(cases_tac ⌜ℕℝ 0 ≤ x⌝
	THEN asm_rewrite_tac[ℝ_abs_def, open_interval_def, closed_interval_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The following algebraic lemma is used often enough to be worth recording:
it says that, providing both sides are well-defined, $1/x+1/y = (x+y)/xy$.
%%%%
%%%%
=SML

val ⦏ℝ_plus_recip_thm⦎ = save_thm ( "ℝ_plus_recip_thm", (
set_goal([], ⌜∀x y⦁ ¬x = ℕℝ 0 ∧ ¬y = ℕℝ 0 ⇒
	(x ⋏-⋏1 + y ⋏-⋏1) = (x + y) * x ⋏-⋏1 * y ⋏-⋏1⌝);
a(REPEAT strip_tac THEN conv_tac (RIGHT_C ℝ_anf_conv));
a(ALL_FC_T rewrite_tac[ℝ_times_recip_thm]);
a(rewrite_tac[ℝ_times_assoc_thm1] THEN ALL_FC_T rewrite_tac[ℝ_times_recip_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℕℝ_recip_thm⦎ = save_thm ( "ℕℝ_recip_thm", (
set_goal([], ⌜∀m⦁ ℕℝ(m + 1) ⋏-⋏1 ⋏-⋏1 = ℕℝ (m + 1)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜¬ℕℝ (m + 1) = ℕℝ 0⌝ THEN_LIST
	[id_tac, all_fc_tac[ℝ_recip_clauses]]);
a(rewrite_tac[ℕℝ_plus_homomorphism_thm1, ℕℝ_one_one_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℕℝ_0_less_recip_thm⦎ = save_thm ( "ℕℝ_0_less_recip_thm", (
set_goal([], ⌜∀m⦁ ℕℝ 0 < ℕℝ (m + 1) ⋏-⋏1⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < ℕℝ (m+1)⌝ THEN1 rewrite_tac[ℕℝ_0_less_thm]);
a(all_fc_tac[ℝ_0_less_0_less_recip_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℕℝ_recip_not_eq_0_thm⦎ = save_thm ( "ℕℝ_recip_not_eq_0_thm", (
set_goal([], ⌜∀m⦁ ¬ℕℝ (m + 1) ⋏-⋏1 = ℕℝ 0⌝);
a(REPEAT strip_tac);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x⦁ℕℝ 0 < x ⇒ ¬x = ℕℝ 0⌝));
a(rewrite_tac[ℕℝ_0_less_recip_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_0_1_thm⦎ = save_thm ( "ℝ_ℕ_exp_0_1_thm", (
set_goal([], ⌜∀m⦁ ℕℝ 0 ^ (m+1) = ℕℝ 0 ∧ ℕℝ 1 ^ m = ℕℝ 1⌝);
a(∀_tac THEN induction_tac⌜m:ℕ⌝ THEN asm_rewrite_tac[ℝ_ℕ_exp_def]);
pop_thm()
));

=TEX
=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_square_thm⦎ = save_thm ( "ℝ_ℕ_exp_square_thm", (
set_goal([], ⌜∀x:ℝ⦁ x ^ 2 = x * x⌝);
a(pure_rewrite_tac[prove_rule[]⌜2 = (0 + 1) + 1⌝, ℝ_ℕ_exp_def]);
a(rewrite_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_0_less_thm⦎ = save_thm ( "ℝ_ℕ_exp_0_less_thm", (
set_goal([], ⌜∀m:ℕ; x ⦁ ℕℝ 0 < x ⇒ ℕℝ 0 < x^m⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN asm_rewrite_tac[ℝ_ℕ_exp_def]);
a(all_fc_tac[ℝ_0_less_0_less_times_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_1_less_mono_thm⦎ = save_thm ( "ℝ_ℕ_exp_1_less_mono_thm", (
set_goal([], ⌜∀x; m:ℕ⦁ ℕℝ 1 < x ⇒ x^m < x^(m+1) ⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN1 asm_rewrite_tac[ℝ_ℕ_exp_def]);
a(once_rewrite_tac[ℝ_ℕ_exp_def]);
a(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_1_less_mono_thm1⦎ = save_thm ( "ℝ_ℕ_exp_1_less_mono_thm1", (
set_goal([], ⌜∀x; m n:ℕ⦁ℕℝ 1 < x ∧ m < n ⇒ x^m < x^n ⌝);
a(REPEAT ∀_tac THEN induction_tac⌜n:ℕ⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a( lemma_tac⌜n = m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac THEN ALL_FC_T rewrite_tac [ℝ_ℕ_exp_1_less_mono_thm]);
(* *** Goal "2" *** *)
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜x^n⌝ THEN REPEAT strip_tac);
a(ALL_FC_T rewrite_tac [ℝ_ℕ_exp_1_less_mono_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_≤_times_mono_thm⦎ = save_thm ( "ℝ_≤_times_mono_thm", (
set_goal([], ⌜∀x y z ⦁ ℕℝ 0 ≤ x ∧ y ≤ z ⇒ x*y ≤ x*z⌝);
a(rewrite_tac[ℝ_≤_def] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(all_fc_tac[ℝ_times_mono_thm]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_¬_eq_0_thm⦎ = save_thm ( "ℝ_ℕ_exp_¬_eq_0_thm", (
set_goal([], ⌜∀m:ℕ; x ⦁ ¬x = ℕℝ 0 ⇒ ¬ x^m = ℕℝ 0⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN asm_rewrite_tac[ℝ_ℕ_exp_def]);
a(rewrite_tac[ℝ_times_eq_0_thm] THEN REPEAT strip_tac);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_plus_thm⦎ = save_thm ( "ℝ_ℕ_exp_plus_thm", (
set_goal([], ⌜∀x:ℝ; m n:ℕ⦁ x^(m+n) = x^m * x^n⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝ THEN
	asm_rewrite_tac[ℝ_ℕ_exp_def, plus_assoc_thm1]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_times_thm⦎ = save_thm ( "ℝ_ℕ_exp_times_thm", (
set_goal([], ⌜∀x y:ℝ; m:ℕ⦁ (x*y)^m = x^m * y^m⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN rewrite_tac[ℝ_ℕ_exp_def]);
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_recip_thm⦎ = save_thm ( "ℝ_ℕ_exp_recip_thm", (
set_goal([], ⌜∀m:ℕ; x ⦁ ¬x = ℕℝ 0 ⇒ (x^m)⋏-⋏1 = (x ⋏-⋏1)^m⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN asm_rewrite_tac[ℝ_ℕ_exp_def]);
a(lemma_tac ⌜¬ x^m = ℕℝ 0⌝ THEN1 (bc_thm_tac ℝ_ℕ_exp_¬_eq_0_thm THEN REPEAT strip_tac));
a(ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_recip_thm1⦎ = save_thm ( "ℝ_ℕ_exp_recip_thm1", (
set_goal([], ⌜∀m:ℕ; x ⦁ ¬x = ℕℝ 0 ⇒  (x ⋏-⋏1)^m = (x^m)⋏-⋏1⌝);
a(REPEAT strip_tac THEN ALL_FC_T rewrite_tac[ℝ_ℕ_exp_recip_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_1_≤_thm⦎ = save_thm ( "ℝ_ℕ_exp_1_≤_thm", (
set_goal([], ⌜∀m:ℕ; x ⦁ ℕℝ 1 ≤ x ⇒ ℕℝ 1 ≤ x^m ⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN1 asm_rewrite_tac[ℝ_ℕ_exp_def]);
a(rewrite_tac[ℝ_ℕ_exp_def] THEN bc_thm_tac ℝ_≤_trans_thm);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(conv_tac (LEFT_C(pure_once_rewrite_conv[prove_rule[]⌜x = x * ℕℝ 1⌝])));
a(bc_thm_tac ℝ_≤_times_mono_thm THEN REPEAT strip_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_less_1_mono_thm⦎ = save_thm ( "ℝ_ℕ_exp_less_1_mono_thm", (
set_goal([], ⌜∀x; m:ℕ⦁ℕℝ 0 < x ∧ x < ℕℝ 1 ⇒ x^(m+1) < x^m ⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN1 asm_rewrite_tac[ℝ_ℕ_exp_def]);
a(once_rewrite_tac[ℝ_ℕ_exp_def]);
a(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_less_mono_thm⦎ = save_thm ( "ℝ_ℕ_exp_less_mono_thm", (
set_goal([], ⌜∀x; m:ℕ⦁ℕℝ 0 < x ⇒ ℕℝ 0 < x^m ⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN asm_rewrite_tac[ℝ_ℕ_exp_def]);
a(bc_thm_tac ℝ_0_less_0_less_times_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_less_1_mono_thm1⦎ = save_thm ( "ℝ_ℕ_exp_less_1_mono_thm1", (
set_goal([], ⌜∀x; m n:ℕ⦁ℕℝ 0 < x ∧ x < ℕℝ 1 ∧ m < n ⇒ x^n < x^m ⌝);
a(REPEAT ∀_tac THEN induction_tac⌜n:ℕ⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a( lemma_tac⌜n = m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac THEN ALL_FC_T rewrite_tac [ℝ_ℕ_exp_less_1_mono_thm]);
(* *** Goal "2" *** *)
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜x^n⌝ THEN REPEAT strip_tac);
a(ALL_FC_T rewrite_tac [ℝ_ℕ_exp_less_1_mono_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_linear_estimate_thm⦎ = save_thm ( "ℝ_ℕ_exp_linear_estimate_thm", (
set_goal([], ⌜∀x m⦁ℕℝ 0 < x ⇒ ℕℝ 1 + ℕℝ m*x ≤ (ℕℝ 1 + x)^m ⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN
	once_asm_rewrite_tac[ℝ_ℕ_exp_def]
	THEN1 rewrite_tac[ℝ_ℕ_exp_0_1_thm]);
a(rewrite_tac[ℕℝ_plus_homomorphism_thm, ℝ_times_plus_distrib_thm]);
a(contr_tac);
a(all_fc_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c d:ℝ⦁a ≤ b ∧ ¬d ≤ c ⇒ a + c < b + d⌝]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]);
a(once_rewrite_tac[ℝ_less_0_less_thm] THEN rewrite_tac[]
	THEN conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(rewrite_tac[ℝ_¬_less_≤_thm]);
a(lemma_tac⌜ℕℝ 1 ≤ (ℕℝ 1 + x)^m⌝ THEN1
	(bc_thm_tac ℝ_ℕ_exp_1_≤_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LEMMA_T⌜x ≤ x*(ℕℝ 1 + x) ^m⌝ ante_tac
	THEN_LIST [id_tac, PC_T1 "ℝ_lin_arith" prove_tac[]]);
a(conv_tac(LEFT_C(pure_once_rewrite_conv[prove_rule[]⌜x = x * ℕℝ 1⌝])));
a(bc_thm_tac ℝ_≤_times_mono_thm THEN REPEAT strip_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_0_≤_square_thm⦎ = save_thm ( "ℝ_0_≤_square_thm", (
set_goal([], ⌜∀ x:ℝ⦁ ℕℝ 0 ≤ x ^ 2⌝);
a(REPEAT strip_tac THEN rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(cases_tac ⌜ℕℝ 0 ≤ x⌝ THEN1
	bc_thm_tac ℝ_0_≤_0_≤_times_thm
	THEN REPEAT strip_tac);
a(LEMMA_T ⌜x * x = ~x * ~x⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(lemma_tac⌜ℕℝ 0 ≤ ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_0_≤_0_≤_times_thm
	THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_square_eq_0_thm⦎ = save_thm ( "ℝ_square_eq_0_thm", (
set_goal([], ⌜∀ x:ℝ⦁ x ^ 2 = ℕℝ 0 ⇔ x = ℕℝ 0⌝);
a(rewrite_tac[ℝ_ℕ_exp_square_thm]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_times_eq_0_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_bound_below_2_thm⦎ = save_thm ( "ℝ_bound_below_2_thm", (
set_goal([], ⌜∀x y⦁ ℕℝ 0 < x ∧ ℕℝ 0 < y ⇒ ∃d⦁ℕℝ 0 < d ∧ d < x ∧ d < y⌝);
a(REPEAT strip_tac);
a(cases_tac⌜x  <  y⌝ THEN_LIST [∃_tac⌜(1/2)*x⌝, ∃_tac⌜(1/2)*y⌝]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏ℝ_bound_below_3_thm⦎ = save_thm ( "ℝ_bound_below_3_thm", (
set_goal([], ⌜∀x y z⦁
	ℕℝ 0 < x ∧ ℕℝ 0 < y ∧ ℕℝ 0 <  z
⇒	∃d⦁ℕℝ 0 < d ∧ d < x ∧ d < y ∧ d < z⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃c⦁ℕℝ 0 < c ∧ c < x ∧ c < y⌝ THEN1
	(bc_thm_tac ℝ_bound_below_2_thm THEN REPEAT strip_tac));
a(lemma_tac⌜∃d⦁ℕℝ 0 < d ∧ d < c ∧ d < z⌝ THEN1
	(bc_thm_tac ℝ_bound_below_2_thm THEN REPEAT strip_tac));
a(∃_tac⌜d⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_max_2_thm⦎ = save_thm ( "ℝ_max_2_thm", (
set_goal([], ⌜∀x y:ℝ⦁ ∃z⦁x < z ∧ y < z⌝);
a(REPEAT strip_tac);
a(∃_tac⌜(if x < y then y else x) + ℕℝ 1⌝
	THEN cases_tac ⌜x < y⌝ THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_max_3_thm⦎ = save_thm ( "ℝ_max_3_thm", (
set_goal([], ⌜∀x y z:ℝ⦁ ∃t⦁x < t ∧ y < t ∧ z < t⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜y⌝] ℝ_max_2_thm));
a(strip_asm_tac(list_∀_elim[⌜z⌝, ⌜z'⌝] ℝ_max_2_thm));
a(∃_tac⌜z''⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_min_2_thm⦎ = save_thm ( "ℝ_min_2_thm", (
set_goal([], ⌜∀x y:ℝ⦁ ∃z⦁z < x ∧ z < y⌝);
a(REPEAT strip_tac);
a(∃_tac⌜(if y < x then y else x) - ℕℝ 1⌝
	THEN cases_tac ⌜y < x⌝ THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_min_3_thm⦎ = save_thm ( "ℝ_min_3_thm", (
set_goal([], ⌜∀x y z:ℝ⦁ ∃t⦁t < x ∧ t < y ∧ t < z⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜y⌝] ℝ_min_2_thm));
a(strip_asm_tac(list_∀_elim[⌜z⌝, ⌜z'⌝] ℝ_min_2_thm));
a(∃_tac⌜z''⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsubsection{The Archimedean Property}
%%%%
%%%%
%%%%
%%%%
We present the archimedean property in two guises:
the usual formulation, any real is bounded above by some natural number:
%%%%
%%%%
=SML

val ⦏ℝ_archimedean_thm⦎ = save_thm ( "ℝ_archimedean_thm", (
set_goal([], ⌜∀x:ℝ⦁ ∃m⦁ x < ℕℝ m⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜ℕℝ 0⌝]ℝ_less_cases_thm) THEN1 asm_prove_tac[]
	THEN1 ∃_tac⌜1⌝ THEN1 asm_rewrite_tac[]);
a(ℝ_delta_induction_tac⌜x⌝);
a(∃_tac⌜ℕℝ 1⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜ℕℝ 2⌝ THEN REPEAT strip_tac);
a(∃_tac⌜3⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜m+1⌝ THEN rewrite_tac[ℕℝ_plus_homomorphism_thm]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
\ldots and a reciprocal version: any positive real is bounded
below by the reciprocal of a positive natural number.
%%%%
%%%%
=SML

val ⦏ℝ_archimedean_recip_thm⦎ = save_thm ( "ℝ_archimedean_recip_thm", (
set_goal([], ⌜∀x:ℝ⦁ ℕℝ 0 < x ⇒ ∃m⦁ (ℕℝ (m+1))⋏-⋏1 < x⌝);
a(REPEAT strip_tac THEN all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(strip_asm_tac(∀_elim⌜x ⋏-⋏1⌝ℝ_archimedean_thm));
a(lemma_tac⌜x ⋏-⋏1 < ℕℝ (m+1)⌝ THEN1
	(rewrite_tac[ℕℝ_plus_homomorphism_thm] THEN
		bc_thm_tac ℝ_less_trans_thm THEN ∃_tac ⌜ℕℝ m⌝ THEN REPEAT strip_tac));
a(DROP_NTH_ASM_T 2 discard_tac);
a(lemma_tac⌜ℕℝ 0 < ℕℝ (m+1)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [ℝ_less_recip_less_thm]);
a(lemma_tac⌜¬x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses] THEN prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_archimedean_times_thm⦎ = save_thm ( "ℝ_archimedean_times_thm", (
set_goal([], ⌜∀x y⦁ℕℝ 0 < x ⇒ ∃m⦁ y < ℕℝ m * x⌝);
a(REPEAT strip_tac THEN cases_tac⌜¬ℕℝ 0 < y⌝ THEN1
	(∃_tac⌜1⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(strip_asm_tac(∀_elim⌜y⌝ℝ_archimedean_thm));
a(strip_asm_tac(∀_elim⌜x⌝ℝ_archimedean_recip_thm));
a(lemma_tac ⌜y < ℕℝ(m+1)⌝ THEN1
	(rewrite_tac[ℕℝ_plus_homomorphism_thm] THEN
		all_fc_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b⦁a < b ⇒ a < b + ℕℝ 1⌝]));
a(DROP_NTH_ASM_T 3 discard_tac);
a(∃_tac⌜ (m+1)*(m'+1)⌝);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac ⌜(ℕℝ ((m + 1)  * (m' + 1))) * ℕℝ (m' + 1) ⋏-⋏1⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜¬ℕℝ(m'+1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(rewrite_tac[ℝ_times_assoc_thm, ℕℝ_times_homomorphism_thm]);
a(ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2" *** *)
a(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
a(rewrite_tac [ℕℝ_less_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_archimedean_division_thm⦎ = save_thm ( "ℝ_archimedean_division_thm", (
set_goal([], ⌜∀d y⦁ℕℝ 0 < d ∧ ℕℝ 0 ≤ y ⇒ ∃q r⦁ y = ℕℝ q * d + r ∧ ℕℝ 0 ≤ r ∧ r < d⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀m y⦁ℕℝ 0 ≤  y ∧ y < ℕℝ m * d ⇒ ∃q r⦁ y = ℕℝ q * d + r ∧ ℕℝ 0 ≤ r ∧ r < d⌝);
(* *** Goal "1" *** *)
a(POP_ASM_T discard_tac THEN strip_tac THEN induction_tac⌜m:ℕ⌝);
(* *** Goal "1.1" *** *)
a(rewrite_tac[] THEN REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(REPEAT strip_tac);
a(cases_tac⌜y < d⌝);
(* *** Goal "1.2.1" *** *)
a(∃_tac⌜0⌝ THEN ∃_tac⌜y⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[ℕℝ_plus_homomorphism_thm]));
a(lemma_tac⌜ℕℝ 0 ≤ y + ~d ⌝	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a ⦁ y < (a + ℕℝ 1) * d ⇒ y + ~d< a * d⌝]);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(∃_tac⌜q + 1⌝ THEN ∃_tac⌜r⌝ THEN
	rewrite_tac[ℕℝ_plus_homomorphism_thm, ℝ_times_plus_distrib_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1.2.2.1" *** *)
a(all_fc_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a ⦁ y + ~d  = a *d + r⇒y = (a*d+d)+r⌝]);
(* *** Goal "2" *** *)
a(lemma_tac ⌜∃m⦁ y < ℕℝ m * d⌝ THEN1
	(bc_thm_tac ℝ_archimedean_times_thm THEN REPEAT strip_tac));
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜q⌝ THEN ∃_tac⌜r⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_tends_to_infinity_thm⦎ = save_thm ( "ℝ_ℕ_exp_tends_to_infinity_thm", (
set_goal([], ⌜∀x y⦁ℕℝ 1 < x ⇒ ∃m:ℕ⦁ y <  x^m⌝);
a(REPEAT ∀_tac THEN STRIP_T (strip_asm_tac o once_rewrite_rule[ℝ_less_0_less_thm]));
a(strip_asm_tac (list_∀_elim[⌜x + ~ (ℕℝ 1)⌝, ⌜y⌝] ℝ_archimedean_times_thm));
a(strip_asm_tac (list_∀_elim[⌜x + ~ (ℕℝ 1)⌝, ⌜m⌝] ℝ_ℕ_exp_linear_estimate_thm));
a(∃_tac⌜m⌝ THEN1 bc_thm_tac ℝ_less_trans_thm);
a(∃_tac⌜ℕℝ m * (x + ~ (ℕℝ 1))⌝ THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b⦁ℕℝ 1 + a ≤ b ⇒ a < b⌝]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_tends_to_0_thm⦎ = save_thm ( "ℝ_ℕ_exp_tends_to_0_thm", (
set_goal([], ⌜∀x y⦁ℕℝ 0 < x ∧ x < ℕℝ 1 ∧ ℕℝ 0 < y ⇒ ∃m:ℕ⦁ x^m < y⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜¬x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[ℝ_¬_recip_0_thm]);
a(strip_asm_tac (rewrite_rule[](list_∀_elim[⌜x⌝, ⌜ℕℝ 1⌝] ℝ_less_recip_less_thm)));
a(strip_asm_tac (list_∀_elim[⌜x ⋏-⋏1⌝, ⌜y ⋏-⋏1⌝] ℝ_ℕ_exp_tends_to_infinity_thm));
a(∃_tac⌜m⌝ THEN POP_ASM_T ante_tac);
a(ALL_FC_T rewrite_tac[ℝ_ℕ_exp_recip_thm1] THEN strip_tac);
a(all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜ℕℝ 0 < x^m⌝ THEN1 ALL_FC_T rewrite_tac[ℝ_ℕ_exp_0_less_thm]);
a(lemma_tac⌜ℕℝ 0 < (x^m) ⋏-⋏1⌝ THEN1 ALL_FC_T rewrite_tac[ℝ_0_less_0_less_recip_thm]);
a(ante_tac (list_∀_elim[⌜y ⋏-⋏1⌝, ⌜(x^m) ⋏-⋏1⌝] ℝ_less_recip_less_thm));
a(lemma_tac⌜¬y = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜¬(x^m) = ℕℝ 0⌝ THEN1 ALL_FC_T rewrite_tac[ℝ_ℕ_exp_¬_eq_0_thm]);
a(ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Limits}
%%%%
%%%%
%%%%
%%%%
We now prove some basic facts about limits.

Firstly, constant sequences have limits:
%%%%
%%%%
=SML

val ⦏const_lim_seq_thm⦎ = save_thm ( "const_lim_seq_thm", (
set_goal([], ⌜∀c⦁(λm⦁ c) -> c⌝);
a(REPEAT strip_tac THEN rewrite_tac[lim_seq_def]);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
Secondly, if two sequences each have a limit, then so does their
sum and its limit is the sum of the limits:
%%%%
%%%%
=SML

val ⦏plus_lim_seq_thm⦎ = save_thm ( "plus_lim_seq_thm", (
set_goal([], ⌜∀s1 c1 s2 c2⦁
	s1 -> c1 ∧ s2 -> c2 ⇒ (λm⦁s1 m + s2 m) -> c1 + c2⌝);
a(once_rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(lemma_tac ⌜ℕℝ 0 < (1/2)*e ⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2  (fn th =>  asm_fc_tac[] THEN asm_tac th));
a(∃_tac⌜n + n'⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n ≤ m ∧ n' ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_GET_NTH_ASM_T [5, 6] (ALL_FC_T (MAP_EVERY ante_tac)));
a(rewrite_tac[] THEN
	pure_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[] ⌜∀a b:ℝ⦁~a + ~b = ~(a + b)⌝]);
a(FC_T1 fc_⇔_canon  pure_rewrite_tac[ℝ_abs_diff_bounded_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
We now want to give the expected result on the product of two sequences
with limits. We need some preliminaries. The first is of general use,
it says that any sequence with a limit has bounded absolute values:
%%%%
%%%%
=SML

val ⦏lim_seq_bounded_thm⦎ = save_thm ( "lim_seq_bounded_thm", (
set_goal([], ⌜∀s c⦁ s -> c ⇒ ∃b⦁ ℕℝ 0 < b ∧ ∀m⦁ Abs(s m) < b⌝);
a(lemma_tac⌜∀n; s: ℕ → ℝ; b1⦁ ℕℝ 0 < b1 ∧ (∀m⦁n ≤ m ⇒ Abs(s m) < b1) ⇒
	(∃b2⦁ℕℝ 0 < b2 ∧ ∀ m⦁ Abs(s m) < b2)⌝);
(* *** Goal "1" *** *)
a(strip_tac THEN induction_tac ⌜n:ℕ⌝ THEN1 prove_tac[]);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(∃_tac⌜Abs(s n) + b1⌝);
a(spec_nth_asm_tac 1 ⌜n+1⌝);
a(strip_asm_tac(∀_elim⌜s(n+1)⌝ ℝ_0_≤_abs_thm));
a(strip_asm_tac(∀_elim⌜s n⌝ ℝ_0_≤_abs_thm));
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜m' = n⌝ THEN1 (all_var_elim_asm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜n + 1 ≤ m'⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 bc_thm_tac);
a(spec_nth_asm_tac 1 ⌜ℕℝ 1⌝);
a(∃_tac⌜n⌝ THEN ∃_tac⌜Abs c + ℕℝ 2⌝);
a(REPEAT strip_tac THEN1
	(strip_asm_tac(∀_elim⌜c⌝ ℝ_0_≤_abs_thm) THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_asm_fc_tac[]);
a(ante_tac (list_∀_elim[⌜s m + ~c⌝, ⌜c⌝]ℝ_abs_plus_thm));
a(rewrite_tac[ℝ_plus_assoc_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Now a more specialised lemma which is the arithmetic core
of the argument about the product of two sequences:
%%%%
%%%%
=SML
set_goal([], ⌜∀e t x y c d⦁
	Abs(x - c) < e * (ℕℝ 2*t)⋏-⋏1
∧	Abs(y - d) < e * (ℕℝ 2*t)⋏-⋏1
∧	Abs x < t
∧	Abs d < t
⇒	Abs (x*y - c*d) < e	⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(LEMMA_T ⌜x*y + ~(c*d) = x*(y + ~d) + (x + ~c)*d⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜Abs(x*(y + ~d)) + Abs((x + ~c)*d)⌝
	THEN rewrite_tac[ℝ_abs_plus_thm, ℝ_abs_times_thm]);
a(bc_thm_tac ℝ_less_≤_trans_thm THEN ∃_tac⌜t*e*(ℕℝ 2*t)⋏-⋏1 + t*e*(ℕℝ 2*t)⋏-⋏1⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ℝ_plus_mono_thm2);
a(REPEAT strip_tac THEN1 (bc_thm_tac ℝ_abs_less_times_thm THEN REPEAT strip_tac));
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x⦁t*e*x = (e*x)*t⌝]);
a(bc_thm_tac ℝ_abs_less_times_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(conv_tac (LEFT_C ℝ_anf_conv));
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁x*e*t*y = e*(x*t)*y⌝]);
a(lemma_tac⌜¬ ℕℝ 2 * t = ℕℝ 0⌝ THEN1
	(strip_asm_tac(∀_elim⌜x⌝ ℝ_0_≤_abs_thm) THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(ALL_FC_T rewrite_tac[ℝ_times_recip_thm]);
val ⦏times_lim_seq_lemma⦎ = pop_thm ();
=TEX
Now we can prove that the product of two sequences each of which has a limit has
the product of the limits as its limit:
%%%%
%%%%
=SML

val ⦏times_lim_seq_thm⦎ = save_thm ( "times_lim_seq_thm", (
set_goal([], ⌜∀s1 c1 s2 c2⦁
	s1 -> c1 ∧ s2 -> c2 ⇒ (λm⦁s1 m * s2 m) -> c1 * c2⌝);
a(REPEAT strip_tac THEN rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[lim_seq_def]));
a(all_fc_tac[lim_seq_bounded_thm]);
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[lim_seq_def]));
a(strip_asm_tac(∀_elim⌜c2⌝ ℝ_0_≤_abs_thm));
a(lemma_tac⌜ℕℝ 0 < e*(ℕℝ 2 * (b + Abs c2))⋏-⋏1⌝);
(* *** Goal "1" *** *)
a(bc_thm_tac ℝ_0_less_0_less_times_thm THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_0_less_0_less_recip_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [5, 7] (MAP_EVERY ante_tac));
a(all_asm_fc_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜n+n'⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n ≤ m ∧ n' ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_GET_NTH_ASM_T[6, 7] all_fc_tac);
a(bc_thm_tac (rewrite_rule[]times_lim_seq_lemma));
a(∃_tac⌜b + Abs c2⌝ THEN asm_rewrite_tac[]);
a(spec_nth_asm_tac 13 ⌜m⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Now we prove that the negative of a sequence which has a limit has
thenegative of the limit as its limit:
%%%%
%%%%
=SML

val ⦏minus_lim_seq_thm⦎ = save_thm ( "minus_lim_seq_thm", (
set_goal([], ⌜∀s c⦁ s -> c ⇔ (λm⦁~(s m)) ->  ~c⌝);
a(lemma_tac⌜∀s c⦁ s -> c ⇒ (λm⦁~(s m)) ->  ~c⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(pure_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜~(s m) + c = ~ (s m + ~c)⌝]);
a(asm_rewrite_tac[ℝ_abs_minus_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
a(POP_ASM_T ante_tac THEN rewrite_tac[η_axiom]);
pop_thm()
));

=TEX
We can now show by polynomial induction that polynomial functions preserve limits.
As we will see shortly, this shows that every polynomial function is continuous.
%%%%
%%%%
=SML

val ⦏poly_lim_seq_thm⦎ = save_thm ( "poly_lim_seq_thm", (
set_goal([], ⌜∀f s t⦁f ∈ PolyFunc ∧ s -> t ⇒ (λx⦁ f (s x)) -> f t⌝);
a(REPEAT strip_tac);
a(poly_induction_tac ⌜f⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[const_lim_seq_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[η_axiom]);
(* *** Goal "3" *** *)
a(ALL_FC_T (MAP_EVERY ante_tac) [plus_lim_seq_thm]);
a(rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "4" *** *)
a(ALL_FC_T (MAP_EVERY ante_tac) [times_lim_seq_thm]);
a(rewrite_tac[] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
Finally, moving on from polynomials, we will need to reason
about (particular) rational functions from time to time and
this requires the usual result about the limit of
a sequence of reciprocals.
%%%%
%%%%
=SML

val ⦏recip_lim_seq_thm⦎ = save_thm ( "recip_lim_seq_thm", (
set_goal([], ⌜∀s t⦁ s -> t ∧ ¬t = ℕℝ 0 ⇒ (λm⦁ (s m) ⋏-⋏1) -> t ⋏-⋏1⌝);
a(REPEAT strip_tac THEN all_fc_tac [lim_seq_bounded_thm]);
a(DROP_NTH_ASM_T 4 ante_tac THEN
	rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(all_fc_tac[ℝ_¬_0_abs_thm]);
a(lemma_tac⌜ℕℝ 0 < (1/2)*Abs t⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜∃n1⦁∀ m⦁ n1 ≤ m ⇒ (1/2)*Abs t < Abs(s m)⌝);
(* *** Goal "1" *** *)
a(spec_nth_asm_tac 4 ⌜(1/2)*Abs t⌝);
a(∃_tac ⌜n⌝ THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [2] all_fc_tac);
a(CONTR_T (strip_asm_tac o rewrite_rule[ℝ_¬_less_≤_thm]));
a(lemma_tac⌜Abs t < Abs t⌝);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜Abs(s m) + Abs(~(s m + ~t))⌝);
a(REPEAT strip_tac THEN_LIST
	[bc_thm_tac ℝ_abs_plus_bc_thm,
	rewrite_tac[ℝ_abs_minus_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(lemma_tac ⌜ℕℝ 0 < Abs t*Abs t*e⌝ THEN1
	(all_fc_tac[ℝ_0_less_0_less_times_thm] THEN all_fc_tac[ℝ_0_less_0_less_times_thm]));
a(lemma_tac ⌜ℕℝ 0 < (1/2)*Abs t*Abs t*e⌝ THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 7 ⌜(1/2)*Abs t*Abs t*e⌝);
a(∃_tac⌜n1 + n⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n1 ≤ m ∧ n ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 7 ⌜m⌝);
a(LEMMA_T⌜¬Abs(s m) = ℕℝ 0⌝ (asm_tac o rewrite_rule[ℝ_abs_eq_0_thm])
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜¬ ~ t = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[
	conv_rule(ONCE_MAP_C (RIGHT_C eq_sym_conv)) ℝ_minus_recip_thm,
	ℝ_plus_recip_thm]);
a(spec_nth_asm_tac 7 ⌜m⌝);
a(once_rewrite_tac[ℝ_abs_times_thm]);
a(lemma_tac⌜¬Abs t = ℕℝ 0⌝ THEN1 asm_rewrite_tac[ℝ_abs_eq_0_thm]);
a(LEMMA_T ⌜e = ((1/2)*Abs t * Abs t * e)*(Abs ((1/2)*t))⋏-⋏1*(Abs t)⋏-⋏1⌝ once_rewrite_thm_tac
	THEN1 (rewrite_tac[ℝ_abs_times_thm] THEN
		ALL_FC_T rewrite_tac[
			rewrite_rule[](∀_elim⌜1/2⌝(hd(rev(strip_∧_rule ℝ_recip_clauses))))] THEN
			rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
			⌜∀x y⦁((1/2)*x*x*y)*(ℕℝ 2 * x ⋏-⋏1)*x ⋏-⋏1=
				 (x*x ⋏-⋏1) * (x*x ⋏-⋏1) * y⌝]
		THEN ALL_FC_T rewrite_tac[ℝ_times_recip_thm]));
a(bc_thm_tac ℝ_abs_less_times_thm THEN REPEAT strip_tac);
a(once_rewrite_tac[ℝ_times_comm_thm] THEN rewrite_tac[ℝ_abs_times_thm]);
a(ALL_FC_T rewrite_tac[ℝ_minus_recip_thm] THEN rewrite_tac[ℝ_abs_minus_thm]);
a(ALL_FC_T rewrite_tac[ℝ_abs_recip_thm] THEN bc_thm_tac ℝ_times_mono_thm);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac ℝ_0_less_0_less_recip_thm THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(bc_thm_tac ℝ_less_recip_less_thm THEN
	LIST_GET_NTH_ASM_T [14, 5] (MAP_EVERY ante_tac) THEN
	PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
The following conversions are useful in applying some of the previous results (and later
ones) which require the matrix of a $\lambda$-abstraction to be converted
into a suitable form by introducing $\beta$-redexes.
%%%%
%%%%
=SML
fun ⦏un_β_conv⦎ (v : TERM) : CONV = (fn tm =>
	let	val lhs = mk_app(mk_λ(v, tm), v);
	in	eq_sym_rule (β_conv lhs)
	end
);
val ⦏λ_un_β_rands_conv⦎ : CONV = (fn tm =>
	let	val (v, _) = dest_λ tm;
	in	SIMPLE_λ_C (RANDS_C (un_β_conv v)) tm
	end
);
=TEX
Some further generalities about sequences are useful.
The following theorem says that an arbitrary interleaving of two
sequences that converge to the same limit itself converges to that limit:
%%%%
%%%%
=SML

val ⦏lim_seq_choice_thm⦎ = save_thm ( "lim_seq_choice_thm", (
set_goal([], ⌜∀p s1 s2 x⦁ s1 -> x ∧ s2 -> x ⇒ (λm⦁if p m then s1 m else s2 m) -> x⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(∃_tac⌜n + n'⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n ≤ m ∧ n' ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_GET_NTH_ASM_T [4, 5] all_fc_tac);
a(cases_tac⌜p m⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏abs_lim_seq_thm⦎ = save_thm ( "abs_lim_seq_thm", (
set_goal([], ⌜∀s x⦁ s -> x  ⇒ (λm⦁Abs(s m)) -> Abs x⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜Abs(s m + ~x)⌝ THEN REPEAT strip_tac);
a(rewrite_tac[rewrite_rule[]ℝ_abs_abs_minus_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_recip_ℕ_thm⦎ = save_thm ( "lim_seq_recip_ℕ_thm", (
set_goal([], ⌜∀x⦁ (λm⦁x + ℕℝ(m+1)⋏-⋏1) -> x⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(all_fc_tac[ℝ_archimedean_recip_thm]);
a(∃_tac⌜m+1⌝ THEN REPEAT strip_tac);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(lemma_tac⌜ℕℝ 0 < ℕℝ (m+1) ∧ ℕℝ 0 < ℕℝ (m'+1)⌝ THEN1 rewrite_tac[ℕℝ_0_less_thm]);
a(lemma_tac⌜ℕℝ (m+1) < ℕℝ (m'+1)⌝ THEN1 
	(asm_rewrite_tac[ℕℝ_less_thm] THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ 0 ≤ ℕℝ (m' + 1) ⋏-⋏1⌝ THEN1
	(rewrite_tac[ℝ_≤_def] THEN all_fc_tac[ℝ_0_less_0_less_recip_thm] THEN asm_rewrite_tac[]));
a(asm_rewrite_tac[ℝ_abs_def]);
a(all_fc_tac[ℝ_less_recip_less_thm]);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜ℕℝ (m + 1) ⋏-⋏1⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_¬_eq_thm⦎ = save_thm ( "lim_seq_¬_eq_thm", (
set_goal([], ⌜∀x⦁ ∃s⦁ s -> x ∧ (∀m⦁¬s m = x)⌝);
a(REPEAT strip_tac);
a(∃_tac⌜(λm⦁x + ℕℝ(m+1)⋏-⋏1)⌝ THEN rewrite_tac[lim_seq_recip_ℕ_thm]);
a(REPEAT strip_tac THEN lemma_tac⌜ℕℝ 0 < ℕℝ (m + 1) ⋏-⋏1⌝);
(* *** Goal "1" *** *)
a(bc_tac[ℝ_0_less_0_less_recip_thm] THEN rewrite_tac[ℕℝ_0_less_thm]);
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The following ``shift theorem''
shows that we can ignore any finite leading subsequence of
a sequence when we calculate its limit:
%%%%
%%%%
=SML

val ⦏lim_seq_shift_thm⦎ = save_thm ( "lim_seq_shift_thm", (
set_goal([], ⌜∀m s x⦁ (s -> x) ⇔ (λn⦁s (n + m)) -> x⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[] THEN ∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n ≤ m'+m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[] THEN ∃_tac⌜n + m⌝ THEN REPEAT strip_tac);
a(TOP_ASM_T (strip_asm_tac o rewrite_rule[≤_def]) THEN all_var_elim_asm_tac1);
a(SPEC_NTH_ASM_T 1 ⌜n+i⌝ ante_tac THEN
	conv_tac (ONCE_MAP_C anf_conv) THEN
	REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_¬_eq_thm1⦎ = save_thm ( "lim_seq_¬_eq_thm1", (
set_goal([], ⌜∀x d⦁ ℕℝ 0 < d ⇒ ∃s⦁ s -> x ∧ (∀m⦁Abs(s m - x) <  d ∧ ¬s m = x)⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜x⌝ lim_seq_¬_eq_thm));
a(GET_NTH_ASM_T 2 (fn th => all_fc_tac[rewrite_rule[lim_seq_def]th]));
a(∃_tac⌜λp⦁s(p + n)⌝ THEN asm_rewrite_tac[]);
a(strip_tac THEN1 bc_thm_tac lim_seq_shift_thm THEN REPEAT strip_tac);
a(TOP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
A sequences that converges to a non-zero limit can have
at most finitely many zero values:
%%%%
%%%%
=SML

val ⦏lim_seq_¬_0_thm⦎ = save_thm ( "lim_seq_¬_0_thm", (
set_goal([], ⌜∀s x⦁ (s -> x) ∧ ¬x = ℕℝ 0 ⇒ ∃n⦁∀m⦁ n ≤ m ⇒ ¬s m = ℕℝ 0⌝);
a(rewrite_tac[lim_seq_def] THEN contr_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[ℝ_¬_0_abs_thm] THEN all_asm_fc_tac[]);
a(spec_nth_asm_tac 3 ⌜n⌝);
a(spec_nth_asm_tac 3 ⌜m⌝);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[ℝ_abs_minus_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_upper_bound_thm⦎ = save_thm ( "lim_seq_upper_bound_thm", (
set_goal([], ⌜∀s b c⦁ (∀m⦁s m ≤  b) ∧ s -> c ⇒ c ≤ b⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(contr_tac THEN POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(lemma_tac ⌜ℕℝ 0 < c + ~b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜n⌝));
a(POP_ASM_T ante_tac THEN spec_nth_asm_tac 3 ⌜n⌝);
a(LEMMA_T⌜¬ℕℝ 0 ≤ s n + ~c⌝ (fn th => rewrite_tac[th, ℝ_abs_def]) THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_unique_thm⦎ = save_thm ( "lim_seq_unique_thm", (
set_goal([], ⌜∀s b c⦁ s -> b ∧ s -> c⇒ b = c⌝);
a(rewrite_tac[lim_seq_def] THEN contr_tac);
a(lemma_tac⌜b < c ∨ c < b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1" *** *)
a(lemma_tac⌜ℕℝ 0 < (1/2)*(c + ~b)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4, 5] all_fc_tac);
a(REPEAT_N 2 (POP_ASM_T (ante_tac o ∀_elim⌜n'+n⌝)));
a(rewrite_tac[]);
a(cases_tac⌜ℕℝ 0 ≤ (s (n' + n) + ~c)⌝ THEN cases_tac ⌜ℕℝ 0 ≤ s (n' + n) + ~b⌝ THEN
	asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜ℕℝ 0 < (1/2)*(b + ~c)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4, 5] all_fc_tac);
a(REPEAT_N 2 (POP_ASM_T (ante_tac o ∀_elim⌜n'+n⌝)));
a(rewrite_tac[]);
a(cases_tac⌜ℕℝ 0 ≤ (s (n' + n) + ~c)⌝ THEN cases_tac ⌜ℕℝ 0 ≤ s (n' + n) + ~b⌝ THEN
	asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_diffs_tend_to_0_thm⦎ = save_thm ( "lim_seq_diffs_tend_to_0_thm", (
set_goal([], ⌜∀s c⦁ s -> c ⇒ (λm⦁ s(m+1) - s m) -> ℕℝ 0⌝);
a(REPEAT strip_tac);
a(TOP_ASM_T (strip_asm_tac o once_rewrite_rule[∀_elim⌜1⌝lim_seq_shift_thm]));
a(rewrite_tac[] THEN pure_once_rewrite_tac[prove_rule[]⌜ℕℝ 0 = c + ~c⌝]);
a(ho_bc_thm_tac plus_lim_seq_thm THEN REPEAT strip_tac);
a(bc_thm_tac minus_lim_seq_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Continuity}
%%%%
%%%%
%%%%
%%%%
Most of the work on continuity duplicates reasoning for sequences if carried
out from first principles. To allow us to reuse the material on sequences,
we prove that a function is continuous iff. it preserves limits:
=TEX
%%%%
%%%%
=SML

val ⦏cts_lim_seq_thm⦎ = save_thm ( "cts_lim_seq_thm", (
set_goal([], ⌜∀f x⦁ f Cts x ⇔ ∀s⦁ s -> x ⇒ (λm⦁f(s m)) -> f x⌝);
a(rewrite_tac[cts_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜e⌝);
a(spec_nth_asm_tac 4 ⌜d⌝);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(contr_tac THEN lemma_tac⌜
	∃s⦁∀m⦁ Abs(s m + ~x) < (ℕℝ (m+1)) ⋏-⋏1 ∧ e ≤ Abs(f(s m) + ~(f x))
⌝ THEN1 prove_∃_tac THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(lemma_tac⌜ℕℝ 0 < ℕℝ (m' + 1) ⋏-⋏1⌝ THEN1
	(bc_thm_tac ℝ_0_less_0_less_recip_thm THEN rewrite_tac[ℕℝ_less_thm]));
a(spec_nth_asm_tac 2 ⌜ℕℝ (m' + 1) ⋏-⋏1⌝);
a(∃_tac⌜y⌝ THEN REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜s -> x⌝ THEN1 rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 4 discard_tac THEN all_asm_fc_tac[ℝ_archimedean_recip_thm]);
a(∃_tac⌜m + 2⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜ℕℝ (m'+1)⋏-⋏1⌝ THEN asm_rewrite_tac[]);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜ℕℝ (m+1)⋏-⋏1⌝ THEN asm_rewrite_tac[]);
a(bc_thm_tac ℝ_less_recip_less_thm THEN
	rewrite_tac[ℕℝ_plus_homomorphism_thm, ℕℝ_less_thm]
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(ALL_ASM_FC_T (MAP_EVERY ante_tac)[]);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(∃_tac ⌜e⌝ THEN REPEAT strip_tac);
a(∃_tac ⌜n⌝ THEN asm_rewrite_tac[ℝ_¬_less_≤_thm]);
pop_thm()
));

=TEX
It is occasionally convenient to have the following stronger variant
on the previous theorem, which lets us demonstrate continuity of a function $f$
at a point $x$ by considering sequences that tend to $x$ without ever being
equal to $x$.
%%%%
%%%%
=SML

val ⦏cts_lim_seq_thm1⦎ = save_thm ( "cts_lim_seq_thm1", (
set_goal([], ⌜∀f x⦁ f Cts x ⇔ ∀s⦁ s -> x ∧ (∀m⦁¬s m = x) ⇒ (λm⦁f(s m)) -> f x⌝);
a(REPEAT strip_tac THEN1 all_fc_tac[cts_lim_seq_thm]);
a(rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜x⌝ lim_seq_¬_eq_thm));
a(strip_asm_tac(rewrite_rule[](list_∀_elim[⌜λm⦁s m = x⌝, ⌜s'⌝, ⌜s⌝, ⌜x⌝]lim_seq_choice_thm)));
a(lemma_tac⌜∀m⦁ ¬(λm⦁ if s m = x then s' m else s m) m = x⌝ THEN1 
	(REPEAT strip_tac THEN cases_tac ⌜s m = x⌝ THEN asm_rewrite_tac[]));
a(DROP_NTH_ASM_T  6 (ante_tac o ∀_elim ⌜(λm⦁ if s m = x then s' m else s m)⌝) THEN
	asm_rewrite_tac[]);
a(DROP_ASMS_T discard_tac THEN rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(DROP_NTH_ASM_T 2 ante_tac THEN cases_tac⌜s m = x⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
Using the shift theorem, we can now prove a further sharpening of
the characterisation of continuity in terms of sequence convergence.
%%%%
%%%%
=SML

val ⦏cts_lim_seq_thm2⦎ = save_thm ( "cts_lim_seq_thm2", (
set_goal([], ⌜∀f x⦁
	f Cts x ⇔
	∃a b⦁ a < x ∧ x < b ∧
	(∀s⦁ s -> x ∧ (∀m⦁¬s m = x ∧ a < s m ∧ s m < b) ⇒ (λm⦁f(s m)) -> f x)⌝);
a(rewrite_tac[cts_lim_seq_thm1] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜x + ~(ℕℝ 1)⌝ THEN ∃_tac⌜x + ℕℝ 1⌝ THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 3 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(GET_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[lim_seq_def]));
a(LIST_GET_NTH_ASM_T [5, 6]
	(MAP_EVERY(strip_asm_tac o once_rewrite_rule[ℝ_less_0_less_thm])));
a(LIST_GET_NTH_ASM_T [3] all_fc_tac);
a(once_rewrite_tac[∀_elim⌜n + n'⌝lim_seq_shift_thm]);
a(rewrite_tac[]);
a(LEMMA_T⌜∀i j k⦁ s(i+j+k)=(λi⦁s(i + j + k))i⌝ once_rewrite_thm_tac THEN1
	rewrite_tac[]);
a(DROP_NTH_ASM_T 8 bc_thm_tac);
a(ALL_FC_T asm_rewrite_tac[lim_seq_shift_thm] THEN contr_tac
	THEN POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_less_≤_thm]));
(* *** Goal "2.1" *** *)
a(lemma_tac ⌜ℕℝ 0 ≤ ~(s(m+n+n')) + x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜¬Abs(~(~(s(m+n+n')) + x)) < x + ~a⌝ ante_tac THEN1
	(asm_rewrite_tac[ℝ_abs_minus_thm] THEN 
	asm_rewrite_tac[ℝ_abs_def] THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(rewrite_tac[] THEN GET_NTH_ASM_T 4 bc_thm_tac THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac ⌜ℕℝ 0 ≤ s(m+n+n') + ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜¬Abs(s(m+n+n') + ~x) < b + ~x⌝ ante_tac THEN1
	(asm_rewrite_tac[ℝ_abs_def] THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(rewrite_tac[] THEN GET_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX
Now we give the useful result that continuity is a local property: i.e.,
if two functions agree in a neighbourhood of a point and
one is continuous at that point then so is the other:
%%%%
%%%%
=SML

val ⦏cts_local_thm⦎ = save_thm ( "cts_local_thm", (
set_goal([], ⌜∀f g x a b⦁
	a < x ∧ x < b
∧	(∀y⦁ a < y ∧ y < b ⇒ f y = g y)
∧	g Cts x
⇒	f Cts x ⌝);
a(REPEAT strip_tac THEN rewrite_tac[cts_lim_seq_thm2]);
a(∃_tac⌜a⌝ THEN ∃_tac⌜b⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜∀m⦁f(s m) = g(s m)⌝rewrite_thm_tac THEN1
	(REPEAT strip_tac THEN
	spec_nth_asm_tac 1 ⌜m:ℕ⌝ THEN
	all_asm_fc_tac[]));
a(LEMMA_T⌜f x = g x⌝rewrite_thm_tac THEN1 all_asm_fc_tac[]);
a(GET_NTH_ASM_T 3 (bc_thm_tac o rewrite_rule[cts_lim_seq_thm]) THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
We now show that the polynomial constructions preserve limits.
%%%%
%%%%
=SML

val ⦏const_cts_thm⦎ = save_thm ( "const_cts_thm", (
set_goal([], ⌜∀c t⦁ (λx⦁c) Cts t⌝);
a(REPEAT strip_tac THEN rewrite_tac[cts_lim_seq_thm, const_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏id_cts_thm⦎ = save_thm ( "id_cts_thm", (
set_goal([], ⌜∀t⦁ (λx⦁x) Cts t⌝);
a(REPEAT strip_tac THEN rewrite_tac[cts_lim_seq_thm, η_axiom]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_cts_thm⦎ = save_thm ( "plus_cts_thm", (
set_goal([], ⌜∀f g t⦁ f Cts t ∧ g Cts t ⇒ (λx⦁f x + g x) Cts t⌝);
a(rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [plus_lim_seq_thm]);
a(rewrite_tac[] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_cts_thm⦎ = save_thm ( "times_cts_thm", (
set_goal([], ⌜∀f g t⦁ f Cts t ∧ g Cts t ⇒ (λx⦁f x * g x) Cts t⌝);
a(rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [times_lim_seq_thm]);
a(rewrite_tac[] THEN taut_tac);
pop_thm()
));

=TEX
Now we can show that polynomial functions are continuous everywhere.
We could do this by polynomial induction using the theorems just
proved, but it's even easier to use the last result from the previous section:
%%%%
%%%%
=SML

val ⦏poly_cts_thm⦎ = save_thm ( "poly_cts_thm", (
set_goal([], ⌜∀f t⦁ f ∈ PolyFunc ⇒ f Cts t⌝);
a(rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac
	THEN ALL_FC_T rewrite_tac[poly_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏comp_cts_thm⦎ = save_thm ( "comp_cts_thm", (
set_goal([], ⌜∀f g t⦁ f Cts g t ∧ g Cts t ⇒ (λx⦁f(g x)) Cts t⌝);
a(rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac);
a(all_asm_fc_tac[] THEN all_asm_fc_tac[]);
a(POP_ASM_T ante_tac THEN rewrite_tac[η_axiom]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏minus_cts_thm⦎ = save_thm ( "minus_cts_thm", (
set_goal([], ⌜∀t⦁~ Cts t⌝);
a(LEMMA_T ⌜~ = (λx⦁(λx⦁~(ℕℝ 1)) x * (λx⦁x) x)⌝ pure_once_rewrite_thm_tac
	THEN1 (rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(strip_tac THEN bc_thm_tac times_cts_thm);
a(rewrite_tac[const_cts_thm, id_cts_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏minus_comp_cts_thm⦎ = save_thm ( "minus_comp_cts_thm", (
set_goal([], ⌜∀f t⦁f Cts t ⇒ (λx⦁~(f x)) Cts t⌝);
a(REPEAT strip_tac);
a(bc_thm_tac comp_cts_thm THEN REPEAT strip_tac);
a(rewrite_tac[minus_cts_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏recip_cts_thm⦎ = save_thm ( "recip_cts_thm", (
set_goal([], ⌜∀t⦁ ¬t = ℕℝ 0 ⇒ $⋏-⋏1 Cts t⌝);
a(rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac);
a(bc_thm_tac recip_lim_seq_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏recip_comp_cts_thm⦎ = save_thm ( "recip_comp_cts_thm", (
set_goal([], ⌜∀f t⦁f Cts t ∧ ¬f t = ℕℝ 0 ⇒ (λx⦁(f x)⋏-⋏1) Cts t⌝);
a(REPEAT strip_tac);
a(bc_thm_tac comp_cts_thm THEN REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[recip_cts_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏ℝ_ℕ_exp_cts_thm⦎ = save_thm ( "ℝ_ℕ_exp_cts_thm", (
set_goal([], ⌜∀m:ℕ; t⦁ (λx⦁x^m) Cts t⌝);
a(REPEAT strip_tac THEN induction_tac ⌜m:ℕ⌝
	THEN rewrite_tac[ℝ_ℕ_exp_def, const_cts_thm]);
a(ho_bc_thm_tac times_cts_thm);
a(asm_rewrite_tac[id_cts_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_comp_cts_thm⦎ = save_thm ( "ℝ_ℕ_exp_comp_cts_thm", (
set_goal([], ⌜∀f; m:ℕ; t⦁f Cts t ⇒ (λx⦁f x ^ m) Cts t⌝);
a(REPEAT strip_tac);
a(pure_rewrite_tac[prove_rule[]
	⌜(λx⦁f x ^ m) = (λx⦁(λy⦁y ^ m)(f x))⌝]);
a(bc_thm_tac comp_cts_thm THEN REPEAT strip_tac);
a(rewrite_tac[ℝ_ℕ_exp_cts_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏abs_cts_thm⦎ = save_thm ( "abs_cts_thm", (
set_goal([], ⌜∀t⦁ Abs Cts t⌝);
a(rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac);
a(all_fc_tac[abs_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏abs_comp_cts_thm⦎ = save_thm ( "abs_comp_cts_thm", (
set_goal([], ⌜∀f m t⦁f Cts t ⇒ (λx⦁Abs(f x)) Cts t⌝);
a(REPEAT strip_tac);
a(bc_thm_tac comp_cts_thm THEN REPEAT strip_tac);
a(rewrite_tac[abs_cts_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏simple_cts_tac⦎ : TACTIC = (fn gl as (_, tm) => 
	let	val x = snd(dest_app tm);
		val const_thm = all_∀_intro(⇔_t_intro(all_∀_elim const_cts_thm));
		val id_thm = all_∀_intro(⇔_t_intro(all_∀_elim id_cts_thm));
	in
	conv_tac (simple_eq_match_conv const_thm) ORELSE
	conv_tac (simple_eq_match_conv id_thm) ORELSE
	(conv_tac (LEFT_C λ_un_β_rands_conv) THEN 
		(FIRST (map bc_thm_tac [
			plus_cts_thm, times_cts_thm,
			minus_comp_cts_thm, recip_comp_cts_thm,
			abs_comp_cts_thm])
		ORELSE (conv_tac (LEFT_C(SIMPLE_λ_C (RIGHT_C(β_conv))))
			THEN FIRST (map bc_thm_tac [
				ℝ_ℕ_exp_comp_cts_thm])))) ORELSE
	conv_tac (LEFT_C η_conv ORELSE_C RAND_C (LEFT_C β_conv))
	end	gl
);
=IGN
set_goal([], ⌜(λx⦁c) Cts (ℕℝ 2)⌝);
a simple_cts_tac;
val test1 = pop_thm();
set_goal([], ⌜(λx⦁x* Abs y + ℕℝ 3) Cts t⌝);
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
val test2 = pop_thm();
set_goal([], ⌜(λx⦁ℕℝ 3 * ((1/2)+x^7)⋏-⋏1) Cts 1/3⌝);
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(rewrite_tac[]);
val test2 = pop_thm();
=TEX
Another useful lemma says any function continuous
on a closed interval can be extended to a function continuous
on the whole line.
It is occasionally useful to know the chosen values of the continuous extension
so we prove that stronger form first and then derive the weaker one from it.
For various reasons, we formulate the stronger form with the equations
arranged to map in the other order.
%%%%
%%%%
=SML

val ⦏cts_extension_thm1⦎ = save_thm ( "cts_extension_thm1", (
set_goal([], ⌜∀a b f⦁
	a < b
∧	(∀x⦁ a ≤ x ∧ x ≤ b ⇒ f Cts x)
⇒	(∃g⦁
		(∀x⦁ a ≤ x ∧ x ≤ b ⇒ g x = f x)
	∧	(∀x⦁x < a ⇒ g x = f a)
	∧	(∀x⦁b < x ⇒ g x = f b)
	∧	(∀x⦁ g Cts x)) ⌝);
a(REPEAT strip_tac);
a(∃_tac⌜λz⦁
	if	z < a
	then	f a
	else if	b < z
	then	f b
	else	f z⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T⌜¬x < a ∧ ¬ b < x⌝ asm_rewrite_thm_tac THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(LEMMA_T⌜¬x < a⌝  asm_rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(cases_tac⌜x < a⌝ THEN1 bc_thm_tac cts_local_thm);
(* *** Goal "4.1" *** *)
a(∃_tac⌜λx⦁f a⌝ THEN ∃_tac⌜a⌝ THEN ∃_tac⌜x + ~(ℕℝ 1)⌝ THEN
	asm_rewrite_tac[const_cts_thm] THEN REPEAT strip_tac THEN
	asm_rewrite_tac[]);
(* *** Goal "4.2" *** *)
a(cases_tac⌜x = a⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "4.2.1" *** *)
a(rewrite_tac[cts_lim_seq_thm2]);
a(POP_ASM_T ante_tac THEN rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac);
a(∃_tac⌜a + ~(ℕℝ 1)⌝ THEN ∃_tac⌜b⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜¬b < a ⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜∀m⦁¬b < s m⌝rewrite_thm_tac THEN1
	(REPEAT strip_tac THEN
	spec_nth_asm_tac 1 ⌜m:ℕ⌝ THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LEMMA_T ⌜∀m:ℕ⦁
	f a = (λi⦁ f a)m
∧ 	f (s m) = (λi⦁f(s i))m
∧	(s m < a ⇔ (λi⦁s i < a) m)⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac lim_seq_choice_thm THEN rewrite_tac[const_lim_seq_thm]);
a(SPEC_NTH_ASM_T 3 ⌜a⌝ ante_tac);
a(LEMMA_T ⌜a ≤ b⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "4.2.2" *** *)
a(cases_tac⌜x < b⌝ THEN1 bc_thm_tac cts_local_thm);
(* *** Goal "4.2.2.1" *** *)
a(lemma_tac ⌜a < x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(∃_tac⌜f⌝ THEN ∃_tac⌜b⌝ THEN ∃_tac⌜a⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN1 
	(LEMMA_T ⌜¬y < a ∧ ¬b < y⌝rewrite_thm_tac THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(GET_NTH_ASM_T 5 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4.2.2.2" *** *)
a(cases_tac⌜x = b⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "4.2.2.2.1" *** *)
a(LIST_DROP_NTH_ASM_T [1,2] discard_tac THEN rewrite_tac[cts_lim_seq_thm2]);
a(POP_ASM_T ante_tac THEN rewrite_tac[cts_lim_seq_thm] THEN REPEAT strip_tac);
a(∃_tac⌜a⌝ THEN ∃_tac⌜b + ℕℝ 1⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜¬b < a ⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜∀m⦁¬s m < a⌝rewrite_thm_tac THEN1
	(REPEAT strip_tac THEN
	spec_nth_asm_tac 1 ⌜m:ℕ⌝ THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LEMMA_T ⌜∀m:ℕ⦁
	f b = (λi⦁ f b)m
∧ 	f (s m) = (λi⦁f(s i))m
∧	(b < s m ⇔ (λi⦁b < s i) m)⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac lim_seq_choice_thm THEN rewrite_tac[const_lim_seq_thm]);
a(SPEC_NTH_ASM_T 3 ⌜b⌝ ante_tac);
a(LEMMA_T ⌜a ≤ b⌝ rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "4.2.2.2.2" *** *)
a(LEMMA_T ⌜b < x⌝ ante_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [1,2,3,4] discard_tac THEN strip_tac);
a(all_fc_tac[∀_elim⌜b⌝ℝ_less_dense_thm]);
a(bc_thm_tac cts_local_thm);
a(∃_tac⌜λx⦁f b⌝ THEN ∃_tac⌜x + ℕℝ 1⌝ THEN ∃_tac⌜b⌝ THEN
	asm_rewrite_tac[const_cts_thm] THEN REPEAT strip_tac THEN
	asm_rewrite_tac[]);
a(LEMMA_T ⌜¬y < a⌝ rewrite_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The weaker form of the extension theorem can now easily be derived:
%%%%
%%%%
=SML

val ⦏cts_extension_thm⦎ = save_thm ( "cts_extension_thm", (
set_goal([], ⌜∀a b f⦁
	a < b
∧	(∀x⦁ a ≤ x ∧ x ≤ b ⇒ f Cts x)
⇒	(∃g⦁ (∀x⦁ a ≤ x ∧ x ≤ b ⇒ g x = f x) ∧ (∀x⦁ g Cts x)) ⌝);
a(REPEAT strip_tac);
a(all_fc_tac[cts_extension_thm1]);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{A little Topology}
%%%%
%%%%
%%%%
%%%%
Mainly for use in one or two applications of the compactness of a closed interval
we need some elementary facts of a topological nature.

Our definition of an open set is the standard one.
A ``$\delta$'' characterisation which is closer to the style
used in the definitions of sequence convergence etc. is useful.
%%%%
%%%%
=SML

val ⦏open_ℝ_delta_thm⦎ = save_thm ( "open_ℝ_delta_thm", (
set_goal([], ⌜∀A⦁
	A ∈ Open⋎R
⇔	(∀t⦁ t ∈ A ⇒ ∃d⦁ℕℝ 0 < d ∧ ∀y⦁ Abs(y - t) < d ⇒ y ∈ A)
⌝);
a(rewrite_tac[open_ℝ_def, open_interval_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
a(cases_tac⌜t + ~x < y + ~t⌝);
(* *** Goal "1.1" *** *)
a(∃_tac⌜t + ~x⌝ THEN REPEAT strip_tac THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜x < y' ∧ y' < y⌝ THEN1
	(LIST_DROP_NTH_ASM_T [1,2,4,5] (MAP_EVERY ante_tac) THEN
	DROP_ASMS_T discard_tac THEN
	cases_tac⌜ℕℝ 0 ≤ y' + ~t⌝ THEN
	asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜y + ~t⌝ THEN REPEAT strip_tac THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜x < y' ∧ y' < y⌝ THEN1
	(LIST_DROP_NTH_ASM_T [1,2,4,5] (MAP_EVERY ante_tac) THEN
	DROP_ASMS_T discard_tac THEN
	cases_tac⌜ℕℝ 0 ≤ y' + ~t⌝ THEN
	asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
a(∃_tac⌜t + ~d⌝ THEN ∃_tac⌜t + d⌝ THEN REPEAT strip_tac THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(GET_NTH_ASM_T 3 bc_thm_tac);
a(LIST_DROP_NTH_ASM_T [1,2,4] (MAP_EVERY ante_tac) THEN
	DROP_ASMS_T discard_tac THEN
	cases_tac⌜ℕℝ 0 ≤ x + ~t⌝ THEN
	asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Now we give the topological characterisation of sequence convergence.
%%%%
%%%%
=SML

val ⦏lim_seq_open_ℝ_thm⦎ = save_thm ( "lim_seq_open_ℝ_thm", (
set_goal([], ⌜∀s x⦁
	(s -> x)
⇔	(∀A⦁ A ∈ Open⋎R ∧ x ∈ A ⇒ ∃n⦁∀m⦁ n ≤ m ⇒ s m ∈ A)⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT ∀_tac THEN ⇔_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[open_ℝ_delta_thm] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(LIST_GET_NTH_ASM_T [5] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [2,3] bc_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN
	rewrite_tac[open_ℝ_def, open_interval_def] THEN
	REPEAT strip_tac);
a(swap_nth_asm_concl_tac 2 THEN REPEAT strip_tac);
a(∃_tac ⌜{z | x + ~e < z ∧ z < x + e}⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(∃_tac⌜x + ~e⌝ THEN ∃_tac⌜x + e⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.3" *** *)
a(swap_nth_asm_concl_tac 1 THEN REPEAT strip_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(LIST_DROP_NTH_ASM_T [1,2] (MAP_EVERY ante_tac) THEN
	DROP_ASMS_T discard_tac THEN
	cases_tac⌜ℕℝ 0 ≤ s m + ~x⌝ THEN
	asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
We now prove the usual topological characterisation of continuity in
terms of open sets. To avoid complications with relative topologies for now
we just do the cases where the function is continuous on the whole line or on an open set:
=TEX
%%%%
%%%%
=SML

val ⦏cts_open_ℝ_thm⦎ = save_thm ( "cts_open_ℝ_thm", (
set_goal([], ⌜∀f⦁
	(∀x⦁ f Cts x)
⇔	(∀A⦁ A ∈ Open⋎R ⇒ {x | f x ∈ A} ∈ Open⋎R)
⌝);
a(REPEAT_N 3 strip_tac);
a(rewrite_tac[cts_def, open_ℝ_delta_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
a(list_spec_nth_asm_tac 5 [⌜t⌝, ⌜d⌝]);
a(∃_tac⌜d'⌝ THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T[2, 4] bc_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(rewrite_tac[cts_lim_seq_thm, lim_seq_open_ℝ_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(spec_nth_asm_tac 4 ⌜{x | f x ∈ A}⌝);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
The following is used in our proof of the fact that closed intervals are compact:
%%%%
%%%%
=SML

val ⦏closed_interval_closed_thm⦎ = save_thm ( "closed_interval_closed_thm", (
set_goal([], ⌜∀x y⦁ClosedInterval x y ∈ Closed⋎R⌝);
a(rewrite_tac[
	closed_interval_def, closed_ℝ_def, open_ℝ_def, open_interval_def] THEN 
	REPEAT strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(∃_tac⌜t + ~(ℕℝ 1)⌝ THEN ∃_tac ⌜x⌝ THEN
	PC_T1 "sets_ext1" REPEAT strip_tac THEN
	REPEAT strip_tac);
a(rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(∃_tac⌜y⌝ THEN ∃_tac ⌜t + ℕℝ 1⌝ THEN
	PC_T1 "sets_ext1" REPEAT strip_tac
	THEN REPEAT strip_tac);
a(rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The following is useful later, e.g., in proving that the derivative of a function is zero at a local
maximum.
%%%%
%%%%
=SML

val ⦏cts_estimate_thm⦎ = save_thm ( "cts_estimate_thm", (
set_goal([], ⌜∀f x lb ub⦁
	f Cts x
∧	(∀d⦁ℕℝ 0 < d ⇒ (∃z⦁ Abs(z - x) < d ∧ lb ≤ f z) ∧ (∃z⦁ Abs(z - x) < d ∧ f z ≤ ub))
⇒	lb ≤ f x ∧ f x ≤ ub⌝);
a(rewrite_tac[cts_def] THEN contr_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜ℕℝ 0 < lb + ~(f x)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(DROP_NTH_ASM_T 3 (fn th => LIST_DROP_NTH_ASM_T [4] all_fc_tac THEN asm_tac th));
a(LIST_DROP_NTH_ASM_T [6] (ALL_FC_T (MAP_EVERY ante_tac)));
a(cases_tac ⌜ℕℝ 0 ≤ f z + ~(f x)⌝ THEN asm_rewrite_tac[ℝ_abs_def] THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜ℕℝ 0 < f x + ~ub⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(DROP_NTH_ASM_T 3 (fn th => LIST_DROP_NTH_ASM_T [4] all_fc_tac THEN asm_tac th));
a(LIST_DROP_NTH_ASM_T [6] (ALL_FC_T (MAP_EVERY ante_tac)));
a(cases_tac ⌜ℕℝ 0 ≤ f z' + ~(f x)⌝ THEN asm_rewrite_tac[ℝ_abs_def] THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
=SML

val ⦏cts_estimate_0_thm⦎ = save_thm ( "cts_estimate_0_thm", (
set_goal([], ⌜∀f x⦁
	f Cts x
∧	(∀d⦁
		ℕℝ 0 < d
	⇒	(∃z⦁ Abs(z - x) < d ∧ ℕℝ 0 ≤ f z)
	∧	(∃z⦁ Abs(z - x) < d ∧ f z ≤ ℕℝ 0))
⇒	f x = ℕℝ 0⌝);
a(REPEAT strip_tac);
a(all_fc_tac[cts_estimate_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cts_limit_unique_thm⦎ = save_thm ( "cts_limit_unique_thm", (
set_goal([], ⌜∀f g x a b⦁
	a < x ∧ x < b
∧	f Cts x ∧ g Cts x
∧	(∀y⦁a < y ∧ y < b ∧ ¬y = x ⇒ f y = g y)
⇒	f x = g x⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜(λz⦁f z + ~(g z)) x = ℕℝ 0⌝
	(fn th => ante_tac th THEN rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(bc_thm_tac cts_estimate_0_thm THEN ∧_tac
	THEN1 REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(REPEAT ∀_tac THEN ⇒_tac THEN rewrite_tac[]);
a(lemma_tac⌜∃ z⦁ Abs (z + ~x) < d ∧  f z + ~ (g z) = ℕℝ 0 ⌝);
(* *** Goal "1" *** *)
a(lemma_tac⌜∃c⦁ℕℝ 0 < c ∧ c < b + ~x ∧ c < d⌝ THEN1
	(bc_thm_tac ℝ_bound_below_2_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜a < x + c ∧ x + c < b ∧ ¬x + c = x ∧ ℕℝ 0 ≤ (x + c) + ~x⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(∃_tac⌜x + c⌝ THEN asm_rewrite_tac[ℝ_abs_def]);
a(all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN ∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The following theorem is a sometimes useful criterion for continuity, allowing
us to focus attention on values inside an arbitrarily small open interval containing
the point at which continuity is asserted:
%%%%
%%%%
=SML

val ⦏cts_open_interval_thm⦎ = save_thm ( "cts_open_interval_thm", (
set_goal([], ⌜∀f a b x⦁
	f x ∈ OpenInterval a b
∧	(∀c d⦁ f x ∈ OpenInterval c d  ∧ ClosedInterval c d ⊆ OpenInterval a b ⇒ 
		∃s t⦁x ∈ OpenInterval s t ∧ ∀y⦁y ∈ OpenInterval s t ⇒ f y ∈ OpenInterval c d)
⇒	f Cts x⌝);
a(rewrite_tac[open_interval_def, closed_interval_def, cts_def, ⊆_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < b + ~(f x) ∧ ℕℝ 0 < f x + ~a⌝ THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(strip_asm_tac (list_∀_elim[⌜e⌝, ⌜f x + ~a⌝, ⌜b + ~(f x)⌝] ℝ_bound_below_3_thm));
a(lemma_tac⌜a < f x + ~d ∧ f x + d < b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 10 (ante_tac o list_∀_elim[⌜f x + ~d⌝, ⌜f x + d⌝]));
a(asm_rewrite_tac[]);
a(LEMMA_T ⌜~ d < ℕℝ 0 ∧ (∀ x'⦁ f x + ~ d ≤ x' ∧ x' ≤ f x + d ⇒ a < x' ∧ x' < b)⌝
	rewrite_thm_tac THEN1
	(REPEAT strip_tac THEN_LIST
		[PC_T1 "ℝ_lin_arith" asm_prove_tac[],
		all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[],
		all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]]));
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
a(lemma_tac⌜ℕℝ 0 < x + ~s ∧ ℕℝ 0 < t + ~x⌝ THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(strip_asm_tac (list_∀_elim[⌜x + ~s⌝, ⌜t + ~x⌝] ℝ_bound_below_2_thm));
a(∃_tac⌜d'⌝ THEN ALL_FC_T1 fc_⇔_canon asm_rewrite_tac [ℝ_abs_diff_bounded_thm]);
a(∀_tac THEN ⇒_tac);
a(lemma_tac⌜s < y ∧ y < t⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [11] all_fc_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The following theorem says that if a function is Darboux continuous (i.e., if it
satisfies the conclusion of the intermediate value theorem) and monotonic
increasing in an interval then it is continuous.
We state this in two versions, the first deals with a function monotonic on a closed interval:
%%%%
%%%%
=SML

val ⦏darboux_cts_mono_thm⦎ = save_thm ( "darboux_cts_mono_thm", (
set_goal([], ⌜∀f a b x⦁
	(∀x y⦁ x ∈ ClosedInterval a b ∧ y ∈ ClosedInterval a  b ∧ x < y ⇒ f x < f y)
∧	(∀y⦁ y ∈ OpenInterval (f a) (f b) ⇒ ∃x⦁a < x ∧ x < b  ∧ f x = y)
∧	 x ∈ OpenInterval a b
⇒	f Cts x⌝);
a(rewrite_tac[open_interval_def, closed_interval_def] THEN REPEAT strip_tac);
a(bc_thm_tac cts_open_interval_thm THEN
	rewrite_tac[open_interval_def, ⊆_def, closed_interval_def] );
a(∃_tac⌜f b⌝ THEN ∃_tac⌜f a⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜c ≤ d⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 2  ⌜c⌝ THEN spec_nth_asm_tac 4 ⌜d⌝);
a(LIST_DROP_NTH_ASM_T [11] all_fc_tac THEN all_var_elim_asm_tac1);
a(rename_tac[(⌜x'⌝, "U"), (⌜x''⌝, "L")] THEN ∃_tac⌜L:ℝ⌝ THEN ∃_tac⌜U:ℝ⌝);
(* *** Goal "3.1" *** *)
a(lemma_tac⌜¬x = L ∧ ¬x = U⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac1));
a(lemma_tac⌜¬x <  L⌝ THEN1
	(contr_tac THEN LEMMA_T⌜f x < f L⌝ 
		(fn th => ante_tac th THEN GET_ASM_T ⌜f L < f x⌝ ante_tac
			THEN PC_T1 "ℝ_lin_arith" prove_tac[])
		THEN GET_NTH_ASM_T 18 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜¬U < x⌝ THEN1
	(contr_tac THEN LEMMA_T⌜f U < f x⌝ 
		(fn th => ante_tac th THEN GET_ASM_T ⌜f x < f U⌝ ante_tac
			THEN PC_T1 "ℝ_lin_arith" prove_tac[])
		THEN GET_NTH_ASM_T 19 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜L < x ∧ x < U⌝ THEN1 
	(LIST_DROP_NTH_ASM_T (interval 5 19) discard_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LIST_DROP_NTH_ASM_T [3, 4, 5, 6] discard_tac);
a(asm_rewrite_tac[] THEN REPEAT strip_tac
	THEN DROP_NTH_ASM_T 19 bc_thm_tac THEN
		PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The second version deals with a function monotonic on an open interval:
%%%%
%%%%
=SML

val ⦏darboux_cts_mono_thm1⦎ = save_thm ( "darboux_cts_mono_thm1", (
set_goal([], ⌜∀f a b x⦁
	(∀x y⦁ x ∈ OpenInterval a b ∧ y ∈ OpenInterval a b ∧ x < y ⇒ f x < f y)
∧	(∀x y z⦁ x ∈ OpenInterval a b ∧ y ∈ OpenInterval a b ∧ z ∈ OpenInterval (f x) (f y) ⇒ ∃t⦁ t ∈ OpenInterval a b ∧ f t = z)
∧	 x ∈ OpenInterval a b
⇒	f Cts x⌝);
a(rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
a(bc_thm_tac darboux_cts_mono_thm);
a(lemma_tac⌜∃a0 b0⦁ a < a0 ∧ a0 < x ∧ x < b0 ∧ b0 < b⌝
	THEN1 (∃_tac⌜1/2*(a+x)⌝ THEN ∃_tac⌜1/2*(x+b)⌝
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜b0⌝ THEN ∃_tac⌜a0⌝
	THEN rewrite_tac[open_interval_def, closed_interval_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 13 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∃t⦁ (a < t ∧ t < b) ∧ f t = y⌝
	THEN1 (DROP_NTH_ASM_T 9 bc_thm_tac
		THEN ∃_tac⌜b0⌝ THEN ∃_tac⌜a0⌝
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜t⌝ THEN all_var_elim_asm_tac1);
a(lemma_tac⌜a < b0 ∧ a0 < b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜a0 = t⌝ THEN1 all_var_elim_asm_tac1);
a(cases_tac⌜b0 = t⌝ THEN1 all_var_elim_asm_tac1);
a(cases_tac⌜t < a0⌝ THEN1
	(LIST_DROP_NTH_ASM_T [17] all_fc_tac
		THEN all_fc_tac[ℝ_less_antisym_thm]));
a(cases_tac⌜b0 < t⌝ THEN1
	(LIST_DROP_NTH_ASM_T [18] all_fc_tac
		THEN all_fc_tac[ℝ_less_antisym_thm]));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Derivatives}
%%%%
%%%%
%%%%
%%%%
Following Harrison, we make much use of Carath\'{e}odory's characterisation
of the derivative in terms of the continuity of a certain function:
%%%%
%%%%
=SML

val ⦏caratheodory_deriv_thm⦎ = save_thm ( "caratheodory_deriv_thm", (
set_goal([], ⌜∀f c x⦁
	(f Deriv c) x
⇔	(∃g⦁ (∀y⦁f y - f x = g(y)*(y - x)) ∧ g Cts x ∧ g x = c)
⌝);
a(rewrite_tac[deriv_def, cts_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜λz⦁ if z = x then c else (f z - f x)/(z - x)⌝
	THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(cases_tac⌜y = x⌝ THEN asm_rewrite_tac[]);
a(lemma_tac⌜¬(y + ~x) = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rename_tac[(⌜x⌝, "x'")] THEN
	ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b⦁(a*b)*(y + ~x') = a * (y + ~x') * b⌝]);
a(ALL_FC_T rewrite_tac[ℝ_times_recip_thm]);
(* *** Goal "1.2" *** *)
a(all_asm_fc_tac[]);
a(∃_tac⌜d⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜Abs(ℕℝ 0) = ℕℝ 0⌝ THEN1 rewrite_tac[ℝ_abs_eq_0_thm]);
a(cases_tac⌜y = x⌝ THEN1 asm_rewrite_tac[]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[]);
a(∃_tac⌜d⌝ THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
a(lemma_tac⌜¬(y + ~x) = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rename_tac[(⌜x⌝, "x'")] THEN
	ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(rewrite_tac[ℝ_times_assoc_thm] THEN ALL_FC_T rewrite_tac[ℝ_times_recip_thm]);
a(all_var_elim_asm_tac1 THEN DROP_NTH_ASM_T 4 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏deriv_cts_thm⦎ = save_thm ( "deriv_cts_thm", (
set_goal([], ⌜∀f c x⦁ (f Deriv c) x ⇒ f Cts x⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(LEMMA_T ⌜f = λz⦁g z *(z + ~x) + f x⌝ once_rewrite_thm_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜x'⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏const_deriv_thm⦎ = save_thm ( "const_deriv_thm", (
set_goal([], ⌜∀c t⦁ ((λx⦁c) Deriv ℕℝ 0) t⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(∃_tac⌜λz⦁ℕℝ 0⌝ THEN rewrite_tac[]);
a(simple_cts_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏id_deriv_thm⦎ = save_thm ( "id_deriv_thm", (
set_goal([], ⌜∀t⦁ ((λx⦁x) Deriv ℕℝ 1) t⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(∃_tac⌜λz⦁ℕℝ 1⌝ THEN rewrite_tac[]);
a(simple_cts_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_deriv_thm⦎ = save_thm ( "plus_deriv_thm", (
set_goal([], ⌜∀f1 c1 x f2 c2⦁
	(f1 Deriv c1) x ∧ (f2 Deriv c2) x
⇒	((λy⦁f1 y + f2 y) Deriv (c1 + c2)) x⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(rename_tac[(⌜g⌝, "g1"), (⌜g'⌝, "g2")] THEN
	∃_tac⌜λz:ℝ⦁ g1 z + g2 z:ℝ⌝ THEN asm_rewrite_tac[]);
a(ALL_FC_T rewrite_tac[plus_cts_thm]);
a(once_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀a b c d:ℝ⦁ (a + b) + c + d = (a + c) + b + d⌝]);
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_const_deriv_thm⦎ = save_thm ( "plus_const_deriv_thm", (
set_goal([], ⌜∀c x : ℝ⦁ ($+ c Deriv ℕℝ 1) x⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule[]⌜$+ c = λz⦁(λz⦁c) z + (λz⦁z) z⌝]);
a(conv_tac (RATOR_C (RIGHT_C(eq_match_conv
	(prove_rule[]⌜ℕℝ 1 = ℕℝ 0 + ℕℝ 1⌝)))));
a(bc_thm_tac plus_deriv_thm);
a(rewrite_tac [const_deriv_thm, id_deriv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_deriv_thm⦎ = save_thm ( "times_deriv_thm", (
set_goal([], ⌜∀f1 c1 x f2 c2⦁
	(f1 Deriv c1) x ∧ (f2 Deriv c2) x
⇒	((λy⦁f1 y * f2 y) Deriv (c1*f2 x + f1 x*c2)) x⌝);
a(REPEAT strip_tac THEN lemma_tac⌜f2 Cts x⌝ 
	THEN1 all_fc_tac[deriv_cts_thm]);
a(all_asm_ante_tac THEN
	rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(rename_tac[(⌜g⌝, "g1"), (⌜g'⌝, "g2")] THEN
	∃_tac⌜λz:ℝ⦁ g1 z*f2 z +  f1 x*g2 z:ℝ⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[pc_rule1"ℝ_lin_arith"prove_rule[]
	⌜∀a b c d:ℝ⦁a*b + ~(c*d) = (a + ~c)*b + c*(b + ~d)⌝]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_const_deriv_thm⦎ = save_thm ( "times_const_deriv_thm", (
set_goal([], ⌜∀c x : ℝ⦁ ($* c Deriv c) x⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule[]⌜$* c = λz⦁(λz⦁c) z * (λz⦁z) z⌝]);
a(conv_tac (RATOR_C (RIGHT_C(eq_match_conv
	(prove_rule[]⌜c = ℕℝ 0 * (λ z⦁ z)x + (λz⦁c)x * ℕℝ 1⌝)))));
a(bc_thm_tac times_deriv_thm);
a(rewrite_tac [const_deriv_thm, id_deriv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏comp_deriv_thm⦎ = save_thm ( "comp_deriv_thm", (
set_goal([], ⌜∀f1 c1 f2 c2 x⦁
	(f1 Deriv c1) (f2 x) ∧ (f2 Deriv c2) x
⇒	((λy⦁f1(f2 y)) Deriv (c1*c2)) x⌝);
a(REPEAT strip_tac THEN lemma_tac⌜f2 Cts x⌝ 
	THEN1 all_fc_tac[deriv_cts_thm]);
a(all_asm_ante_tac THEN
	rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(rename_tac[(⌜g⌝, "g1"), (⌜g'⌝, "g2")] THEN
	∃_tac⌜λz:ℝ⦁ g1(f2 z)*g2 z:ℝ⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(bc_thm_tac comp_cts_thm THEN REPEAT strip_tac);
pop_thm()
));

val ⦏chain_rule_thm⦎ = comp_deriv_thm;
=TEX
%%%%
%%%%
=SML

val ⦏minus_deriv_thm⦎ = save_thm ( "minus_deriv_thm", (
set_goal([], ⌜∀c t⦁ (~ Deriv ~(ℕℝ 1)) t⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(∃_tac⌜λz⦁~(ℕℝ 1)⌝ THEN rewrite_tac[minus_comp_cts_thm, const_cts_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏minus_comp_deriv_thm⦎ = save_thm ( "minus_comp_deriv_thm", (
set_goal([], ⌜∀f c t⦁ (f Deriv c) t ⇒ ((λx⦁~(f x)) Deriv ~c) t⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN ∃_tac⌜λz⦁~(g z)⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN1 
	(once_rewrite_tac [pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜∀a b:ℝ⦁a = b ⇔ ~a = ~b⌝]
	THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[minus_comp_cts_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_ℕ_exp_deriv_thm⦎ = save_thm ( "ℝ_ℕ_exp_deriv_thm", (
set_goal([], ⌜∀n t⦁ ((λx⦁x^(n+1)) Deriv (ℕℝ n + ℕℝ 1)*t^n) t⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝);
(* *** Goal "1" *** *)
a(pure_rewrite_tac[ℝ_ℕ_exp_def] THEN rewrite_tac[id_deriv_thm]);
(* *** Goal "2" *** *)
a(pure_once_rewrite_tac[ℝ_ℕ_exp_def]);
a(pure_rewrite_tac[prove_rule[]⌜
	(λ x:ℝ⦁ x * x ^ (n + 1)) = λ x⦁ (λx⦁x) x * (λx⦁x ^ (n + 1))x⌝]);
a(LEMMA_T⌜
	(ℕℝ (n + 1) + ℕℝ 1) * t * t ^ n =
	ℕℝ 1*(λx⦁x^(n + 1))t + (λx⦁x) t*(ℕℝ n + ℕℝ 1)*t^n⌝
	pure_rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[ℕℝ_plus_homomorphism_thm, ℝ_ℕ_exp_def]);
a(conv_tac(RANDS_C ℝ_anf_conv) THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(bc_thm_tac times_deriv_thm);
a(asm_rewrite_tac[id_deriv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏recip_deriv_thm⦎ = save_thm ( "recip_deriv_thm", (
set_goal([], ⌜∀t⦁ ¬t = ℕℝ 0 ⇒ ($⋏-⋏1 Deriv ~(t ⋏-⋏1 * t ⋏-⋏1)) t⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(∃_tac⌜λy⦁
	if	y = t
	then	~(t ⋏-⋏1 * t ⋏-⋏1)
	else	(y ⋏-⋏1 + ~t ⋏-⋏1)*(y + ~t)⋏-⋏1⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(cases_tac⌜y = t⌝ THEN asm_rewrite_tac[ℝ_times_assoc_thm]);
a(POP_ASM_T (asm_tac o once_rewrite_rule[ℝ_eq_thm]));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses, ℝ_minus_recip_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[cts_lim_seq_thm1] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
a(all_fc_tac[lim_seq_¬_0_thm]);
a(once_rewrite_tac[∀_elim⌜n⌝ lim_seq_shift_thm] THEN rewrite_tac[]);
a(LEMMA_T ⌜∀n'⦁(s (n' + n) ⋏-⋏1 + ~ t ⋏-⋏1) * (s (n' + n) + ~ t) ⋏-⋏1
	= ~(s (n' + n) ⋏-⋏1 * t ⋏-⋏1)⌝ rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜¬s (n'+n) = ℕℝ 0⌝ THEN1
	(TOP_ASM_T bc_thm_tac THEN REPEAT strip_tac));
a(lemma_tac⌜¬~t = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_plus_recip_thm]);
a(lemma_tac⌜¬s(n'+n) + ~ t = ℕℝ 0⌝ THEN1
	(spec_nth_asm_tac 4 ⌜n'+n⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b c⦁
	(a * b * c) * a ⋏-⋏1= b * c * a * a ⋏-⋏1⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses, ℝ_minus_recip_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2.2" *** *)
a(LEMMA_T ⌜~ (t ⋏-⋏1 * t ⋏-⋏1) = t ⋏-⋏1 * ~(t ⋏-⋏1) ∧
	(λ n'⦁ ~ (s (n' + n) ⋏-⋏1 * t ⋏-⋏1)) =
	(λ n'⦁ (λm⦁ (λm'⦁s (m' + n)) m ⋏-⋏1) n' * (λm⦁~ (t ⋏-⋏1)) n')⌝
	 pure_rewrite_thm_tac THEN1
	(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN rewrite_tac[]));
a(bc_thm_tac times_lim_seq_thm THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(bc_thm_tac recip_lim_seq_thm THEN REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[lim_seq_shift_thm]);
(* *** Goal "2.2.2" *** *)
a(rewrite_tac[const_lim_seq_thm]);
(* *** Goal "3" *** *)
a(rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏recip_comp_deriv_thm⦎ = save_thm ( "recip_comp_deriv_thm", (
set_goal([], ⌜∀f c t⦁
	(f Deriv c) t
∧	¬f t = ℕℝ 0
⇒	((λx⦁ (f x) ⋏-⋏1) Deriv ~((f t) ⋏-⋏1 * (f t) ⋏-⋏1) * c ) t⌝);
a(REPEAT strip_tac);
a(all_fc_tac [recip_deriv_thm]);
a(all_fc_tac [comp_deriv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏poly_deriv_thm⦎ = save_thm ( "poly_deriv_thm", (
set_goal([], ⌜∀l x⦁ (PolyEval l Deriv PolyEval(DerivCoeffs l) x) x⌝);
a(REPEAT strip_tac THEN list_induction_tac⌜l : ℝ LIST⌝);
(* *** Goal "1" *** *)
a(rewrite_tac [deriv_coeffs_def]);
a(LEMMA_T ⌜PolyEval [] = λx⦁ℕℝ 0⌝ rewrite_thm_tac THEN1 rewrite_tac[poly_eval_def]);
a(rewrite_tac[const_deriv_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN rewrite_tac [deriv_coeffs_def] THEN rename_tac[(⌜x':ℝ⌝, "c")]);
a(LEMMA_T ⌜PolyEval (Cons c l) = λx⦁c+ x*PolyEval l x⌝ rewrite_thm_tac
	THEN1 rewrite_tac[poly_eval_def]);
a(rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv) plus_eval_thm]);
a(pure_once_rewrite_tac[prove_rule[]
	⌜(λ x⦁ c + x * PolyEval l x) = (λ x⦁ (λx⦁c) x + (λx⦁ x * PolyEval l x) x)⌝]);
a(conv_tac(RATOR_C (RIGHT_C (pure_once_rewrite_conv [prove_rule[]⌜∀x⦁x = ℕℝ 0 + x⌝]))));
a(bc_thm_tac plus_deriv_thm);
a(rewrite_tac [const_deriv_thm, poly_eval_def]);
a(pure_once_rewrite_tac[prove_rule[]
	⌜(λ x⦁ x * PolyEval l x) = (λ x⦁ (λx⦁ x) x  * PolyEval l x)⌝]);
a(pure_once_rewrite_tac[prove_rule[]
	⌜PolyEval l x + x *PolyEval (DerivCoeffs l) x
	= ℕℝ 1 * PolyEval l x + (λx⦁x) x * PolyEval (DerivCoeffs l) x⌝]);
a(bc_thm_tac times_deriv_thm);
a(asm_rewrite_tac[id_deriv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏deriv_local_thm⦎ = save_thm ( "deriv_local_thm", (
set_goal([], ⌜∀f g x a b c⦁
	a < x ∧ x < b
∧	(∀y⦁ a < y ∧ y < b ⇒ f y = g y)
∧	(g Deriv c) x
⇒	(f Deriv c) x ⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(∃_tac⌜λz⦁if  a < z ∧ z < b  then g' z else (f z + ~(f x))/(z + ~x)⌝
	THEN all_var_elim_asm_tac1 THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(cases_tac ⌜a < y ∧ y < b⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a(ALL_ASM_FC_T asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(lemma_tac ⌜¬y + ~x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rename_tac[(⌜x⌝, "u")] THEN ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(rewrite_tac[ℝ_times_assoc_thm] THEN  ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "1.3" *** *)
a(lemma_tac ⌜¬y + ~x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rename_tac[(⌜x⌝, "u")] THEN ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(rewrite_tac[ℝ_times_assoc_thm] THEN  ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2" *** *)
a(bc_thm_tac cts_local_thm);
a(MAP_EVERY ∃_tac [⌜g'⌝, ⌜b⌝, ⌜a⌝] THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
A function $f$ is differentiable with derivative $c$ at $x$ iff.
the function $(f(y) - f(x))/(y - x)$ of $y$ tends to $c$ at $x$.
This is a trivial consequence of the definitions.
%%%%
%%%%
=SML

val ⦏deriv_lim_fun_thm⦎ = save_thm ( "deriv_lim_fun_thm", (
set_goal([], ⌜∀f c x⦁ (f Deriv c) x ⇔ ((λy⦁(f y - f x)/(y - x)) --> c) x⌝);
a(rewrite_tac[lim_fun_def, deriv_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏deriv_unique_thm⦎ = save_thm ( "deriv_unique_thm", (
set_goal([], ⌜∀f x c d⦁ (f Deriv c) x ∧ (f Deriv d) x ⇒ c = d⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(bc_thm_tac cts_limit_unique_thm);
a(strip_asm_tac(∀_elim⌜x⌝ℝ_unbounded_below_thm)
	THEN strip_asm_tac (∀_elim⌜x⌝ℝ_unbounded_above_thm));
a(∃_tac⌜y'⌝ THEN ∃_tac⌜y⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜¬ y'' + ~x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜∀s t⦁s = t ⇔ s*(y'' + ~x) = t*(y'' + ~x)⌝ once_rewrite_thm_tac
	THEN1 (rename_tac[(⌜x⌝, "xx")]
		THEN ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_times_cancel_thm]));
a(LIST_GET_NTH_ASM_T[8, 10] (rewrite_tac o map (conv_rule(ONCE_MAP_C eq_sym_conv))));
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Proof Automation for Derivatives}
%%%%
%%%%
%%%%
%%%%
=TEX
Our tool for automating proof of derivatives will use
``$sho\_match$'' --- the following very special case of higher order matching: 
matching is as for ordinary first order matching except
that subterms of the form $f(x)$ where $f$ is a variable and $x$ is a bound
variable can match arbitrary expressions of the right type with
$e$ being matched to $(\lambda x\bullet e)x$.
The restriction that $x$ be bound is simply to make the algorithm easier.
Type instantiation is not attempted.
Neither of these restrictions is relevant in our application to calculating derivatives.
When matching a term of the form $f(x)$, if $f$ corresponds to a $\lambda$-abstraction
in the other term appllied to an argument that corresponds to $x$, then the first order
match is taken; otherwise, the higher-order match is preferred.   
=SML
local
fun aux1 (fv_map : (TERM * TERM) list) 
	(bv_map : (TERM * TERM) list)
	 (ltm : TERM)  (rf : TERM)  (rx : TERM) : (TERM * TERM) list OPT = (
	if	is_var rf
	andalso	is_var rx
	then	let	val (lexp, _) = find fv_map (fn (_, t) => t =$ rf);
			val (lbv1, _) = find fv_map (fn (_, t) => t =$ rx);
		in	case dest_simple_term lexp of 
				Simpleλ(lbv2, body) => (
					if	lbv2 ~=$ lbv1
					andalso	body ~=$ ltm
					then	Value fv_map
					else	Nil
			) | _ => Nil
		end	handle Fail _ =>
		let	val (lbv, _) = find bv_map (fn (_, t) => t =$ rx);
		in
			let	val (lf, lv) = dest_app ltm;
			in	if	lv =$ lbv
				andalso	is_simple_λ lf
				then	Nil (* take first order match *)
				else	Value (tl []) (* fail and fall through *)
			end	handle Fail _ =>
			let	val la = mk_simple_λ(lbv, ltm);
			in	if	snd(dest_→_type(type_of rf)) =: type_of ltm
				then	Value ( (mk_simple_λ(lbv, ltm), rf) :: fv_map )
				else	Nil
			end	handle Fail _ => Nil
		end
	else	Nil
);
fun aux2 (fv_map : (TERM * TERM) list) 
	(bv_map : (TERM * TERM) list)
	(ltm : TERM) (rtm : TERM) : (TERM * TERM) list OPT =
(
	case dest_simple_term rtm of
		Var _ => (
		let	val (lv, rv) = find bv_map (fn (_, t)  => t =$ rtm);
		in	if	ltm =$ lv
			then	Value fv_map
			else	Nil
		end	handle Fail _ => ( (* from find *)
			let	val (lx, _) = find fv_map (fn (_, t)  => t =$ rtm);
			in	if	ltm ~=$ lx
				then	Value fv_map
				else	Nil
			end	handle	Fail _ => (
				if	type_of ltm =: type_of rtm
				then	Value ((ltm, rtm)::fv_map)
				else	Nil
			)
		)
	) |	Const _ =>  (
			if	ltm =$ rtm
			then	Value fv_map
			else	Nil
	) |	Simpleλ(rv, rbody) => (
			case dest_simple_term ltm of
				Simpleλ(lv, lbody) => (
					aux2 fv_map ((lv, rv) :: bv_map) lbody rbody
			) |	_ => Nil
	) |	App(rf, rx) => (
			case aux1 fv_map bv_map ltm rf rx of
				Nil => (
					case dest_simple_term ltm of
						App(lf, lx) => (
					case aux2 fv_map bv_map lf rf of
						Value fvm => aux2 fvm bv_map lx rx
					|	Nil =>  aux1 fv_map bv_map ltm rf rx
					) |	_ => Nil
			) |	res as Value _ => res
	)
);
in
	fun ⦏sho_match⦎  (ltm : TERM) (rtm : TERM) : (TERM * TERM) list = (
		force_value (aux2 [] [] ltm rtm)
	);
end;
=TEX
We need functions for destructing and deconstructing terms of the form
=INLINEFT
(f Deriv x) y
=TEX
:
=SML
val ⦏deriv_tm⦎ = ⌜$Deriv⌝;
fun ⦏dest_deriv⦎ (tm : TERM) : TERM * TERM * TERM = (
	let	val (rator1, arg) = dest_app tm;
		val (rator2, deriv) = dest_app rator1;
		val (deriv, func) = dest_app rator2
	in	if	deriv =$ deriv_tm
		then	(func, deriv, arg)
		else	hd[]
	end
);
fun mk_deriv   ( (f, x, y) : TERM * TERM * TERM) : TERM = (
	mk_app(mk_app(mk_app(deriv_tm, f), x), y)
);
=TEX
We will preprocess theorems to be used in constructing derivatives. The result
of preprocessing a theorem will be a list of pairs, each pair giving a theorem
and the list of free variables of the input theorem from which it was derived.
The preprocessing strips off universal quantifiers, moves the antecedents of
implications into the assumptions and splits up any conjunctions in the resulting
list of assumptions. As a heuristic mainly to deal with the operation that raise
a real number to a natural number power, we also throw in the result of composing
the theorem with the chain rule if the operator in the theorem has its last argument
not a real number.
=SML
fun ⦏asm_∧_elim_rule⦎ (thm : THM) : THM = (
	let	val (p, q) = dest_∧(find (asms thm) is_∧);
	in	asm_∧_elim_rule(prove_asm_rule (∧_intro (asm_rule p) (asm_rule q)) thm)
	end	handle Fail _ => thm
);
fun ⦏all_undisch_rule⦎ (thm : THM)  : THM = (
	all_undisch_rule (undisch_rule thm) handle Fail _ =>  thm
);
val ⦏ℝ_type⦎ = ⓣℝ⌝;
fun ⦏deriv_preprocess⦎ (thms : THM list) :  (THM * TERM list)  list = (
	let	fun heuristic fvs thm1 = (
			let	val (func, _, _) = dest_deriv (concl thm1);
				val last_arg = snd(dest_app(snd(dest_simple_λ func)));
			in	if	not(type_of last_arg =: ℝ_type)
				then
				let	val thm2 = all_∀_elim(∀_elim func comp_deriv_thm);
					val thm3 = conv_rule(ONCE_MAP_C β_conv) thm2;
				in	[(asm_∧_elim_rule(all_undisch_rule thm3), fvs)]
				end
				else	[]
			end	handle Fail _ => []
		);

		fun aux acc (thm::more) = (
			let	val thm1 = asm_∧_elim_rule
					(all_undisch_rule (all_∀_elim thm));
				val fvs = frees(concl thm);
			in	aux (heuristic fvs thm1 @((thm1, fvs) :: acc)) more
			end	handle Fail _ => aux acc more
		) | aux acc[] = rev acc;
	in	aux [] (flat (map strip_∧_rule thms))
	end
);
=TEX
We need some miscellaneous rules to support the main step:
=SML
fun ⦏β_elim_rule⦎ (tm : TERM) : THM = (
	undisch_rule (snd(⇔_elim(ONCE_MAP_C β_conv tm)))
);
fun ⦏freshen⦎ (fixed : TERM list) (tms : TERM list) (thm : THM) : THM = (
	let	val vs = thm_frees thm term_diff fixed;
		val vs' = list_variant tms vs;
		val subs = combine vs' vs;
	in	asm_inst_term_rule subs thm
	end
);
fun ⦏β_reduce_and_match⦎ (tm1 : TERM) (tm2 : TERM) : (TERM * TERM) list = (
	let	val tm1' = snd(dest_eq(concl (TRY_C(MAP_C β_conv) tm1)));
		val tm2' = snd(dest_eq(concl (TRY_C(MAP_C β_conv) tm2)));
		val (_, subs) = term_match tm1' tm2';
	in	subs
	end
);
fun ⦏β_eq_conv⦎ (tm2 : TERM) : CONV = (fn tm1 =>
	(TRY_C (MAP_C β_conv) THEN_C (fn t => eq_sym_rule(TRY_C(MAP_C β_conv) tm2)))
	tm1
);
=TEX
Now the main step: given a term of the form
=INLINEFT
(f Deriv x)y
=TEX
and a preprocessed input theorem, see if
the input theorem can be instantiated to yield a theorem of the form
=INLINEFT
(f Deriv x') y'
=TEX
, where $x'$ is an instance of $x$ and $y$ is an instance of $y'$.
Note the opposite direction of the instantiations here: we are synthesizing information
about $x$ while analysing the syntactic form of $f$, the values of $y$ are forced
upon us during the analysis by the input theorems.

We check to see that the step some progress by
checking that that the theorem we get does not have the form
=INLINEFT
t ⊢ t
=TEX
. This is important to ensure termination in the where
the original $thm$ came from an assumption saying that a function has a derivative
at exactly one point.
=SML
fun ⦏thm_step⦎ (fixed : TERM list) (tm : TERM)
	((thm, fvs) : THM * TERM list) (acc_thm : THM) : THM = (
	let	val (f_tm, deriv_tm, arg_tm) = dest_deriv tm;
		val thm1 = freshen fvs (thm_frees acc_thm) thm;
		val (_, _, arg_tm1) = dest_deriv (concl thm1);
		val (_, subs1) = term_match arg_tm arg_tm1;
		val check_fvs1 =
			if	any subs1 (fn (_, t) => t term_mem fvs)
			then	(hd[]; false)
			else	true;	
		val thm2 = asm_inst_term_rule subs1 thm1;
		val (func2, _, _) = dest_deriv (concl thm2);
		val subs2 = sho_match f_tm func2;
		val check_fvs2 =
			if	any subs2 (fn (_, t) => t term_mem fvs)
			then	(hd[]; false)
			else	true;	
		val thm3 = asm_inst_term_rule subs2 thm2;
		val concl3 = concl thm3;
		val check_progrees = case asms thm3 of
			[] => true
		|	tms => (find tms (fn t => not(t ~=$ concl3)); true);
		val subs4 = β_reduce_and_match concl3 tm;
		val check_fixed =
			if	any subs4 (fn (_, t) => t term_mem fixed)
			then	(hd[]; false)
			else	true;	
		val acc_thm4 = asm_inst_term_rule subs4 acc_thm;
		val tm4 = subst subs4 tm;
		val thm4 = ⇔_mp_rule (β_eq_conv tm4 concl3) thm3;
		val res_thm = prove_asm_rule thm4 acc_thm4;
	in	res_thm
	end
);
=TEX
At the next level up in the algorithm a step takes a pass over all the preprocessed
input theorems and all of the assumptions of the theorem being accumulated
attempting to elimiinate an assumption in favour of assertions about derivatives
of simpler functions:
=SML
fun ⦏simple_deriv_step⦎ (fixed : TERM list)
	(infos : (THM * TERM list) list) (acc_thm : THM) : THM OPT= (
	let	fun thm_steps [] _ = Nil
		|    thm_steps (_::more_asms) [] = thm_steps more_asms infos
		|    thm_steps (asml as (asm::_)) (info::more_infos) = (
			Value(thm_step fixed asm info acc_thm)
			handle Fail _ => thm_steps  asml more_infos
		);
	in	thm_steps (asms acc_thm) infos
	end
);
=TEX
Putting this all together gives the core algorithm which calculates the derivative of a 
term denoting a function at a given argument:
=SML
val var_y = ⌜y:ℝ⌝;
fun ⦏simple_deriv_rule⦎ (thms : THM list) : TERM -> TERM -> THM = (
	let	val infos = deriv_preprocess thms;
		fun go fixed thm = (
			case simple_deriv_step fixed infos thm of
				Value thm' => go fixed thm'
			|	Nil => thm
		);
	in	fn tm => fn arg =>
		let	val fixed = frees arg term_union frees tm;
			val df = variant fixed var_y;
			val gl = mk_deriv(tm, df,  arg);
		in	go fixed (asm_rule gl)
		end
	end
);
=TEX
We now define interface to the core algorithm, which invokes it, and then turns the resulting
theorem into a universally quantified implication with no $\beta$-redexes or $\eta$-redexes
and with hypotheses that are unique by dint of the uniqueness theorem for derivatives
identified. $\eta$-reduction is only done for functions from reals to reals to avoid
rendering terms involving binders unreadable. The conclusion of the theorem
is universally quantified over all variables that do not appear free in the term whose
derivative we are calculating.
Before defining the interface we give
rules to do the various simplifications:

The following rule conjoins all the assumptions of a theorem into one.
=SML
fun ⦏asm_∧_intro_rule⦎ (thm : THM) : THM = (
	case asms thm of
		(asm1::asm2::_) => (
		let	val thm1 = asm_rule (mk_∧(asm1, asm2));
			val thm2 = ∧_left_elim thm1;
			val thm3 = ∧_right_elim thm1;
			val thm4 = prove_asm_rule thm2 thm;
			val thm5 = prove_asm_rule thm3 thm4;
		in	asm_∧_intro_rule thm5
		end
	) | 	_ => thm
);
=TEX
The following rule does the elimination of $\beta$- and $\eta$-redexes:
=SML
val ⦏ℝ_η_axiom⦎ = inst_type_rule[(ⓣℝ⌝, ⓣ'a⌝), (ⓣℝ⌝, ⓣ'b⌝)] η_axiom;
val ⦏β_ℝ_η_elim_conv⦎ = ONCE_MAP_C (β_conv AND_OR_C eq_match_conv ℝ_η_axiom);
fun ⦏asm_β_η_elim_rule⦎ (thm : THM) : THM = (
	let		fun aux1 acc [] = acc
		|   aux1 acc (asm::more) = (
			aux1 (β_ℝ_η_elim_conv asm::acc) more
			handle Fail _ => aux1 acc more
		);
		fun aux2 acc_thm [] = acc_thm
		|   aux2 acc_thm (thm1::more) = (
			let	val thm2 = snd(⇔_elim thm1);
				val thm3 = undisch_rule thm2;
			in	aux2 (prove_asm_rule thm3 acc_thm) more
			end
		);
	in	aux2 thm (aux1 [] (asms thm))
	end
);
=TEX
The following rule looks for assumptions which must  be the same by dint of the
uniqueness of derivatives and identifies them. (Note this does not need the uniqueness
theorem, in predicate logic it would be a weakening of the theorem).
=SML
fun ⦏deriv_dup_elim_rule⦎ (thm : THM) : THM = (
	let	fun aux1 asm1 asm2 thm1 = (
			let	val (f1, x1, y1) = dest_deriv asm1;
				val (f2, x2, y2) = dest_deriv asm2;
			in	if	f1 ~=$ f2
				andalso	y1 ~=$ y2
				then	asm_inst_term_rule [(x1, x2)] thm1
					handle Fail _ =>
					asm_inst_term_rule [(x2, x1)] thm1
				else	hd []
			end
		);
		fun aux2 asm1 [] thm1 = hd []
		|   aux2 asm1 (asm2::more) thm1 = (
			aux1 asm1 asm2 thm1 handle Fail _ => aux2 asm1 more thm1
		);
		fun aux3 [] thm1 = thm1
		|   aux3 (asm::more) thm1 = (
			aux2 asm more thm1 handle Fail _ => aux3 more thm1
		);

	in	aux3 (asms thm) thm
	end
);
=TEX
Now the promised interface to the simple derivative rule (which essentially just composes the
rules above in the right order):
=SML
fun ⦏deriv_rule⦎ (thms : THM list) : TERM -> TERM -> THM = (
	let	val rule = simple_deriv_rule thms;
	in	fn tm => fn arg =>
		let	val thm1 = rule tm arg;
			val thm2 = conv_rule(TRY_C (β_ℝ_η_elim_conv)) thm1;
			val thm3 = deriv_dup_elim_rule(asm_β_η_elim_rule thm2);
			val thm4 = all_⇒_intro (asm_∧_intro_rule thm3);
			val bvs = frees (concl thm4) term_diff (arg::frees tm);
			val thm5 = list_∀_intro bvs thm4;
		in	thm5
		end
	end
);
=TEX
A tactical packaging for the rule:
=SML
fun ⦏DERIV_T⦎ (thms : THM list) (ttac : THM -> TACTIC) : TACTIC = (
	let	val rule = deriv_rule thms;
	in	fn gl as (_, conc) =>
		let	val (f, _, arg) = dest_deriv conc;
			val thm = rule f arg;
		in	ttac thm gl
		end
	end
);
=TEX
A basic set of theorems for use with the rule, sufficient to attack many rational functions:
=SML
val ⦏rat_deriv_thms⦎ = [
	const_deriv_thm,
	id_deriv_thm,
	plus_deriv_thm,
	times_deriv_thm,
	minus_deriv_thm,
	recip_deriv_thm,
	ℝ_ℕ_exp_deriv_thm,
	rewrite_rule[](∀_elim⌜0⌝ ℝ_ℕ_exp_deriv_thm),
	rewrite_rule[](∀_elim⌜1⌝ ℝ_ℕ_exp_deriv_thm),
	rewrite_rule[](∀_elim⌜2⌝ ℝ_ℕ_exp_deriv_thm),
	rewrite_rule[](∀_elim⌜3⌝ ℝ_ℕ_exp_deriv_thm),
	comp_deriv_thm
];
val ⦏rat_deriv_rule⦎ = deriv_rule rat_deriv_thms;
val ⦏RAT_DERIV_T⦎ = DERIV_T rat_deriv_thms;
=IGN


val tms = [
	 ⌜  (λx:ℝ⦁ x)  ⌝,
	 ⌜  (λx:ℝ⦁ y:ℝ)  ⌝,
	 ⌜  (λx:ℝ⦁ ~(f (y)):ℝ)  ⌝,
	 ⌜  (λx:ℝ⦁ a + x * y)  ⌝,
	 ⌜  (λx:ℝ⦁ x * y)  ⌝,
	 ⌜  (λx:ℝ⦁ x + x*x*y)  ⌝,
	 ⌜  (λx:ℝ⦁ a ^ (n+1) + x^(n+1)+ x * y)  ⌝,
	 ⌜  (λx:ℝ⦁ x ^ 2 )  ⌝,
	 ⌜  (λx:ℝ⦁ (f(x):ℝ)^2)  ⌝,
	 ⌜  (λx:ℝ⦁ f x + ℕℝ 3) ⌝,
	 ⌜  (λx:ℝ⦁ ~(g x):ℝ) ⌝,
	 ⌜  (λx:ℝ⦁ ~(g x) * f x + ℕℝ 3 * x) ⌝,
	 ⌜ ~ : ℝ → ℝ ⌝,
	 ⌜  (  λx:ℝ⦁ Exp(Log x)  ) ⌝,
	 ⌜  (  λx:ℝ⦁ Log(Exp x)  ) ⌝,
	 ⌜  (  λx:ℝ⦁Sin(x) ^ 2 + Cos(x) ^ 2  ) ⌝,
	 ⌜  (  λx:ℝ⦁Sin(x) * Cos(x)  ) ⌝,
	 ⌜  (  λx:ℝ⦁ (Sin x + ~ (Cos x)) ^ 2 ) ⌝,
	 ⌜  (  λx:ℝ⦁ Log(Cos x)  ) ⌝,
	 ⌜  (λx:ℝ⦁ (x + ℕℝ 1) * (x + ~(ℕℝ 1)) ⋏-⋏1 )  ⌝,
	 ⌜  (λx:ℝ⦁ ℕℝ 1 ⋏-⋏1 + ℕℝ 2 ⋏-⋏1 * x^2 + ℕℝ 6 ⋏-⋏1 * x^3  ) ⌝
];

map (conv_rule (TRY_C(ONCE_MAP_C ℝ_anf_conv))) (map (switch rat_deriv_rule ⌜X:ℝ⌝) tms);
rat_deriv_rule ⌜ λx:ℝ⦁ f x + f x : ℝ⌝ ⌜Y:ℝ⌝;
simple_deriv_rule rat_deriv_thms ⌜ λx:ℝ⦁ f x + f x : ℝ⌝ ⌜Y:ℝ⌝;

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Some Classical Theorems}
%%%%
%%%%
%%%%
%%%%
First of all we prove the following rather unusual result which works out
nicely in some cases where we would otherwise have to work directly with
suprema. For the want of a better name, we call it the ``curtain
induction principle'' (think of sliding a curtain along the real line starting
from $-\infty$).
%%%%
%%%%
=SML

val ⦏curtain_induction_thm⦎ = save_thm ( "curtain_induction_thm", (
set_goal([], ⌜∀p:ℝ→BOOL⦁
	(∃x⦁p x)
∧	(∀x⦁p x ⇒ ∀y⦁y < x ⇒ p y)
∧	(∀x⦁∃y z⦁ y < x ∧ x < z ∧ (p y ⇒ p z))
⇒	(∀x⦁p x) 
⌝);
a(contr_tac);
a(lemma_tac⌜∃P⦁P = {t | p t}⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜¬P = {} ∧ ∃c⦁∀x⦁x ∈ P ⇒ x ≤ c⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜x'⌝ THEN all_var_elim_asm_tac1 THEN contr_tac);
a(lemma_tac⌜x' < x''⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(all_fc_tac[ℝ_sup_thm] THEN fc_tac[ℝ_sup_thm]);
a(LIST_DROP_NTH_ASM_T [1,2] fc_tac);
a(spec_nth_asm_tac 8 ⌜Sup P⌝);
(* *** Goal "3.1" *** *)
a(swap_nth_asm_concl_tac 3 THEN rewrite_tac[ℝ_¬_less_≤_thm]);
a(bc_thm_tac ℝ_sup_≤_bc_thm THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN1 (∃_tac⌜c⌝ THEN asm_rewrite_tac[]));
a(contr_tac THEN lemma_tac⌜y < y'⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "3.2" *** *)
a(lemma_tac ⌜∃w⦁Sup P < w ∧ w < z⌝ THEN1
	(bc_thm_tac ℝ_less_dense_thm THEN REPEAT strip_tac));
a(lemma_tac⌜w ≤ z⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜w ∈ P⌝ THEN1 (asm_rewrite_tac[] THEN all_asm_fc_tac[]));
a(lemma_tac⌜w ≤ Sup P⌝ THEN1 all_asm_fc_tac[]);
a(PC_T1"ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
val ⦏curtain_induction_tac⦎ = gen_induction_tac curtain_induction_thm;
=IGN
set_goal([], ⌜∀x:ℝ⦁∃y⦁x ≤ y⌝);
a(strip_tac);
a(curtain_induction_tac⌜x⌝);
(* *** Goal "1" *** *)
a(∃_tac ⌜x⌝ THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN ∃_tac⌜y⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜x + ~(1/2)⌝ THEN ∃_tac⌜x + (1/2)⌝ THEN REPEAT strip_tac);
a(∃_tac⌜y'+3/2⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val test10 = pop_thm();
=TEX
Bolzano's principle of bisection, via a lemma which contains most
of the argument:
%%%%
%%%%
=SML
set_goal([], ⌜∀p⦁
	(∀x y⦁y < x ⇒ p x y)
∧	(∀x y z⦁ x ≤ y ∧ y ≤ z ∧ p x y ∧ p y z ⇒ p x z)
∧	(∀y⦁∃d⦁ ℕℝ 0 < d ∧ (∀x z⦁  x ≤ y ∧ y ≤ z ∧ z - x < d ⇒ p x z))
⇒	(∀x y⦁p x y)
⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜∀t⦁t ≤ y ⇒ p x t⌝ (strip_asm_tac o ∀_elim⌜y⌝));
a(lemma_tac⌜∀c⦁p c c⌝ THEN1
	(REPEAT strip_tac THEN
	POP_ASM_T (strip_asm_tac o ∀_elim⌜c:ℝ⌝) THEN
	POP_ASM_T bc_thm_tac THEN asm_rewrite_tac[]));
a(curtain_induction_tac⌜y:ℝ⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜x + ~(ℕℝ 1)⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜t < x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(GET_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(cases_tac⌜y' < x⌝);
(* *** Goal "3.1" *** *)
a(∃_tac⌜y' + ~(ℕℝ 1)⌝ THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(cases_tac⌜t < x⌝ THEN1 all_asm_fc_tac[]);
a(lemma_tac⌜t = x⌝ THEN_LIST[PC_T1"ℝ_lin_arith"asm_prove_tac[], all_var_elim_asm_tac1]);
a(asm_rewrite_tac[]);
(* *** Goal "3.2" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_less_≤_thm]));
a(cases_tac⌜¬∀b⦁b < y' ⇒ p x b⌝);
(* *** Goal "3.2.1" *** *)
a(∃_tac⌜b⌝ THEN ∃_tac⌜y' + ℕℝ 1⌝ THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜b⌝);
(* *** Goal "3.2.2" *** *)
a(spec_nth_asm_tac 4 ⌜y'⌝);
a(∃_tac⌜y' + ~(1/3*d)⌝ THEN ∃_tac⌜y' + 1/3*d⌝ THEN REPEAT strip_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜t < y'⌝ THEN1 all_asm_fc_tac[]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_less_≤_thm]));
a(lemma_tac⌜∃a⦁x ≤ a ∧ a ≤ y' ∧ y' - a ≤ 1/3*d ∧ p x a⌝);
(* *** Goal "3.2.2.1" *** *)
a(cases_tac⌜x ≤ y' + ~(1/3*d)⌝);
(* *** Goal "3.2.2.1.1" *** *)
a(∃_tac⌜y' + ~(1/3*d)⌝ THEN REPEAT strip_tac THEN_TRY
	PC_T1"ℝ_lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 7 ⌜y' + ~(1/3*d)⌝);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.2.2.1.2" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[]);
(* *** Goal "3.2.2.2" *** *)
a(GET_NTH_ASM_T 14 bc_thm_tac);
a(∃_tac⌜a⌝ THEN REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(GET_NTH_ASM_T 8 bc_thm_tac THEN REPEAT strip_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏bisection_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏bisection_thm⦎ = save_thm ( "bisection_thm", (
set_goal([], ⌜∀p a b⦁
	(∀x y z⦁ x ≤ y ∧ y ≤ z ∧ p x y ∧ p y z ⇒ p x z)
∧	(∀y⦁∃d⦁ ℕℝ 0 < d ∧ (∀x z⦁  x ≤ y ∧ y ≤ z ∧ z - x < d ⇒ p x z))
∧	a ≤ b
⇒	p a b
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀a b⦁(λ x y⦁if x ≤ y then p x y else T)a b⌝ THEN1
	(bc_thm_tac bisection_lemma THEN rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" (= 3, 4, and 5) *** *)
a(all_asm_fc_tac[]);
(* *** Goal "6" *** *)
a(spec_nth_asm_tac 2 ⌜y⌝);
a(∃_tac⌜d⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[]));
a(all_asm_fc_tac[]);
(* *** Goal "7" *** *)
a(POP_ASM_T (ante_tac o list_∀_elim[⌜a⌝, ⌜b⌝]) THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
One half of the Heine-Borel theorem says that every closed interval is compact;
i.e., every covering of the closed interval by a family
of open sets has a finite subcovering.
Nearly all the analysis is in the following lemma, which deals with
the case where the covering actually covers the whole real line:
%%%%
%%%%
=SML
set_goal([], ⌜∀V x y⦁
	V ⊆ Open⋎R
∧	(∀z⦁ z ∈ ⋃V)
⇒	∃W⦁ W ⊆ V ∧ W ∈ Finite ∧ ClosedInterval x y ⊆ ⋃ W⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(curtain_induction_tac⌜y:ℝ⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜x + ~(ℕℝ 1)⌝ THEN REPEAT strip_tac);
a(∃_tac⌜{}⌝ THEN PC_T1 "sets_ext1" rewrite_tac[empty_finite_thm, closed_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext1" (spec_nth_asm_tac 1) ⌜z⌝ THEN all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜ClosedInterval x y ⊆ ClosedInterval x y'⌝ THEN1
	(rewrite_tac[closed_interval_def] THEN
	PC_T1 "sets_ext1" REPEAT strip_tac THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[
	pc_rule1 "sets_ext1" prove_rule[]⌜∀A B C⦁A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
a(∃_tac⌜W⌝ THEN REPEAT strip_tac);
(* *** Goal "4" *** *)
a(PC_T1 "'propositions" cases_tac⌜¬(∀ z⦁ z ∈ ⋃ V)⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4.1" *** *)
a(∃_tac⌜y' + ~(ℕℝ 1)⌝ THEN ∃_tac⌜y' + ℕℝ 1⌝ THEN REPEAT strip_tac);
(* *** Goal "4.2" *** *)
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜y'⌝ o pc_rule1 "sets_ext1" rewrite_rule[]));
a(DROP_NTH_ASM_T 3 ante_tac THEN
	rewrite_tac[open_ℝ_def, open_interval_def] THEN
	PC_T1 "sets_ext" REPEAT strip_tac);
a(all_asm_fc_tac[] THEN all_fc_tac[ℝ_less_dense_thm]);
a(∃_tac⌜z'⌝ THEN ∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(∃_tac⌜{s} ∪ W⌝ THEN ALL_FC_T rewrite_tac[singleton_∪_finite_thm]);
a(rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
(* *** Goal "4.2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac THEN1 all_var_elim_asm_tac1);
a(PC_T1 "sets_ext1" all_asm_fc_tac[]);
(* *** Goal "4.2.2" *** *)
a(GET_NTH_ASM_T 8 ante_tac THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (strip_asm_tac o pc_rule1 "sets_ext1" rewrite_rule[closed_interval_def]));
a(cases_tac⌜x' < x''⌝);
(* *** Goal "4.2.2.1" *** *)
a(∃_tac ⌜s⌝ THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 5 bc_thm_tac THEN
	REPEAT strip_tac THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4.2.2.2" *** *)
a(lemma_tac⌜x'' ≤ z'⌝  THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_GET_NTH_ASM_T [3] all_fc_tac);
a(∃_tac ⌜s'⌝ THEN REPEAT strip_tac);
val ⦏heine_borel_lemma⦎ = pop_thm();
=TEX
The theorem follows from the lemma by a simple
argument showing that, w.l.o.g., we may assume that the open covering
of the closed interval is actually an open covering of the whole real line
(because one can throw in the complement of the interval first and then
afterwards discard it from the finite subcovering).
%%%%
%%%%
=SML

val ⦏closed_interval_compact_thm⦎ = save_thm ( "closed_interval_compact_thm", (
set_goal([], ⌜∀x y⦁ ClosedInterval x y ∈ Compact⋎R⌝);
a(rewrite_tac[compact_ℝ_def] THEN REPEAT strip_tac);
a(lemma_tac⌜{~(ClosedInterval x y)} ∪ V ⊆ Open⋎R
	∧ (∀z⦁ z ∈ ⋃({~(ClosedInterval x y)} ∪ V))⌝ THEN
	REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac(pc_rule1 "sets_ext1" prove_rule[]
	⌜∀x A B⦁ x ∈ B ∧ A ⊆ B ⇒ {x} ∪ A ⊆ B⌝) THEN REPEAT strip_tac);
a(rewrite_tac[rewrite_rule[closed_ℝ_def] closed_interval_closed_thm]);
(* *** Goal "2" *** *)
a(cases_tac⌜¬z ∈ ClosedInterval x y⌝ THEN1
	(∃_tac⌜~(ClosedInterval x y)⌝ THEN PC_T1 "sets_ext1" asm_rewrite_tac[]
	THEN asm_rewrite_tac[]));
a(all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀A B⦁z ∈ A ∧ A ⊆ B ⇒ z ∈ B⌝]);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(EXTEND_PC_T1 "'mmp1" all_fc_tac[heine_borel_lemma]);
a(∃_tac⌜W \ {~(ClosedInterval x y)}⌝ THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN
	all_fc_tac[pc_rule1"sets_ext1" prove_rule[]⌜∀A B⦁x' ∈ A ∧ A ⊆ B ⇒ x' ∈ B⌝] THEN
	all_var_elim_asm_tac1);
(* *** Goal "3.2" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜W⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "3.3" *** *)
a(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(∃_tac⌜s⌝ THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac⌜x'⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The following lemma is useful in connection with certain compactness arguments:
=SML

val ⦏finite_chain_thm⦎ = save_thm ( "finite_chain_thm", (
set_goal([], ⌜∀V⦁
	V ∈ Finite
∧	¬V = {}
∧	(∀A B⦁ A ∈ V ∧ B ∈ V ⇒ A ⊆ B ∨ B ⊆ A)
⇒	∃A⦁ A ∈ V ∧ ⋃V = A	
⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac THEN POP_ASM_T ante_tac);
a(finite_induction_tac ⌜V⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_var_elim_asm_tac1 THEN ∃_tac⌜x⌝ THEN PC_T1 "sets_ext1" prove_tac[]);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(i_contr_tac THEN lemma_tac⌜A ⊆ B ∨ B ⊆ A⌝ THEN1 POP_ASM_T bc_thm_tac);
a(REPEAT strip_tac);
(* *** Goal "3" *** *)
a(lemma_tac⌜A ⊆ x ∨ x ⊆ A⌝ THEN1 POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜⋃{x} = x⌝ THEN1
	(PC_T1 "sets_ext1" prove_tac[] THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac));
a(asm_rewrite_tac[pc_rule1"sets_ext1"prove_rule[]⌜∀X Y⦁⋃ (X ∪ Y) = ⋃X ∪ ⋃Y⌝]);
a(GET_NTH_ASM_T 2 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "3.2" *** *)
a(∃_tac⌜A⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜⋃{x} = x⌝ THEN1
	(PC_T1 "sets_ext1" prove_tac[] THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac));
a(asm_rewrite_tac[pc_rule1"sets_ext1"prove_rule[]⌜∀X Y⦁⋃ (X ∪ Y) = ⋃X ∪ ⋃Y⌝]);
a(GET_NTH_ASM_T 2 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
The next classical result is that a function continuous on a closed
attains is bounded and, indeed, attains its upper bound.
We do the special case where the function is continuous everywhere
as a lemma first. However, we do the special case in the more general
context of a function on an arbitrary compact set.
%%%%
%%%%
=SML

val ⦏cts_compact_maximum_thm⦎ = save_thm ( "cts_compact_maximum_thm", (
set_goal([], ⌜∀X f⦁
	¬X = {}
∧	X ∈ Compact⋎R
∧	(∀x⦁ f Cts x)
⇒	∃x⦁ x ∈ X ∧ ∀z⦁z ∈ X ⇒ f z ≤ f x⌝);
a(contr_tac);
a(lemma_tac⌜{A | ∃x⦁ x ∈ X ∧ A = {z | f z < f x}} ⊆ Open⋎R⌝);
(* *** Goal "1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(lemma_tac⌜{y | y < f x'} ∈ Open⋎R⌝);
(* *** Goal "1.1" *** *)
a(rewrite_tac[open_ℝ_def, open_interval_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(all_fc_tac[ℝ_less_dense_thm]);
a(∃_tac⌜t + ~(ℕℝ 1)⌝ THEN ∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(all_var_elim_asm_tac1 THEN fc_tac[cts_open_ℝ_thm]);
a(LEMMA_T ⌜{z | f z < f x'} = {z | f z ∈ {y | y < f x'}}⌝ pure_rewrite_thm_tac THEN1
	rewrite_tac[]);
a(POP_ASM_T bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜X ⊆ ⋃{A | ∃x⦁ x ∈ X ∧ A = {z | f z < f x}}⌝);
(* *** Goal "2.1" *** *)
a(PC_T "sets_ext1" strip_tac THEN REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜x⌝);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(∃_tac⌜{a | f a < f z}⌝ THEN asm_rewrite_tac[]);
a(∃_tac⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 5 (fn th => all_fc_tac[rewrite_rule[compact_ℝ_def]th]));
a(lemma_tac⌜∀A B⦁ A ∈ W ∧ B ∈ W ⇒ A ⊆ B ∨ B ⊆ A⌝);
(* *** Goal "2.2.1" *** *)
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(lemma_tac⌜A ∈ {A | ∃x⦁ x ∈ X ∧ A = {z | f z < f x}} ∧
	B ∈ {A | ∃x⦁ x ∈ X ∧ A = {z | f z < f x}}⌝ THEN1
	(ALL_FC_T rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
		⌜∀ x y X Y⦁ x ∈ X ∧ X ⊆ Y ⇒ x ∈ Y⌝]));
a(all_var_elim_asm_tac1);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜¬W = {}⌝);
(* *** Goal "2.2.2.1" *** *)
a(swap_nth_asm_concl_tac 2 THEN all_var_elim_asm_tac1);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(DROP_NTH_ASM_T 7 (PC_T1 "sets_ext" strip_asm_tac));
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(all_fc_tac[finite_chain_thm]);
a(all_fc_tac[pc_rule1 "sets_ext1" prove_rule[]
		⌜∀ x y X Y⦁ x ∈ X ∧ X ⊆ Y ⇒ x ∈ Y⌝]);
a(swap_nth_asm_concl_tac 7 THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f a b⦁
	a ≤ b
∧	(∀x⦁ f Cts x)
⇒	∃x⦁ a ≤ x ∧ x ≤ b ∧ ∀z⦁a ≤ z ∧ z ≤ b ⇒ f z ≤ f x⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜¬ClosedInterval a b = {} ∧ ClosedInterval a b ∈ Compact⋎R⌝ THEN1
	(rewrite_tac[closed_interval_compact_thm] THEN
	rewrite_tac[closed_interval_def] THEN
	PC_T1 "sets_ext1" REPEAT strip_tac THEN
	∃_tac⌜a⌝ THEN REPEAT strip_tac));
a(all_fc_tac[cts_compact_maximum_thm]);
a(∃_tac ⌜x⌝ THEN POP_ASM_T ante_tac THEN POP_ASM_T ante_tac);
a(rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
val ⦏cts_bounded_lemma⦎ = pop_thm();
=TEX
Now the general result on the boundedness of a function continuous on
some closed interval:
%%%%
%%%%
=SML

val ⦏cts_maximum_thm⦎ = save_thm ( "cts_maximum_thm", (
set_goal([], ⌜∀f a b⦁
	a ≤ b
∧	(∀x⦁ a ≤ x ∧ x ≤ b ⇒ f Cts x)
⇒	∃x⦁ a ≤ x ∧ x ≤ b ∧ ∀z⦁ a ≤ z ∧ z ≤ b ⇒ f z ≤ f x⌝);
a(REPEAT strip_tac);
a(cases_tac⌜a = b⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(∃_tac⌜b⌝ THEN REPEAT strip_tac THEN
	LEMMA_T ⌜z = b⌝ rewrite_thm_tac THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac ⌜a < b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[conv_rule (ONCE_MAP_C eq_sym_conv) cts_extension_thm]);
a(all_fc_tac[cts_bounded_lemma]);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f a b⦁
	a ≤ b
∧	(∀x⦁ a ≤ x ∧ x ≤ b ⇒ f Cts x)
⇒	∃x⦁ a ≤ x ∧ x ≤ b ∧ ∀z⦁ a ≤ z ∧ z ≤ b ⇒ Abs(f z) ≤ Abs(f x)⌝);
a(REPEAT strip_tac);
a(bc_thm_tac (rewrite_rule[](∀_elim⌜λz⦁Abs(f z)⌝ cts_maximum_thm)));
a(REPEAT strip_tac THEN bc_thm_tac comp_cts_thm);
a(rewrite_tac[abs_cts_thm] THEN all_asm_fc_tac[]);
val ⦏cts_abs_bounded_lemma⦎ =pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏cts_abs_bounded_thm⦎ = save_thm ( "cts_abs_bounded_thm", (
set_goal([], ⌜∀f a b⦁
	a ≤ b
∧	(∀x⦁ a ≤ x ∧ x ≤ b ⇒ f Cts x)
⇒	∃c⦁ ∀z⦁ a ≤ z ∧ z ≤ b ⇒ Abs(f z) ≤ c⌝);
a(REPEAT strip_tac THEN all_fc_tac[cts_abs_bounded_lemma]);
a(∃_tac⌜Abs(f x)⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The next classical result will be the intermediate value theorem.
As so often, a lemma containing the main part of the argument comes first.
We follow many authors in doing the case where the intermediate value is $0$
first to simplify the absolute value reasoning and we restrict to the case
where the function is negative towards the left of the interval and positive
towards the right. The proof is by bisection.
%%%%
%%%%
=SML
set_goal([], ⌜∀f a b⦁
	(∀x⦁ f Cts x) ∧ a ≤ b
⇒	f a < ℕℝ 0 ∧ ℕℝ 0 < f b ⇒ ∃x⦁a ≤ x ∧ x ≤ b ∧ f x = ℕℝ 0⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(bc_thm_tac (rewrite_rule[]
	(∀_elim⌜λa b⦁f a < ℕℝ 0 ∧ ℕℝ 0 < f b ⇒ ∃x⦁a ≤ x ∧ x ≤ b ∧ f x = ℕℝ 0⌝
	bisection_thm)));
a(REPEAT strip_tac THEN_TRY SOLVED_T
	(contr_tac THEN all_asm_fc_tac[ℝ_≤_trans_thm] THEN all_asm_fc_tac[]));
(* *** Goal "1" *** *)
a(lemma_tac⌜f y = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜f y = ℕℝ 0⌝ THEN1
	(∃_tac⌜ℕℝ 1⌝ THEN contr_tac THEN all_asm_fc_tac[]));
a(DROP_NTH_ASM_T 3 (strip_asm_tac o rewrite_rule[cts_def] o ∀_elim⌜y⌝));
a(lemma_tac ⌜ℕℝ 0 < (1/3)*Abs (f y)⌝ THEN1
	(lemma_tac ⌜¬Abs (f y) = ℕℝ 0⌝ THEN1
	asm_rewrite_tac[ℝ_abs_eq_0_thm] THEN
	strip_asm_tac(∀_elim⌜f y⌝ℝ_0_≤_abs_thm) THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_asm_fc_tac[]);
a(∃_tac⌜d⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 ≤ ~(x + ~y) ∧ ℕℝ 0 ≤ z + ~y⌝ THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜Abs(~(x + ~y)) < d ∧ Abs(z + ~y) < d⌝ ante_tac THEN1
	(asm_rewrite_tac[ℝ_abs_def] THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(rewrite_tac[ℝ_abs_minus_thm] THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [10] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [1, 2, 7, 8, 14] (MAP_EVERY ante_tac) THEN
	DROP_ASMS_T discard_tac THEN
	MAP_EVERY cases_tac
		[⌜ℕℝ 0 ≤ f z + ~(f y)⌝, ⌜ℕℝ 0 ≤ f x + ~(f y)⌝, ⌜ℕℝ 0 ≤ f y⌝] THEN
	asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏intermediate_value_lemma⦎ = pop_thm();
=TEX
With the lemma, we can prove the intermediate value theorem proper.
There is a small amount of doubt about what the exact statement should be.
We interpret the weasel word ``between'' which occurs in so many textbook
accounts as meaning ``strictly between''. (The more general formulation with
non-strict inequalities is only vacuously more general --- it just gives
one the trivial cases where the interval consists of a point or where the
intermediate value is achieved at one of the end-points; and, of course,
the statement is vacuously true if the interval is empty).
%%%%
%%%%
=SML

val ⦏intermediate_value_thm⦎ = save_thm ( "intermediate_value_thm", (
set_goal([], ⌜∀f a b⦁
	a < b
∧	(∀x⦁a ≤ x ∧ x ≤ b ⇒ f Cts x)
⇒	(∀y⦁(f a < y ∧ y < f b ∨ f b < y ∧ y < f a) ⇒ ∃x⦁ a < x ∧ x < b ∧ f x = y)⌝);
a(lemma_tac⌜∀f a b⦁
	a < b
∧	(∀x⦁a ≤ x ∧ x ≤ b ⇒ f Cts x)
⇒	(∀y⦁(f a < y ∧ y < f b) ⇒ ∃x⦁ a < x ∧ x < b ∧ f x = y)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀x⦁a ≤ x ∧ x ≤ b ⇒ (λz⦁f z + ~y) Cts x⌝ THEN1
	(REPEAT (simple_cts_tac ORELSE strip_tac) THEN ALL_ASM_FC_T rewrite_tac[]));
a(DROP_NTH_ASM_T 4 discard_tac);
a(all_fc_tac[conv_rule (ONCE_MAP_C eq_sym_conv) cts_extension_thm]);
a(LEMMA_T⌜(λz⦁f z + ~y) a < ℕℝ 0 ∧ ℕℝ 0 < (λz⦁f z + ~y) b⌝ ante_tac THEN1
	(rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac ⌜a ≤ b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 3 ⌜a⌝ THEN POP_ASM_T pure_rewrite_thm_tac);
a(spec_nth_asm_tac 3 ⌜b⌝ THEN POP_ASM_T rewrite_thm_tac THEN REPEAT strip_tac);
a(all_fc_tac[intermediate_value_lemma]);
a(lemma_tac⌜¬x = a ∧ ¬x = b⌝ THEN1
	(contr_tac THEN all_var_elim_asm_tac1 THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜a < x ∧ x < b⌝ THEN1
	(PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac ⌜x⌝ THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [12] (ALL_FC_T (MAP_EVERY ante_tac)));
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN1 (contr_tac THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]));
a(lemma_tac⌜∀ x⦁ a ≤ x ∧ x ≤ b ⇒ (λx⦁ ~(f x)) Cts x⌝ THEN1
	(REPEAT (simple_cts_tac ORELSE strip_tac) THEN ALL_ASM_FC_T rewrite_tac[]));
a(lemma_tac⌜ (λx⦁ ~(f x)) a < ~y ∧ ~y < (λx⦁ ~(f x)) b⌝ THEN1
	(rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_asm_fc_tac[]);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
To prove the mean value theorem, we will need the principle that a function which is
differentiable at a local minimum or maximum has a zero derivative there.
Most of the work of this goes into the following special case.
%%%%
%%%%
=SML
set_goal([], ⌜∀f a b c⦁
	a < ℕℝ 0 ∧ ℕℝ 0 < b
∧	(∀y⦁a < y ∧ y < b ⇒ ℕℝ 0 ≤ f y)
∧	f(ℕℝ 0) = ℕℝ 0
∧	(f Deriv c)  (ℕℝ 0)
⇒	c = ℕℝ 0⌝);
a(rewrite_tac[caratheodory_deriv_thm] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 ante_tac THEN all_var_elim_asm_tac1 THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN bc_thm_tac cts_estimate_0_thm THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(cases_tac⌜(1/2)*b < (1/2)*d⌝);
(* *** Goal "1.1" *** *)
a(∃_tac⌜(1/2)*b⌝ THEN rewrite_tac[]);
a(LEMMA_T ⌜ℕℝ 0 ≤ (1/2)*b⌝ (fn th => rewrite_tac[th, ℝ_abs_def]) 
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ℕℝ 0 ≤ f((1/2)*b)⌝ ante_tac THEN1
	((lemma_tac ⌜a < (1/2)*b ∧ (1/2)*b < b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[])
	THEN all_asm_fc_tac[]));
a(asm_rewrite_tac[]);
a(lemma_tac ⌜ℕℝ 0 < (1/2)*b⌝  THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(contr_tac THEN POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(ALL_FC_T (MAP_EVERY ante_tac)[∀_elim⌜(1/2)*b⌝ℝ_times_mono_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(∃_tac⌜(1/2)*d⌝ THEN rewrite_tac[]);
a(LEMMA_T ⌜ℕℝ 0 ≤ (1/2)*d⌝ (fn th => rewrite_tac[th, ℝ_abs_def]) 
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ℕℝ 0 ≤ f((1/2)*d)⌝ ante_tac THEN1
	((lemma_tac ⌜a < (1/2)*d ∧ (1/2)*d < b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[])
	THEN all_asm_fc_tac[]));
a(asm_rewrite_tac[]);
a(lemma_tac ⌜ℕℝ 0 < (1/2)*d⌝  THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(contr_tac THEN POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(ALL_FC_T (MAP_EVERY ante_tac)[∀_elim⌜(1/2)*d⌝ℝ_times_mono_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜~((1/2)*d) < (1/2)*a⌝);
(* *** Goal "2.1" *** *)
a(∃_tac⌜(1/2)*a⌝ THEN rewrite_tac[]);
a(LEMMA_T ⌜¬ ℕℝ 0 ≤ (1/2)*a⌝ (fn th => rewrite_tac[th, ℝ_abs_def]) 
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ℕℝ 0 ≤ f((1/2)*a)⌝ ante_tac THEN1
	((lemma_tac ⌜a < (1/2)*a ∧ (1/2)*a < b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[])
	THEN all_asm_fc_tac[]));
a(asm_rewrite_tac[]);
a(lemma_tac ⌜ℕℝ 0 < ~((1/2)*a)⌝  THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(contr_tac THEN POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(ALL_FC_T (MAP_EVERY ante_tac)[∀_elim⌜~((1/2)*a)⌝ℝ_times_mono_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜~((1/2)*d)⌝ THEN rewrite_tac[]);
a(LEMMA_T ⌜¬ ℕℝ 0 ≤ ~((1/2)*d)⌝ (fn th => rewrite_tac[th, ℝ_abs_def]) 
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ℕℝ 0 ≤ f(~((1/2)*d))⌝ ante_tac THEN1
	((lemma_tac ⌜a < ~((1/2)*d) ∧ ~((1/2)*d) < b⌝
		THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[])
	THEN all_asm_fc_tac[]));
a(asm_rewrite_tac[]);
a(lemma_tac ⌜ℕℝ 0 < (1/2)*d⌝  THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(contr_tac THEN POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(ALL_FC_T (MAP_EVERY ante_tac)[∀_elim⌜((1/2)*d)⌝ℝ_times_mono_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏local_min_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏local_min_thm⦎ = save_thm ( "local_min_thm", (
set_goal([], ⌜∀f x a b c⦁
	a < x ∧ x < b
∧	(∀y⦁a < y ∧ y < b ⇒ f x ≤ f y)
∧	(f Deriv c)  x
⇒	c = ℕℝ 0⌝);
a(REPEAT  strip_tac);
a(ante_tac (list_∀_elim[⌜λz⦁f (z + x) + ~(f x)⌝, ⌜a + ~x⌝, ⌜b + ~x⌝, ⌜c⌝]local_min_lemma));
a(STRIP_T bc_thm_tac THEN rewrite_tac[]);
a(strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 4 (ante_tac o once_rewrite_rule[ℝ_≤_0_≤_thm]));
a(STRIP_T bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜c = c * ℕℝ 1⌝]);
a(RAT_DERIV_T  (bc_thm_tac o rewrite_rule[]));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏local_max_thm⦎ = save_thm ( "local_max_thm", (
set_goal([], ⌜∀f x a b c⦁
	a < x ∧ x < b
∧	(∀y⦁a < y ∧ y < b ⇒ f y ≤ f x)
∧	(f Deriv c)  x
⇒	c = ℕℝ 0⌝);
a(REPEAT  strip_tac);
a(ante_tac (list_∀_elim[⌜λz⦁~(f z)⌝, ⌜x⌝, ⌜a⌝, ⌜b⌝, ⌜~c⌝]local_min_thm));
a(asm_rewrite_tac[
	pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁(~a ≤ ~b ⇔ b ≤ a) ∧ (~a = b ⇔ a = ~b)⌝]);
a(STRIP_T bc_thm_tac);
a(RAT_DERIV_T (bc_thm_tac o  conv_rule(ONCE_MAP_C ℝ_anf_conv))
	THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f df a b⦁
	a <  b
∧	(∀x⦁a ≤  x ∧ x ≤ b ⇒ f Cts x)
∧	(∀x⦁a <  x ∧ x < b ⇒ (f Deriv df x) x)
∧	f a = f b
∧	(∃x⦁a ≤ x ∧ x ≤ b ∧ f b < f x)
⇒	(∃x⦁a < x ∧ x < b ∧ (f Deriv (ℕℝ 0)) x)⌝);
a(REPEAT  strip_tac);
a(lemma_tac⌜a ≤ b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[cts_maximum_thm]);
a(TOP_ASM_T (ante_tac o ∀_elim⌜x⌝) THEN LIST_GET_NTH_ASM_T [6, 7] rewrite_tac);
a(once_rewrite_tac[prove_rule[]⌜∀p q r⦁p ∧ q ∧ r ⇔ p ∧ q ∧ (p ∧ q ⇒ r)⌝]);
a(strip_tac THEN ∃_tac⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal 1" *** *)
a((cases_tac⌜a = x'⌝ THEN1 all_var_elim_asm_tac1) THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal 2" *** *)
a((cases_tac⌜b = x'⌝ THEN1 all_var_elim_asm_tac1) THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal 3" *** *)
a(spec_nth_asm_tac 12 ⌜x'⌝);
a(lemma_tac ⌜df x' = ℕℝ 0⌝ THEN_LIST [bc_thm_tac local_max_thm,
	POP_ASM_T (rewrite_thm_tac o eq_sym_rule) THEN strip_tac]);
a(MAP_EVERY ∃_tac[⌜f⌝, ⌜b⌝, ⌜x'⌝, ⌜a⌝] THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 5 ante_tac THEN DROP_ASMS_T discard_tac);
a(rewrite_tac[ℝ_≤_def] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
val ⦏rolle_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏rolle_thm⦎ = save_thm ( "rolle_thm", (
set_goal([], ⌜∀f df a b⦁
	a <  b
∧	(∀x⦁a ≤ x ∧ x ≤ b ⇒ f Cts x)
∧	(∀x⦁a < x ∧ x < b ⇒ (f Deriv df x) x)
∧	f a = f b
⇒	(∃x⦁a < x ∧ x < b ∧ (f Deriv (ℕℝ 0)) x)⌝);
a(REPEAT  strip_tac);
a(cases_tac⌜∀x⦁a < x ∧ x < b ⇒ f x = f b⌝);
(* *** Goal "1" *** *)
a(lemma_tac⌜∀x⦁a ≤ x ∧ x ≤ b ⇒ f x = f b⌝ THEN1
	(rewrite_tac[ℝ_≤_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac1 THEN all_asm_fc_tac[] THEN REPEAT strip_tac));
a(all_fc_tac[ℝ_less_dense_thm]);
a(∃_tac⌜z⌝ THEN REPEAT strip_tac THEN bc_thm_tac deriv_local_thm);
a(MAP_EVERY ∃_tac[⌜λz:ℝ⦁f b⌝, ⌜b⌝, ⌜a⌝] THEN asm_rewrite_tac[const_deriv_thm]);
(* *** Goal "2" *** *)
a(lemma_tac⌜f b < f x ∨ f x < f b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.1" *** *)
a(bc_thm_tac rolle_lemma);
a(∃_tac⌜df⌝ THEN asm_rewrite_tac[]);
a(∃_tac⌜x⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∃x⦁a < x ∧ x < b ∧ ((λz⦁~(f z)) Deriv ℕℝ 0)x⌝);
(* *** Goal "2.2.1" *** *)
a(bc_thm_tac rolle_lemma);
a(∃_tac⌜λx⦁~(df x)⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2.1.1" *** *)
a(bc_thm_tac minus_comp_cts_thm THEN all_asm_fc_tac[]);
(* *** Goal "2.2.1.2" *** *)
a(LIST_GET_NTH_ASM_T [8] all_fc_tac);
a(RAT_DERIV_T (fn th => all_fc_tac[conv_rule(ONCE_MAP_C ℝ_anf_conv) th]));
a(asm_rewrite_tac[]);
(* *** Goal "2.2.1.3" *** *)
a(∃_tac⌜x⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜((λz⦁~((λz⦁~(f z)) z)) Deriv ~(~(ℕℝ 0)))x'⌝
	(fn th => ante_tac th THEN rewrite_tac[η_axiom]));
a(bc_thm_tac minus_comp_deriv_thm);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cauchy_mean_value_thm⦎ = save_thm ( "cauchy_mean_value_thm", (
set_goal([], ⌜∀f df g dg a b⦁
	a < b
∧	(∀x⦁a ≤ x ∧ x ≤ b ⇒ f Cts x)
∧	(∀x⦁a < x ∧ x < b ⇒ (f Deriv df x) x)
∧	(∀x⦁a ≤ x ∧ x ≤ b ⇒ g Cts x)
∧	(∀x⦁a < x ∧ x < b ⇒ (g Deriv dg x) x)
⇒	(∃x⦁ a < x ∧ x < b
	∧	(dg x)*(f b - f a) = (df x)*(g b - g a))⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃H⦁∀x⦁ H x = (g b - g a)*(f x - f a) - (f b - f a)*(g x - g a)⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∃dH⦁∀x⦁ dH x = (g b - g a)*(df x) - (f b - f a)*(dg x)⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∀x⦁a ≤ x ∧ x ≤ b ⇒ H Cts x⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac
	THEN pure_once_rewrite_tac[prove_rule[]⌜H = (λx⦁H x)⌝]);
a(DROP_NTH_ASM_T 4 once_rewrite_thm_tac THEN rewrite_tac[]);
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac)
	THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∀x⦁a < x ∧ x < b ⇒ (H Deriv dH x) x⌝);
a(REPEAT strip_tac
	THEN pure_once_rewrite_tac[prove_rule[]
		⌜H = (λx⦁H x) ∧ dH = (λx⦁dH x)⌝]);
a(LIST_DROP_NTH_ASM_T [4, 5] pure_once_rewrite_tac THEN rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [4, 6] all_fc_tac);
a(RAT_DERIV_T (fn th => all_fc_tac[th]));
a(POP_ASM_T discard_tac THEN TOP_ASM_T ante_tac
	THEN conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(STRIP_T rewrite_thm_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∃x⦁a < x ∧ x < b ∧ (H Deriv ℕℝ 0) x⌝);
(* *** Goal "2.2.1" *** *)
a(bc_thm_tac rolle_thm);
a(∃_tac⌜dH⌝ THEN LIST_DROP_NTH_ASM_T [2, 9] rewrite_tac);
a(REPEAT strip_tac THEN1
	(contr_tac THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]));
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(LEMMA_T ⌜dH x = ℕℝ 0⌝ ante_tac THEN1 all_fc_tac[deriv_unique_thm]);
a(LIST_DROP_NTH_ASM_T [6] rewrite_tac);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏mean_value_thm⦎ = save_thm ( "mean_value_thm", (
set_goal([], ⌜∀f df a b⦁
	a < b
∧	(∀x⦁a ≤ x ∧ x ≤ b ⇒ f Cts x)
∧	(∀x⦁a < x ∧ x < b ⇒ (f Deriv df x) x)
⇒	(∃x⦁a < x ∧ x < b ∧ f b - f a = (b - a) * df x)⌝);
a(REPEAT strip_tac);
a(ante_tac (
	list_∀_elim
	[⌜λx:ℝ⦁x⌝, ⌜λx:ℝ⦁ℕℝ 1⌝, ⌜f⌝, ⌜df⌝, ⌜a⌝, ⌜b⌝]
	cauchy_mean_value_thm));
a(asm_rewrite_tac[id_cts_thm, id_deriv_thm]
	THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN ALL_ASM_FC_T asm_rewrite_tac[]);
a(POP_ASM_T ante_tac THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
In practice the subtleties about not requiring differentiability at the end points of
the interval etc. just adds complication in many uses of the mean value theorem.
%%%%
%%%%
=SML

val ⦏mean_value_thm1⦎ = save_thm ( "mean_value_thm1", (
set_goal([], ⌜∀f df a b⦁
	a < b
∧	(∀x⦁a ≤ x ∧ x ≤ b ⇒ (f Deriv df x) x)
⇒	(∃x⦁a < x ∧ x < b ∧ f(b) - f(a) = (b - a) * df x)⌝);
a(REPEAT strip_tac THEN bc_thm_tac mean_value_thm THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac deriv_cts_thm);
a(contr_tac THEN all_asm_fc_tac[] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏deriv_0_thm1⦎ = save_thm ( "deriv_0_thm1", (
set_goal([], ⌜∀f a b⦁
	(∀x⦁a <  x ∧ x < b ⇒ (f Deriv ℕℝ 0) x)
⇒	(∀ x y⦁a <  x ∧ x <  y ∧ y < b ⇒ f x = f y)⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜∀ x⦁ a < x ∧ x < b ⇒ f Cts x⌝ THEN1
	(REPEAT strip_tac THEN all_asm_fc_tac[] THEN  all_fc_tac[deriv_cts_thm]));
a(lemma_tac ⌜∀ z⦁ x ≤ z ∧ z ≤ y ⇒ f Cts z⌝ THEN1
	(POP_ASM_T (fn th =>
		(REPEAT strip_tac THEN bc_thm_tac th THEN
			PC_T1 "ℝ_lin_arith" asm_prove_tac[]))));
a(lemma_tac⌜∀ z⦁ x < z ∧ z < y ⇒ (f Deriv (λx⦁ ℕℝ 0) z) z⌝ THEN1
	(DROP_NTH_ASM_T 6 (fn th =>
		(REPEAT strip_tac THEN rewrite_tac[] THEN
			bc_thm_tac th THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]))));
a(all_fc_tac[mean_value_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏deriv_0_thm⦎ = save_thm ( "deriv_0_thm", (
set_goal([], ⌜∀f a b⦁
	(∀x⦁a <  x ∧ x < b ⇒ (f Deriv ℕℝ 0) x)
⇒	(∃c⦁∀ x⦁a <  x ∧ x < b ⇒ f x = c)⌝);
a(REPEAT strip_tac);
a(cases_tac⌜¬a < b⌝ THEN1
	(∃_tac⌜c⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[ℝ_less_dense_thm]);
a(∃_tac⌜f z⌝ THEN REPEAT strip_tac);
a(cases_tac⌜x = z⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜x <  z ∨ z < x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN all_fc_tac[deriv_0_thm1]);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
In applications it is very common to prove a function is constant by proving its
derivative vanishes everywhere:
%%%%
%%%%
=SML

val ⦏deriv_0_thm2⦎ = save_thm ( "deriv_0_thm2", (
set_goal([], ⌜∀f x y⦁
	(∀x⦁(f Deriv ℕℝ 0) x)
⇒	(f x = f y)⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜∃c⦁∀x⦁f x = c⌝ THEN_LIST [id_tac, asm_rewrite_tac[]]);
a(∃_tac⌜f(ℕℝ 0)⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜∃a b⦁a < x ∧ a < ℕℝ 0 ∧ x < b ∧ ℕℝ 0 < b⌝
	THEN1
	(∃_tac⌜~(Abs x) + ~(ℕℝ 1)⌝ THEN ∃_tac⌜Abs x + ℕℝ 1⌝
	THEN cases_tac⌜ℕℝ 0 ≤ x⌝ THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LEMMA_T ⌜∃c⦁∀x⦁ a < x ∧ x < b ⇒  f x = c⌝ strip_asm_tac
	THEN1 bc_thm_tac deriv_0_thm THEN REPEAT strip_tac
	THEN ALL_ASM_FC_T asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏deriv_0_less_thm⦎ = save_thm ( "deriv_0_less_thm", (
set_goal([], ⌜∀f df a b⦁
	a <  b
∧	(∀x⦁a ≤  x ∧ x ≤ b ⇒ f Cts x)
∧	(∀x⦁a <  x ∧ x < b ⇒ (f Deriv df x) x)
∧	(∀x⦁a <  x ∧ x < b ⇒ ℕℝ 0 < df x)
⇒	(f a < f b)⌝);
a(REPEAT strip_tac);
a(all_fc_tac [mean_value_thm]);
a(LEMMA_T⌜ℕℝ 0 < f b - f a⌝ (fn th => ante_tac th THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(pure_asm_rewrite_tac[] THEN bc_thm_tac ℝ_0_less_0_less_times_thm THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%
The following general theorem is used to give bounds on the values of the trigonometric functions.
%%%%
%%%%
=SML

val ⦏deriv_linear_estimate_thm⦎ = save_thm ( "deriv_linear_estimate_thm", (
set_goal([], ⌜
	∀f df a b⦁
	a < b
∧	(∀x⦁ a ≤ x ∧ x ≤ b ⇒ (f Deriv df x) x)
∧	(∀x⦁ a < x ∧ x < b ⇒ Abs (df x) ≤ ℕℝ 1)
⇒	Abs(f b - f a) ≤ b - a
⌝);
a(REPEAT strip_tac THEN all_fc_tac[mean_value_thm1]);
a(asm_rewrite_tac[ℝ_abs_times_thm]);
a(lemma_tac ⌜ℕℝ 0 ≤ b + ~a⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜Abs (b + ~a) = b + ~a⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_abs_def]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y⦁  x*y ≤ x ⇔ ℕℝ 0 ≤ x * (ℕℝ 1 + ~y)⌝]);
a(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Uncountabiliy of the Reals}
We prove Cantor's thorem that the reals are uncountable and develop some useful
facts about sequences and nested intervals {\it en route}.
The first two facts about sequences just give the obvious one-step criteria for a sequence
to be monotone increasing or decreasing.
%%%%
%%%%
=SML

val ⦏ℝ_mono_inc_seq_thm⦎ = save_thm ( "ℝ_mono_inc_seq_thm", (
set_goal([], ⌜∀f : ℕ → ℝ⦁ (∀m⦁f m ≤ f (m+1)) ⇒ (∀m n⦁f m ≤ f(m + n))⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝ THEN1 rewrite_tac[]);
a(bc_thm_tac ℝ_≤_trans_thm);
a(∃_tac⌜f(m+n)⌝ THEN  REPEAT strip_tac);
a(once_rewrite_tac[plus_assoc_thm1] THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f : ℕ → ℝ⦁ (∀m⦁f(m+1) ≤ f m) ⇒ (∀m n⦁ f(m+n) ≤ f m)⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝ THEN1 rewrite_tac[]);
a(bc_thm_tac ℝ_≤_trans_thm);
a(∃_tac⌜f (m+n)⌝ THEN  REPEAT strip_tac);
a(once_rewrite_tac[plus_assoc_thm1] THEN asm_rewrite_tac[]);
val ℝ_mono_dec_seq_thm = save_pop_thm "ℝ_mono_dec_seq_thm";
=TEX
We now want to investigate the ordering relations that hold between the lower and upper
bounds of  a sequence of nested closed intervals.
In the applications, it is easier to work with sequences of lower and upper bounds rather
than the sequences of intervals themselves, and so we do this, while making the names of the
theorems reflect their intended purpose.
We first of all want to prove that no lower bound is greater than any upper bound. We do
the two parts of this assertion as lemmas first:
%%%%
%%%%
=SML
set_goal([], ⌜∀L U: ℕ → ℝ⦁
	(∀m⦁L m ≤ L (m+1) ∧ U (m+1) ≤ U m ∧ L m ≤ U m)
⇒	(∀m n⦁L m ≤ U (m+n))⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀m⦁L m ≤ L(m+1)⌝ THEN1 asm_rewrite_tac[]);
a(all_fc_tac[ℝ_mono_inc_seq_thm]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜L(m+n)⌝ THEN asm_rewrite_tac[]);
val nested_interval_lemma1 = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀L U : ℕ → ℝ⦁
	(∀m⦁L m ≤ L (m+1) ∧ U (m+1) ≤ U m ∧ L m ≤ U m)
⇒	(∀m n⦁L (m+n) ≤ U m)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀m⦁U (m+1) ≤ U m⌝ THEN1 asm_rewrite_tac[]);
a(all_fc_tac[ℝ_mono_dec_seq_thm]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜U(m+n)⌝ THEN asm_rewrite_tac[]);
val nested_interval_lemma2 = pop_thm();
=TEX
The two parts now fit together to give the theorem that no lower bound of a sequence
of nested intervals is greater than any upper bound.
%%%%
%%%%
=SML

val ⦏nested_interval_bounds_thm⦎ = save_thm ( "nested_interval_bounds_thm", (
set_goal([], ⌜∀L U : ℕ → ℝ⦁
	(∀m⦁L m ≤ L (m+1) ∧ U (m+1) ≤ U m ∧ L m ≤ U m)
⇒	(∀m n⦁L m ≤ U n)⌝);
a(REPEAT strip_tac THEN LEMMA_T ⌜m:ℕ ≤ n ∨ n ≤ m⌝ ante_tac THEN1
	rewrite_tac[≤_cases_thm]);
a(rewrite_tac[≤_def] THEN REPEAT strip_tac THEN all_var_elim_asm_tac1 THEN
	ALL_FC_T rewrite_tac [nested_interval_lemma1, nested_interval_lemma2]);
pop_thm()
));

=TEX
We can now prove Cantor's theorem that the reals are uncountable given two more
rather specific lemmas. The first of these lemmas says that given a closed interval containing
more than one point and any real number, there is a sub-interval, also containing more than
one point, that does not contain the given number.
%%%%
%%%%
=SML
set_goal([], ⌜∀a b x : ℝ⦁
	a < b
⇒	(∃c d⦁ a ≤ c ∧ c < d ∧ d ≤ b ∧ (x < c ∨ d < x))⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃u⦁a < u ∧ u < b⌝ THEN1
	(all_fc_tac [ℝ_less_dense_thm] THEN contr_tac THEN all_asm_fc_tac[]));
a(lemma_tac⌜∃v⦁u < v ∧ v < b⌝ THEN1
	(all_fc_tac [ℝ_less_dense_thm] THEN contr_tac THEN all_asm_fc_tac[]));
a(cases_tac⌜x ≤ u⌝ THEN1
	(∃_tac⌜v⌝ THEN ∃_tac⌜b⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜a⌝ THEN ∃_tac⌜u⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏cantor_lemma1⦎ = pop_thm();
=TEX
The second lemma simply makes the previous one easier to use to define the sequences
of lower and upper bounds of a sequence of nested closed intervals whose intersection
will miss a given attempt to enumerate the reals.
%%%%
%%%%
=SML
set_goal([], ⌜∃f g: ℝ → ℝ → ℝ → ℝ⦁ ∀x a b⦁
	a < b
⇒	a ≤ f x a b ∧ g x a b ≤ b ∧ f x a b < g x a b ∧ (x < f x a b ∨ g x a b < x)⌝);
a(prove_∃_tac THEN REPEAT strip_tac);
a(cases_tac⌜¬a'' < b''⌝ THEN asm_rewrite_tac[]);
a(all_fc_tac[cantor_lemma1] THEN (POP_ASM_T (strip_asm_tac o ∀_elim ⌜x''⌝))
	THEN ∃_tac⌜d⌝ THEN ∃_tac⌜c⌝ THEN REPEAT strip_tac);
val ⦏cantor_lemma2⦎ = pop_thm();
=TEX
Now the main part of the proof of Cantor's theorem: if a sequence $X_m$ of real numbers is given,
we can find a sequence of closed intervals $[L_m, U_m]$, such that $X_m \not\in [L_m, U_m]$.
%%%%
%%%%
=SML

val ⦏nested_interval_diag_thm⦎ = save_thm ( "nested_interval_diag_thm", (
set_goal([], ⌜∀X : ℕ → ℝ⦁ ∃L U: ℕ → ℝ⦁∀m⦁
	L m ≤ L (m+1)
∧	U (m+1) ≤ U m
∧	L m < U  m
∧	(X m < L m ∨ U m< X m)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ ∃L U: ℕ → ℝ⦁
	L 0 < U 0
∧	∀m⦁L m < U m 
	⇒	L m ≤ L (m+1)
	∧	U (m+1) ≤ U m
	∧	L (m+1) < U  (m+1)
	∧	(X m < L (m+1) ∨ U (m+1) < X m)⌝);
(* *** Goal "1" *** *)
a(lemma_tac⌜∃a b:ℝ⦁ a < b⌝ THEN1 (∃_tac⌜ℕℝ 0⌝ THEN ∃_tac⌜ℕℝ 1⌝ THEN REPEAT strip_tac));
a(strip_asm_tac cantor_lemma2);
a(lemma_tac⌜∃h : ℕ → ℝ × ℝ⦁
	h 0 = (a, b)
∧	∀m⦁ h(m + 1) = (f (X m) (Fst(h m)) (Snd(h m)), g (X m) (Fst(h m)) (Snd(h m)))
⌝ THEN1 prove_∃_tac);
a(∃_tac⌜λm⦁Fst (h m)⌝ THEN ∃_tac ⌜λm⦁Snd (h m)⌝ THEN strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∀m⦁L m < U m⌝ THEN1
	(strip_tac THEN induction_tac⌜m:ℕ⌝ THEN
	REPEAT strip_tac THEN all_asm_fc_tac[]));
a(DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜λm⦁L(m+1)⌝ THEN ∃_tac ⌜λm⦁U(m+1)⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
Now we show that any sequence of nested closed intervals has non-empty intersection:
%%%%
%%%%
=SML

val ⦏nested_interval_intersection_thm⦎ = save_thm ( "nested_interval_intersection_thm", (
set_goal([], ⌜∀L U: ℕ → ℝ⦁
	(∀m⦁L m ≤ L (m+1) ∧ U (m+1) ≤ U m ∧ L m ≤ U m)
⇒	(∃x⦁∀m⦁L m ≤ x ∧ x ≤U m)⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜
	¬ {x|∃ m⦁ x = L m} = {}
∧	(∃ a⦁ ∀ x⦁ x ∈ {x|∃ m⦁ x = L m} ⇒ x ≤ a)⌝ (∧_THEN asm_tac));
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext" prove_tac[]);
a(∃_tac⌜U k⌝ THEN REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(all_fc_tac[nested_interval_bounds_thm] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜Sup{x|∃ m⦁ x = L m}⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac ℝ_≤_sup_bc_thm THEN asm_rewrite_tac[]);
a(prove_tac[]);
(* *** Goal "2.2" *** *)
a(bc_thm_tac ℝ_sup_≤_bc_thm THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(all_fc_tac[nested_interval_bounds_thm] THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
Putting the last two theorems together gives us Cantor's theorem:
%%%%
%%%%
=SML

val ⦏ℝ_uncountable_thm ⦎ = save_thm ( "ℝ_uncountable_thm ", (
set_goal([], ⌜∀X: ℕ → ℝ⦁ ∃x⦁∀m⦁¬x = X m⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜X⌝ nested_interval_diag_thm));
a(lemma_tac⌜∃x⦁∀m⦁L m ≤ x ∧ x ≤U m⌝ THEN1
	(bc_thm_tac nested_interval_intersection_thm THEN asm_rewrite_tac[]
	THEN asm_rewrite_tac[ℝ_≤_def]));
a(∃_tac⌜x⌝ THEN contr_tac THEN all_var_elim_asm_tac1);
a(spec_nth_asm_tac 1 ⌜m⌝);
a(spec_nth_asm_tac 4 ⌜m⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

val ⦏cantor_ℝ_thm⦎ = ℝ_uncountable_thm;
=TEX
\subsection{More Topology}
We now develop some more topological results.
First of all we prove the standard facts about unions and intersections of open and closed sets
(which comprise the axioms for same in abstract topology).
These facts depend in turn on simpler facts about open and closed intervals:
=TEX
%%%%
%%%%
=SML

val ⦏∩_open_interval_thm⦎ = save_thm ( "∩_open_interval_thm", (
set_goal([], ⌜∀x1 y1 x2 y2⦁∃x y⦁ OpenInterval x1 y1 ∩ OpenInterval x2 y2 = OpenInterval x y⌝);
a(REPEAT strip_tac THEN cases_tac⌜(x1:ℝ) < x2⌝ THEN cases_tac⌜(y1:ℝ) < y2⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜x2⌝ THEN ∃_tac⌜y1⌝ THEN PC_T1 "sets_ext" rewrite_tac[open_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜x2⌝ THEN ∃_tac⌜y2⌝ THEN PC_T1 "sets_ext" rewrite_tac[open_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜x1⌝ THEN ∃_tac⌜y1⌝ THEN PC_T1 "sets_ext" rewrite_tac[open_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(∃_tac⌜x1⌝ THEN ∃_tac⌜y2⌝ THEN PC_T1 "sets_ext" rewrite_tac[open_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏∩_closed_interval_thm⦎ = save_thm ( "∩_closed_interval_thm", (
set_goal([], ⌜∀x1 y1 x2 y2⦁∃x y⦁ ClosedInterval x1 y1 ∩ ClosedInterval x2 y2 = ClosedInterval x y⌝);
a(REPEAT strip_tac THEN cases_tac⌜(x1:ℝ) < x2⌝ THEN cases_tac⌜(y1:ℝ) < y2⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜x2⌝ THEN ∃_tac⌜y1⌝ THEN PC_T1 "sets_ext" rewrite_tac[closed_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜x2⌝ THEN ∃_tac⌜y2⌝ THEN PC_T1 "sets_ext" rewrite_tac[closed_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜x1⌝ THEN ∃_tac⌜y1⌝ THEN PC_T1 "sets_ext" rewrite_tac[closed_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(∃_tac⌜x1⌝ THEN ∃_tac⌜y2⌝ THEN PC_T1 "sets_ext" rewrite_tac[closed_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Now we show that open sets are closed under arbitrary unions \ldots
%%%%
%%%%
=SML

val ⦏⋃_open_ℝ_thm⦎ = save_thm ( "⋃_open_ℝ_thm", (
set_goal([], ⌜∀V⦁ V ⊆ Open⋎R ⇒ ⋃V ∈ Open⋎R⌝);
a(PC_T1"sets_ext" rewrite_tac[open_ℝ_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(∃_tac⌜x'⌝ THEN ∃_tac⌜y⌝ THEN contr_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
\ldots and hence under binary unions \ldots
%%%%
%%%%
=SML

val ⦏∪_open_ℝ_thm ⦎ = save_thm ( "∪_open_ℝ_thm ", (
set_goal([], ⌜∀X Y⦁ X ∈ Open⋎R ∧ Y ∈ Open⋎R ⇒ X ∪ Y ∈ Open⋎R⌝);
a(REPEAT ∀_tac);
a(ante_tac(∀_elim⌜{X; Y}⌝ ⋃_open_ℝ_thm));
a(rewrite_tac[pc_rule1"sets_ext" prove_rule[]⌜∀x y c⦁ {x; y} ⊆ c ⇔ x ∈ c ∧ y ∈ c⌝]);
(* Need lemma which is easier to prove generically: *)
	push_goal([], ⌜∀x y⦁ ⋃{x; y} = x ∪ y⌝);
	a(PC_T1 "sets_ext" REPEAT strip_tac THEN all_asm_fc_tac[]);
	(* *** Goal "1" *** *)
	a(∃_tac⌜x⌝ THEN PC_T1 "sets_ext" REPEAT strip_tac);
	(* *** Goal "2" *** *)
	a(∃_tac⌜y⌝ THEN PC_T1 "sets_ext" REPEAT strip_tac);
(a o rewrite_thm_tac o pop_thm)();
pop_thm()
));

=TEX
\ldots and under binary intersections \ldots
%%%%
%%%%
=SML

val ⦏∩_open_ℝ_thm ⦎ = save_thm ( "∩_open_ℝ_thm ", (
set_goal([], ⌜∀X Y⦁ X ∈ Open⋎R ∧ Y ∈ Open⋎R ⇒ X ∩ Y ∈ Open⋎R⌝);
a(rewrite_tac[open_ℝ_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(strip_asm_tac (list_∀_elim[⌜x⌝, ⌜y⌝, ⌜x'⌝ , ⌜y'⌝] ∩_open_interval_thm));
a(∃_tac⌜x''⌝ THEN ∃_tac⌜y''⌝ THEN POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(REPEAT_N 4 (POP_ASM_T ante_tac) THEN PC_T1 "sets_ext" prove_tac[]);
pop_thm()
));

=TEX
To get the analogous fcts for closed sets, we need a lemma about complements of
intersections:
%%%%
%%%%
=SML
set_goal([], ⌜∀v⦁~(⋂v) = ⋃{a | ~a ∈ v}⌝);
a(PC_T1"sets_ext" rewrite_tac[complement_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜~s⌝ THEN rewrite_tac[complement_def] THEN REPEAT strip_tac);
a(asm_rewrite_tac[pc_rule1"sets_ext" prove_rule[complement_def]⌜∀a:'a SET⦁~ (~ a) = a⌝]);
(* *** Goal "2" *** *)
a(∃_tac⌜~s⌝ THEN rewrite_tac[complement_def] THEN REPEAT strip_tac);
val ⦏complement_⋂_lemma⦎ = pop_thm();
=TEX
\ldots whence closed sets are closed under arbitrary intersections \ldots
%%%%
%%%%
=SML

val ⦏⋂_closed_ℝ_thm⦎ = save_thm ( "⋂_closed_ℝ_thm", (
set_goal([], ⌜∀V⦁ V ⊆ Closed⋎R ⇒ ⋂V ∈ Closed⋎R⌝);
a(rewrite_tac[closed_ℝ_def, complement_⋂_lemma]);
a(REPEAT strip_tac THEN bc_thm_tac ⋃_open_ℝ_thm);
a(PC_T1"sets_ext" asm_prove_tac []);
a(ALL_ASM_FC_T (MAP_EVERY ante_tac) []);
a(rewrite_tac[pc_rule1"sets_ext" prove_rule[complement_def]⌜∀a:'a SET⦁~ (~ a) = a⌝]);
pop_thm()
));

=TEX
\ldots and under binary intersections \ldots
%%%%
%%%%
=SML

val ⦏∩_closed_ℝ_thm⦎ = save_thm ( "∩_closed_ℝ_thm", (
set_goal([], ⌜∀X Y⦁ X ∈ Closed⋎R ∧ Y ∈ Closed⋎R ⇒ X ∩ Y ∈ Closed⋎R⌝);
a(rewrite_tac[closed_ℝ_def,
	pc_rule1"sets_ext" prove_rule[complement_def]⌜∀a b⦁~(a ∩ b) = ~a ∪ ~b⌝]);
a(REPEAT strip_tac THEN bc_thm_tac ∪_open_ℝ_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
\ldots and under binary unions:
%%%%
%%%%
=SML

val ⦏∪_closed_ℝ_thm⦎ = save_thm ( "∪_closed_ℝ_thm", (
set_goal([], ⌜∀X Y⦁ X ∈ Closed⋎R ∧ Y ∈ Closed⋎R ⇒ X ∪ Y ∈ Closed⋎R⌝);
a(rewrite_tac[closed_ℝ_def,
	pc_rule1"sets_ext" prove_rule[complement_def]⌜∀a b⦁~(a ∪ b) = ~a ∩ ~b⌝]);
a(REPEAT strip_tac THEN bc_thm_tac ∩_open_ℝ_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
We have already proved that closed intervals are closed sets.
We now prove that opern intervals are open sets and various facts about complements
of intervals and half-infinite intervals (which we just write out as set comprehensions):
%%%%
%%%%
=SML

val ⦏open_interval_open_thm⦎ = save_thm ( "open_interval_open_thm", (
set_goal([], ⌜∀x y⦁ OpenInterval x y ∈ Open⋎R⌝);
a(rewrite_tac[open_ℝ_def] THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN ∃_tac⌜y⌝ THEN PC_T1 "sets_ext" REPEAT strip_tac);
pop_thm()
));

=TEX
The complement of an open interval is the union of two closed half-infinite intervals:
%%%%
%%%%
=SML

val ⦏complement_open_interval_thm⦎ = save_thm ( "complement_open_interval_thm", (
set_goal([], ⌜∀x y⦁ ~(OpenInterval x y) = {t | t ≤ x} ∪ {t | y ≤ t}⌝);
a(rewrite_tac[open_interval_def]);
a(PC_T1"sets_ext" rewrite_tac[complement_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The complement of a closed interval is the union of two open half-infinite intervals:
%%%%
%%%%
=SML

val ⦏complement_closed_interval_thm⦎ = save_thm ( "complement_closed_interval_thm", (
set_goal([], ⌜∀x y⦁ ~(ClosedInterval x y) = {t | t < x} ∪ {t | y < t}⌝);
a(rewrite_tac[closed_interval_def]);
a(PC_T1"sets_ext" rewrite_tac[complement_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Open half-infinite intervals are open sets:
%%%%
%%%%
=SML

val ⦏half_infinite_intervals_open_thm⦎ = save_thm ( "half_infinite_intervals_open_thm", (
set_goal([], ⌜∀x⦁ {t | t < x} ∈ Open⋎R ∧ {t | x < t} ∈ Open⋎R⌝);
a(rewrite_tac [open_ℝ_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[ℝ_less_dense_thm]);
a(strip_asm_tac (∀_elim⌜t⌝ℝ_unbounded_below_thm));
a(∃_tac⌜y⌝ THEN  ∃_tac⌜z⌝ THEN PC_T1 "sets_ext" rewrite_tac[open_interval_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_fc_tac[ℝ_less_dense_thm]);
a(strip_asm_tac (∀_elim⌜t⌝ℝ_unbounded_above_thm));
a(∃_tac⌜z⌝ THEN  ∃_tac⌜y⌝ THEN PC_T1 "sets_ext" rewrite_tac[open_interval_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Closed half-infinite intervals are closed sets:
%%%%
%%%%
=SML

val ⦏half_infinite_intervals_closed_thm⦎ = save_thm ( "half_infinite_intervals_closed_thm", (
set_goal([], ⌜∀x⦁ {t | t ≤ x} ∈ Closed⋎R ∧ {t | x ≤ t} ∈ Closed⋎R⌝);
a(rewrite_tac [closed_ℝ_def]);
a(LEMMA_T⌜∀x:ℝ⦁ ~ {t|t ≤ x} = {t | x < t} ∧ ~ {t|x ≤ t} = {t | t < x}⌝
	(fn th => rewrite_tac[th, half_infinite_intervals_open_thm]));
a(PC_T1 "sets_ext" rewrite_tac[complement_def] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
The empty set and the set of all real numbers are both open and closed:
%%%%
%%%%
=SML

val ⦏empty_universe_open_closed_thm⦎ = save_thm ( "empty_universe_open_closed_thm", (
set_goal([], ⌜{} ∈ Open⋎R ∧ Universe ∈ Open⋎R ∧ {} ∈ Closed⋎R ∧ Universe ∈ Closed⋎R⌝);
a(rewrite_tac [closed_ℝ_def, taut_rule⌜∀p q⦁ p ∧ q ∧ q ∧ p ⇔ p ∧ q⌝]);
a(rewrite_tac[open_ℝ_def] THEN REPEAT strip_tac);
a(rewrite_tac[open_interval_def]);
a(∃_tac ⌜t + ~(ℕℝ 1)⌝ THEN ∃_tac⌜t + (ℕℝ 1)⌝ THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
Now we can prove that compact sets are closed:
%%%%
%%%%
=SML

val ⦏compact_closed_thm ⦎ = save_thm ( "compact_closed_thm ", (
set_goal([], ⌜Compact⋎R ⊆ Closed⋎R⌝);
a(PC_T1 "sets_ext" rewrite_tac[]);
a(rewrite_tac[compact_ℝ_def]);
a(REPEAT strip_tac THEN rename_tac[(⌜x:ℝ SET⌝, "C")]);
a(cases_tac⌜C = {}⌝ THEN1 asm_rewrite_tac[empty_universe_open_closed_thm]);
a(rewrite_tac [closed_ℝ_def] THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1"sets_ext"prove_rule[complement_def]⌜∀a:'a SET⦁~a = {z | ¬z ∈ a}⌝]);
a(rewrite_tac[open_ℝ_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∃V⦁V = {X | ∃e⦁ ℕℝ 0 < e ∧ X = {z | z < t + ~e} ∪{z | t + e < z}}⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜V ⊆ Open⋎R ∧ C ⊆ ⋃ V⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T "sets_ext" strip_tac THEN all_var_elim_asm_tac1 THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN bc_thm_tac ∪_open_ℝ_thm);
a(rewrite_tac[half_infinite_intervals_open_thm]);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜t⌝]ℝ_less_cases_thm) THEN_TRY (SOLVED_T all_var_elim_asm_tac)
	THEN all_fc_tac[ℝ_less_dense_thm]);
(* *** Goal "2.1" *** *)
a(∃_tac⌜{w|w < t + ~(t + ~z)} ∪ {w|t + (t + ~z) < w}⌝ THEN REPEAT strip_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN REPEAT strip_tac);
a(∃_tac⌜t + ~z⌝ THEN REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜{w|w < t + ~(z + ~t)} ∪ {w|t + (z + ~t) < w}⌝ THEN REPEAT strip_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN REPEAT strip_tac);
a(∃_tac⌜z + ~t⌝ THEN REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(all_asm_fc_tac[]);
a(cases_tac⌜W = {}⌝ THEN1 PC_T1 "sets_ext" asm_prove_tac[]);
a(lemma_tac⌜∀A B⦁ A ∈ W ∧ B ∈ W ⇒ A ⊆ B ∨ B ⊆ A⌝);
(* *** Goal "3.1" *** *)
a(REPEAT ∀_tac THEN ⇒_tac);
a(LEMMA_T⌜A ∈ V ∧ B ∈ V⌝ ante_tac THEN1 PC_T1 "sets_ext" asm_prove_tac[]);
a(asm_rewrite_tac[] THEN ⇒_tac THEN asm_rewrite_tac[]);
a(strip_asm_tac(list_∀_elim[⌜e⌝, ⌜e'⌝] ℝ_≤_cases_thm) THEN_LIST
	[∨_right_tac, ∨_left_tac] THEN PC_T1 "sets_ext" REPEAT strip_tac
	THEN PC_T1"ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.2" *** *)
a(all_fc_tac[finite_chain_thm]);
a(LEMMA_T ⌜A ∈ V⌝ ante_tac THEN1 PC_T1 "sets_ext" asm_prove_tac[]);
a(var_elim_nth_asm_tac 10 THEN REPEAT strip_tac);
a(∃_tac⌜t + ~e⌝ THEN ∃_tac⌜t + e⌝ THEN rewrite_tac[open_interval_def] THEN
	PC_T1 "sets_ext" REPEAT strip_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜C ⊆ A⌝ ante_tac THEN1 (var_elim_nth_asm_tac 5 THEN strip_tac));
a(LEMMA_T⌜¬x ∈ A⌝ ante_tac THEN_LIST
	[asm_rewrite_tac[], PC_T1 "sets_ext" prove_tac[]]);
a(PC_T1 "sets_ext" REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Compact sets contain their minimum and maximum values:
%%%%
%%%%
=SML

val ⦏compact_min_max_thm ⦎ = save_thm ( "compact_min_max_thm ", (
set_goal([], ⌜∀X⦁
	¬X = {}
∧	X ∈ Compact⋎R
⇒	∃L U⦁ L ∈ X ∧ U ∈ X ∧ ∀x⦁x ∈ X ⇒ L ≤ x ∧ x ≤ U⌝);
a(REPEAT strip_tac);
a(strip_asm_tac id_cts_thm);
a(LEMMA_T⌜∀t⦁ (λx⦁~((λx⦁ x)x)) Cts t⌝ ante_tac THEN1
	(∀_tac THEN bc_thm_tac minus_comp_cts_thm THEN asm_rewrite_tac[]));
a(rewrite_tac[] THEN strip_tac);
a(ALL_FC_T (MAP_EVERY ante_tac) [cts_compact_maximum_thm]);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀x y:ℝ⦁~x ≤ ~y ⇔ y ≤ x⌝]
	THEN REPEAT strip_tac);
a(∃_tac⌜x'⌝ THEN ∃_tac⌜x⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
Closed subsets of compact sets are compact:
%%%%
%%%%
=SML

val ⦏closed_⊆_compact_thm ⦎ = save_thm ( "closed_⊆_compact_thm ", (
set_goal([], ⌜∀X Y⦁
	Y ∈ Closed⋎R ∧ Y ⊆ X ∧ X ∈ Compact⋎R
⇒	Y ∈ Compact⋎R⌝);
a(rewrite_tac[closed_ℝ_def, compact_ℝ_def] THEN REPEAT strip_tac);
a(lemma_tac⌜{~Y} ∪ V ⊆ Open⋎R ∧ X ⊆ ⋃({~Y} ∪ V)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac (pc_rule1 "sets_ext" prove_rule[] ⌜∀x b c⦁x ∈ c ∧ b ⊆ c ⇒ {x} ∪ b ⊆ c⌝)
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(cases_tac⌜x ∈ Y⌝);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 3 (PC_T1 "sets_ext" strip_asm_tac));
a(PC_T1 "sets_ext" all_asm_fc_tac[]);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(∃_tac⌜~Y⌝ THEN rewrite_tac[complement_def] THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(all_asm_fc_tac[]);
a(∃_tac⌜W \ {~Y}⌝ THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(bc_thm_tac (pc_rule1 "sets_ext" prove_rule[] ⌜∀a b c⦁a ⊆ b ∪ c ⇒ a \ b ⊆ c⌝)
	THEN REPEAT strip_tac);
(* *** Goal "3.2" *** *)
a(bc_thm_tac ⊆_finite_thm THEN ∃_tac⌜W⌝ THEN PC_T1 "sets_ext" prove_tac[]);
(* *** Goal "3.3" *** *)
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(lemma_tac⌜Y ⊆ ⋃W⌝ THEN1
	all_fc_tac [pc_rule1 "sets_ext" prove_rule[] ⌜∀a b c⦁a ⊆ b ∧ b ⊆  c ⇒ a ⊆ c⌝]);
a(POP_ASM_T ante_tac THEN POP_ASM_T ante_tac THEN DROP_ASMS_T discard_tac
	THEN PC_T1 "sets_ext" REPEAT strip_tac);
a(PC_T1 "sets_ext" all_asm_fc_tac[]);
a(∃_tac⌜s⌝ THEN REPEAT strip_tac);
a(contr_tac THEN all_var_elim_asm_tac1);
a(PC_T1 "sets_ext" asm_prove_tac[complement_def]);
pop_thm()
));

=TEX
The empty set is compact but the set of all real numbers is not:
%%%%
%%%%
=SML

val ⦏empty_universe_compact_thm ⦎ = save_thm ( "empty_universe_compact_thm ", (
set_goal([], ⌜{} ∈ Compact⋎R ∧ ¬Universe ∈ Compact⋎R⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[compact_ℝ_def] THEN REPEAT strip_tac THEN ∃_tac⌜{}⌝
	THEN rewrite_tac[empty_finite_thm]);
(* *** Goal "2" *** *)
a(contr_tac THEN LEMMA_T⌜¬(Universe:ℝ SET) = {}⌝ asm_tac THEN1
	PC_T1 "sets_ext" rewrite_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [compact_min_max_thm ]);
a(rewrite_tac[] THEN contr_tac);
a(strip_asm_tac(∀_elim⌜L⌝ ℝ_unbounded_below_thm));
a(lemma_tac⌜L ≤ y⌝ THEN1 asm_rewrite_tac[]);
a(PC_T1"ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
The Heine-Borel theorem: a set is compact iff. it is closed and bounded:
%%%%
%%%%
=SML

val ⦏heine_borel_thm ⦎ = save_thm ( "heine_borel_thm ", (
set_goal([], ⌜∀X⦁
	X ∈ Compact⋎R
⇔	X ∈ Closed⋎R ∧ ∃L U⦁ ∀x⦁x ∈ X ⇒ L ≤ x ∧ x ≤ U⌝);
a(∀_tac);
a(cases_tac⌜X = {}⌝ THEN1 asm_rewrite_tac[
	empty_universe_open_closed_thm, empty_universe_compact_thm]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext" all_fc_tac[compact_closed_thm]);
(* *** Goal "2" *** *)
a(all_fc_tac[compact_min_max_thm]);
a(∃_tac⌜L⌝ THEN ∃_tac⌜U⌝ THEN POP_ASM_T accept_tac);
(* *** Goal "3" *** *)
a(lemma_tac⌜X ⊆ ClosedInterval L U⌝ THEN1
	PC_T1 "sets_ext" asm_rewrite_tac[closed_interval_def]);
a(bc_thm_tac closed_⊆_compact_thm);
a(∃_tac⌜ClosedInterval L U⌝ THEN asm_rewrite_tac[closed_interval_compact_thm]);
pop_thm()
));

=TEX
The following lemma contains most of the proof that the real numbers are connected.
It says that if $X$ and $Y$ are non-empty open sets whose union is the set of all real numbers
then $X$ and $Y$ are not disjoint, under the hypothesis that $X$ contains
an element that is smaller than some element of $Y$ (which is a technical convenience to
simplify the case analysis in the general result):
%%%%
%%%%
=SML
set_goal([], ⌜∀X Y x y⦁
	x ∈ X ∧ X ∈ Open⋎R ∧ y ∈ Y ∧ Y ∈ Open⋎R ∧ (∀x⦁x ∈ X ∪ Y) ∧ x < y
⇒	(∃x⦁ x ∈ X ∩ Y)⌝);
a(PC_T "sets_ext" contr_tac);
a(LEMMA_T⌜∃f⦁ f = (λt⦁ if t ∈ X then x else y)⌝ (∃_THEN asm_tac) THEN1 prove_∃_tac);
a(lemma_tac⌜∀t⦁x ≤ t ∧ t ≤ y ⇒ f Cts t⌝ THEN1 (strip_tac THEN STRIP_T discard_tac));
a(all_var_elim_asm_tac1 THEN intro_∀_tac(⌜t⌝, ⌜t⌝));
(* *** Goal "1" *** *)
a(rewrite_tac[cts_open_ℝ_thm] THEN REPEAT strip_tac);
a(cases_tac⌜x ∈ A⌝ THEN cases_tac ⌜y ∈ A⌝);
(* *** Goal "1.1" *** *)
a(lemma_tac⌜{x'|(if x' ∈ X then x else y) ∈ A} = Universe⌝ THEN_LIST
	[id_tac, asm_rewrite_tac[empty_universe_open_closed_thm]]);
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(cases_tac⌜x' ∈ X⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜{x'|(if x' ∈ X then x else y) ∈ A} = X⌝ THEN_LIST
	[id_tac, asm_rewrite_tac[]]);
a(PC_T1 "sets_ext" REPEAT strip_tac THEN POP_ASM_T ante_tac
	THEN cases_tac⌜x' ∈ X⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a(lemma_tac⌜{x'|(if x' ∈ X then x else y) ∈ A} = Y⌝ THEN_LIST
	[id_tac, asm_rewrite_tac[]]);
a(PC_T1 "sets_ext" REPEAT strip_tac THEN POP_ASM_T ante_tac
	THEN cases_tac⌜x' ∈ X⌝ THEN asm_rewrite_tac[]
	THEN PC_T1 "sets_ext" asm_prove_tac[]);
(* *** Goal "1.4" *** *)
a(lemma_tac⌜{x'|(if x' ∈ X then x else y) ∈ A} = {}⌝ THEN_LIST
	[id_tac, asm_rewrite_tac[empty_universe_open_closed_thm]]);
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN cases_tac⌜x' ∈ X⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜¬y ∈ X⌝ THEN1 PC_T1 "sets_ext" asm_prove_tac[]);
a(all_fc_tac[ℝ_less_dense_thm]);
a(lemma_tac⌜f x < z ∧ z < f y⌝ THEN1 asm_rewrite_tac[]);
a(strip_asm_tac intermediate_value_thm THEN rename_tac[]);
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a(cases_tac⌜x' ∈ X⌝ THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏connected_lemma⦎ = pop_thm();
=TEX
Now we can prove the general result that the real numbers cannot be written as the union of
two disjoint non-empty open sets. I.e., the topological space of real numbers is connected.
%%%%
%%%%
=SML

val ⦏ℝ_connected_thm ⦎ = save_thm ( "ℝ_connected_thm ", (
set_goal([], ⌜∀X Y⦁
	¬X = {} ∧ X ∈ Open⋎R ∧ ¬Y = {} ∧ Y ∈ Open⋎R ∧ (∀x⦁x ∈ X ∪ Y)
⇒	(∃x⦁ x ∈ X ∩ Y)⌝);
a(PC_T1 "sets_ext" REPEAT strip_tac THEN rename_tac[(⌜x':ℝ⌝, "y")]);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜y⌝]ℝ_less_cases_thm) THEN_LIST [
	bc_thm_tac connected_lemma,
	PC_T1 "sets_ext" asm_prove_tac[],
	bc_thm_tac (once_rewrite_rule[
		pc_rule1"sets_ext" prove_rule[]⌜∀a b⦁a ∪ b = b ∪ a ∧ a ∩ b = b ∩ a⌝]
			connected_lemma)]
	THEN contr_tac THEN rename_tac[] THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
\subsection{Cauchy Sequences}
In this section we prove that a sequence of real numbers converges iff. it is a Cauchy
sequence. For future use, we will prove various standard lemmas first.

The easy direction is to show that any convergent sequence is a Cauchy sequence:
%%%%
%%%%
=SML

val ⦏lim_seq_cauchy_seq_thm ⦎ = save_thm ( "lim_seq_cauchy_seq_thm ", (
set_goal([], ⌜∀s x⦁s -> x ⇒ ∀e⦁ ℕℝ 0 < e ⇒∃n⦁∀k m⦁n ≤ k ∧ n ≤ m ⇒ Abs(s k - s m) < e⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_asm_fc_tac[]);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 discard_tac THEN all_asm_fc_tac[]);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜Abs(s k + ~x) + Abs(~(s m + ~x))⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ℝ_abs_plus_bc_thm);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (rewrite_tac[ℝ_abs_minus_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
For the converse, we will need to know that finite sequences are bounded above \ldots
%%%%
%%%%
=SML

val ⦏fin_seq_bounded_thm⦎ = save_thm ( "fin_seq_bounded_thm", (
set_goal([], ⌜∀s : ℕ → ℝ; n⦁ ∃b⦁ ∀m⦁ m ≤ n ⇒ s m < b⌝);
a(REPEAT strip_tac THEN induction_tac⌜n:ℕ⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜s 0 + ℕℝ 1⌝ THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1 THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(strip_asm_tac(list_∀_elim[⌜s(n+1)⌝, ⌜b⌝]ℝ_≤_cases_thm));
(* *** Goal "2.1" *** *)
a(∃_tac⌜b + ℕℝ 1⌝ THEN REPEAT strip_tac);
a(cases_tac⌜m' ≤ n⌝ THEN1 (all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜m' = n + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜s(n+1) + ℕℝ 1⌝ THEN REPEAT strip_tac);
a(cases_tac⌜m' ≤ n⌝ THEN1 (all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜m' = n + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
\ldots and that Cauchy sequences are bounded above \ldots
%%%%
%%%%
=SML

val ⦏cauchy_seq_bounded_above_thm ⦎ = save_thm ( "cauchy_seq_bounded_above_thm ", (
set_goal([], ⌜∀s : ℕ → ℝ⦁
	(∀e⦁ ℕℝ 0 < e ⇒∃n⦁∀k m⦁n ≤ k ∧ n ≤ m ⇒ Abs(s k - s m) < e)
⇒	∃b⦁ ∀m⦁s m < b⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜ℕℝ 0⌝ℝ_unbounded_above_thm));
a(all_asm_fc_tac[] THEN LIST_DROP_NTH_ASM_T [3] discard_tac);
a(strip_asm_tac(list_∀_elim[⌜s⌝, ⌜n⌝]fin_seq_bounded_thm));
a(∃_tac⌜b + y⌝ THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜m⌝, ⌜n⌝]≤_cases_thm));
(* *** Goal "1" *** *)
a(all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(SPEC_NTH_ASM_T 3 ⌜n⌝ (fn th => all_fc_tac[th]));
a(spec_nth_asm_tac 3 ⌜n⌝);
a(cases_tac⌜ℕℝ 0 ≤ s n + ~ (s m)⌝);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[ℝ_abs_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[ℝ_abs_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
\ldots and below (so that we can argue about suprema and infima of subsets of
the range of the sequence):
%%%%
%%%%
=SML

val ⦏cauchy_seq_bounded_below_thm ⦎ = save_thm ( "cauchy_seq_bounded_below_thm ", (
set_goal([], ⌜∀s : ℕ → ℝ⦁
	(∀e⦁ ℕℝ 0 < e ⇒∃n⦁∀k m⦁n ≤ k ∧ n ≤ m ⇒ Abs(s k - s m) < e)
⇒	∃b⦁ ∀m⦁b  < s m⌝);
a(LEMMA_T⌜∀x y:ℝ⦁Abs (x - y) = Abs(~x + y)⌝ once_rewrite_thm_tac THEN1
	(once_rewrite_tac[pc_rule1"ℝ_lin_arith"prove_rule[]⌜∀x y:ℝ⦁ ~x + y = ~(x + ~y)⌝]
	THEN rewrite_tac[ℝ_abs_minus_thm]));
a(REPEAT strip_tac);
a(all_fc_tac[rewrite_rule[](∀_elim⌜λm⦁~(s m)⌝ cauchy_seq_bounded_above_thm)]);
a(∃_tac⌜~b⌝ THEN REPEAT strip_tac);
a(asm_rewrite_tac[pc_rule1"ℝ_lin_arith"prove_rule[]⌜∀x y:ℝ⦁ ~x <  y ⇔ ~y < x⌝]);
pop_thm()
));

=TEX
Any (non-strict) monotone increasing sequence with an upper bound converges (to the supremum of
the set of values taken by the sequence), moreover the terms of the sequence are all no smaller than
the limit.
We prove this first of all giiving the explicit value for the limit.
%%%%
%%%%
=SML

val ⦏lim_seq_mono_inc_sup_thm ⦎ = save_thm ( "lim_seq_mono_inc_sup_thm ", (
set_goal([], ⌜∀s: ℕ → ℝ; ub⦁
	(∀m⦁s m ≤ ub ∧ s m ≤ s (m+1))
⇒	(s -> Sup{t | ∃m⦁t = s m} ∧ (∀m⦁s m ≤ Sup{t | ∃m⦁t = s m} ))
⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac ⌜∀ m n⦁ s m ≤ s (m + n)⌝ THEN1
	(bc_thm_tac ℝ_mono_inc_seq_thm THEN asm_rewrite_tac[]));
a(LEMMA_T⌜
	¬{t | ∃m⦁t = s m} = {}
∧	(∃a⦁ ∀x⦁x ∈ {t | ∃m⦁t = s m} ⇒ x ≤ a)⌝ (∧_THEN asm_tac)  THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext" REPEAT strip_tac THEN ∃_tac⌜s m⌝ THEN rewrite_tac[]);
a(∃_tac⌜m⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(∃_tac ⌜ub⌝ THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜∀m⦁s m ≤ (Sup {t|∃ m⦁ t = s m})⌝ THEN1
	(strip_tac THEN bc_thm_tac ℝ_≤_sup_bc_thm THEN
	asm_rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "3.1" *** *)
a(POP_ASM_T bc_thm_tac THEN ∃_tac⌜m⌝ THEN REPEAT strip_tac);
(* *** Goal "3.2" *** *)
a(lemma_tac⌜∀m⦁ℕℝ 0 ≤ Sup {t|∃ m⦁ t = s m} + ~(s m)⌝ THEN1
	(REPEAT strip_tac THEN spec_nth_asm_tac 1 ⌜m:ℕ⌝
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(once_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ ⦁a + ~b = ~(b + ~a)⌝]);
a(rewrite_tac[ℝ_abs_minus_thm] THEN asm_rewrite_tac[ℝ_abs_def]);
a(ante_tac (∀_elim⌜{t|∃ m⦁ t = s m}⌝ ℝ_less_sup_thm)
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(contr_tac THEN LEMMA_T⌜Sup {t|∃ m⦁ t = s m} + ~e < Sup {t|∃ m⦁ t = s m}⌝ ante_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(pure_asm_rewrite_tac[] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜m⌝ THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[≤_def] THEN contr_tac
	THEN all_var_elim_asm_tac1);
a(lemma_tac⌜s m ≤ s (m + i)⌝ THEN1 asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(bc_thm_tac ℝ_≤_sup_bc_thm THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN ∃_tac ⌜m⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
Now we give the pure existence version:
%%%%
%%%%
=SML

val ⦏lim_seq_mono_inc_thm ⦎ = save_thm ( "lim_seq_mono_inc_thm ", (
set_goal([], ⌜∀s: ℕ → ℝ; ub⦁
	(∀m⦁s m ≤ ub ∧ s m ≤ s (m+1))
⇒	∃x⦁ s -> x ∧ (∀m⦁s m ≤ x )
⌝);
a(REPEAT strip_tac THEN ∃_tac⌜Sup {t|∃ m:ℕ⦁ t = s m}⌝
	THEN all_fc_tac[lim_seq_mono_inc_sup_thm]
	THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
And similarly for a  (non-strict) monotone decreasing sequence with a lower bound:
%%%%
%%%%
=SML

val ⦏lim_seq_mono_dec_thm ⦎ = save_thm ( "lim_seq_mono_dec_thm ", (
set_goal([], ⌜∀s: ℕ → ℝ; lb⦁
	(∀m⦁lb ≤ s m ∧ s (m+1) ≤ s m)
⇒	∃x⦁ s -> x ∧ (∀m⦁x ≤ s m )
⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜∃u⦁∀m⦁u m = ~(s m)⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜∀m⦁u m ≤ ~lb  ∧ u m ≤ u (m+1)⌝ THEN1
	asm_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁~a ≤ ~b ⇔b ≤ a⌝]);
a(all_fc_tac[lim_seq_mono_inc_thm] THEN ∃_tac⌜~ x:ℝ⌝);
a(ante_tac minus_cts_thm THEN rewrite_tac[cts_lim_seq_thm]);
a(REPEAT ∀_tac THEN (STRIP_T (fn th => all_fc_tac[th])));
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[η_axiom,
	pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a : ℝ; f m⦁~a ≤ f m ⇔ ~(f m) ≤ a⌝]);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
Any sequence bounded below and above has an {\em upper bound} or
$\mbox{\sf lim}\;\mbox{\sf sup}$.
%%%%
%%%%
=SML

val ⦏lim_sup_thm ⦎ = save_thm ( "lim_sup_thm ", (
set_goal([], ⌜∀s: ℕ → ℝ; lb ub⦁
	(∀m⦁lb ≤ s m ∧ s m ≤ ub)
⇒	∃lim_sup⦁ ∀e⦁ ℕℝ 0 < e ⇒
		(∃n⦁ ∀m⦁n ≤ m ⇒ s m < lim_sup + e)
	∧	(∀n⦁∃m⦁ n ≤ m ∧ lim_sup < s m + e)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃U⦁∀m⦁U m = Sup{t | ∃n⦁m ≤ n ∧ t =s n}⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜∀m⦁
	¬{t | ∃n⦁m ≤ n ∧ t =s n} = {}
∧	(∃a⦁ ∀x⦁x ∈ {t | ∃n⦁m ≤ n ∧ t =s n} ⇒ x ≤ a)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext" REPEAT strip_tac THEN ∃_tac⌜s m⌝ THEN rewrite_tac[]);
a(∃_tac⌜m⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(∃_tac ⌜ub⌝ THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜∀m⦁lb ≤ U m ∧ U (m+1) ≤ U m⌝ THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(asm_rewrite_tac[] THEN bc_thm_tac ℝ_≤_sup_bc_thm
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜s m⌝ THEN REPEAT strip_tac
	THEN1 asm_rewrite_tac[]);
a(POP_ASM_T bc_thm_tac THEN ∃_tac⌜m⌝ THEN REPEAT strip_tac);
(* *** Goal "3.2" *** *)
a(asm_rewrite_tac[] THEN bc_thm_tac ℝ_⊆_sup_thm THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(∃_tac ⌜n⌝ THEN asm_rewrite_tac[] THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3.3" *** *)
a(all_fc_tac[lim_seq_mono_dec_thm]);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[lim_seq_def]));
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "3.3.1" *** *)
a(lemma_tac⌜ℕℝ 0 < (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_asm_fc_tac[]);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜U m⌝ 
	THEN REPEAT strip_tac THEN1 asm_rewrite_tac[]);
(* *** Goal "3.3.1.1" *** *)
a(bc_thm_tac ℝ_≤_sup_bc_thm THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN ∃_tac ⌜m⌝ THEN REPEAT strip_tac);
(* *** Goal "3.3.1.2" *** *)
a(DROP_NTH_ASM_T 8 discard_tac);
a(DROP_NTH_ASM_T 3 (fn th => all_asm_fc_tac[] THEN asm_tac th));
a(lemma_tac⌜ℕℝ 0 ≤ U m + ~ x⌝ THEN1
	(spec_nth_asm_tac 6 ⌜m⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[ℝ_abs_def]
	THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.3.2" *** *)
a(contr_tac THEN POP_ASM_T (strip_asm_tac o
	rewrite_rule[taut_rule⌜∀p q⦁¬(p ∧ q) ⇔ p ⇒ ¬q⌝,
		pc_rule1"ℝ_lin_arith" prove_rule[] ⌜∀a b:ℝ⦁¬a < b ⇔ b ≤ a⌝]));
a(LEMMA_T⌜¬x ≤ U n⌝ (fn th => ante_tac th THEN asm_rewrite_tac[]));
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜∀a b:ℝ⦁¬a  ≤ b ⇔ b < a⌝]);
a(asm_rewrite_tac[] THEN bc_thm_tac ℝ_sup_less_bc_thm THEN asm_rewrite_tac[]);
a(∃_tac⌜x + ~ (1/2)* e⌝ THEN REPEAT strip_tac THEN_LIST
	[all_var_elim_asm_tac1, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(spec_nth_asm_tac 2 ⌜n'⌝);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
And any sequence bounded below and above has a {\em lower bound} or
$\mbox{\sf lim}\;\mbox{\sf inf}$.
%%%%
%%%%
=SML

val ⦏lim_inf_thm ⦎ = save_thm ( "lim_inf_thm ", (
set_goal([], ⌜∀s: ℕ → ℝ; lb ub⦁
	(∀m⦁lb ≤ s m ∧ s m ≤ ub)
⇒	∃lim_inf⦁ ∀e⦁ ℕℝ 0 < e ⇒
		(∃n⦁ ∀m⦁n ≤ m ⇒  lim_inf - e < s m)
	∧	(∀n⦁∃m⦁ n ≤ m ∧ s m - e < lim_inf)
⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜∃u⦁∀m⦁u m = ~(s m)⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜∀m⦁~ub ≤ u m ∧ u m ≤ ~lb ⌝ THEN1
	asm_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁~a ≤ ~b ⇔ b ≤ a⌝]);
a(DROP_NTH_ASM_T 3 discard_tac  THEN all_fc_tac[lim_sup_thm] THEN ∃_tac⌜~ lim_sup:ℝ⌝);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[
	pc_rule1"ℝ_lin_arith" prove_rule[]⌜
		∀a b c: ℝ⦁(~a + ~b < c  ⇔ ~c < a + b) ∧ (a + ~b < ~c ⇔ c <  ~a + b)⌝ ]);
pop_thm()
));

=TEX
The proof that Cauchy sequences converge is now straiightforward.
%%%%
%%%%
=SML

val ⦏cauchy_seq_lim_seq_thm ⦎ = save_thm ( "cauchy_seq_lim_seq_thm ", (
set_goal([], ⌜∀s⦁
	(∀e⦁ ℕℝ 0 < e ⇒∃n⦁∀k m⦁n ≤ k ∧ n ≤ m ⇒ Abs(s k - s m) < e)
⇒	∃x⦁ s -> x⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃lb ub⦁∀m⦁lb ≤ s m ∧ s m ≤ ub⌝ THEN1
	(all_fc_tac[cauchy_seq_bounded_below_thm] THEN
	∃_tac⌜b:ℝ⌝ THEN asm_rewrite_tac[ℝ_≤_def] THEN
	POP_ASM_T discard_tac THEN
	all_fc_tac[cauchy_seq_bounded_above_thm] THEN
	∃_tac⌜b:ℝ⌝ THEN asm_rewrite_tac[]));
a(all_fc_tac[lim_sup_thm] THEN ∃_tac⌜lim_sup:ℝ⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/3)*e⌝ THEN1 PC_T1"ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_asm_fc_tac[]);
a(DROP_NTH_ASM_T 7 discard_tac THEN ∃_tac⌜n + n'⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n ≤ m  ∧ n'  ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(DROP_NTH_ASM_T 6 (strip_asm_tac o ∀_elim⌜m⌝));
a(lemma_tac⌜n'  ≤ m'⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ Abs (s m' - s m) < (1 / 3) * e⌝ ante_tac
	THEN1 LIST_DROP_NTH_ASM_T [8] all_fc_tac);
a(cases_tac⌜ℕℝ 0 ≤ s m + ~ lim_sup⌝ THEN cases_tac ⌜ℕℝ 0 ≤ s m' + ~ (s m)⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_⇔_cauchy_seq_thm ⦎ = save_thm ( "lim_seq_⇔_cauchy_seq_thm ", (
set_goal([], ⌜∀s⦁
	(∃x⦁s -> x)
⇔	(∀e⦁ ℕℝ 0 < e ⇒∃n⦁∀k m⦁n ≤ k ∧ n ≤ m ⇒ Abs(s k - s m) < e)⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[lim_seq_cauchy_seq_thm]);
a(∃_tac⌜n⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(bc_thm_tac cauchy_seq_lim_seq_thm THEN POP_ASM_T accept_tac);
pop_thm()
));

=TEX
\subsection{Limits of Function Values}
We follow our earlier strategy of reducing problems about limits of function values
to limits of sequences:
%%%%
%%%%
=SML

val ⦏lim_fun_lim_seq_thm⦎ = save_thm ( "lim_fun_lim_seq_thm", (
set_goal([], ⌜∀f c x⦁
	(f --> c) x
⇔	(∀s⦁s -> x ∧ (∀m⦁¬s m = x) ⇒ (λm⦁f(s m)) -> c)⌝);
a(rewrite_tac[lim_fun_def, lim_seq_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(LIST_DROP_NTH_ASM_T [3, 5] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(lemma_tac⌜¬s m = x⌝ THEN1 asm_rewrite_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(contr_tac THEN strip_asm_tac(∀_elim⌜x⌝ lim_seq_¬_eq_thm));
a(lemma_tac⌜∃t⦁∀m⦁ Abs(t m + ~x) < Abs(s m + ~x) ∧¬t m = x ∧ ¬Abs(f(t m) + ~c) < e⌝
	THEN1 prove_∃_tac THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(lemma_tac⌜¬s m' = x⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜ℕℝ 0 < Abs(s m' +  ~x)⌝ THEN1
	(cases_tac⌜ℕℝ 0 ≤ s m' + ~x⌝ THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(spec_nth_asm_tac 5 ⌜Abs(s m'  + ~x)⌝);
a(∃_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 6 (ante_tac o ∀_elim⌜t⌝) THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 4 (fn th => all_fc_tac[rewrite_rule[lim_seq_def]th]));
a(∃_tac ⌜n⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜Abs(s m + ~x)⌝ THEN asm_rewrite_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "2.2.2" *** *)
a(∃_tac⌜e⌝ THEN REPEAT strip_tac);
a(∃_tac⌜n⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏const_lim_fun_thm⦎ = save_thm ( "const_lim_fun_thm", (
set_goal([], ⌜∀c t⦁ ((λx⦁c) --> c) t⌝);
a(rewrite_tac[lim_fun_lim_seq_thm, const_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏id_lim_fun_thm⦎ = save_thm ( "id_lim_fun_thm", (
set_goal([], ⌜∀t⦁ ((λx⦁x) --> t) t⌝);
a(rewrite_tac[lim_fun_lim_seq_thm, η_axiom] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_lim_fun_thm⦎ = save_thm ( "plus_lim_fun_thm", (
set_goal([], ⌜∀f1 t1 x f2 t2⦁
	(f1 --> t1) x
∧	 (f2 --> t2) x
⇒	((λx⦁f1 x + f2 x) --> t1 + t2) x⌝);
a(rewrite_tac[lim_fun_lim_seq_thm] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [plus_lim_seq_thm]);
a(rewrite_tac[] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_lim_fun_thm⦎ = save_thm ( "times_lim_fun_thm", (
set_goal([], ⌜∀f1 t1 x f2 t2⦁ (f1 --> t1) x ∧  (f2 --> t2) x ⇒ ((λx⦁f1 x * f2 x) --> t1 * t2) x⌝);
a(rewrite_tac[lim_fun_lim_seq_thm] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [times_lim_seq_thm]);
a(rewrite_tac[] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏recip_lim_fun_thm⦎ = save_thm ( "recip_lim_fun_thm", (
set_goal([], ⌜∀f t x⦁ (f --> t) x ∧  ¬t = ℕℝ 0 ⇒ ((λx⦁(f x) ⋏-⋏1) --> t ⋏-⋏1) x⌝);
a(rewrite_tac[lim_fun_lim_seq_thm] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [recip_lim_seq_thm]);
a(rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏comp_lim_fun_thm⦎ = save_thm ( "comp_lim_fun_thm", (
set_goal([], ⌜∀f t x g⦁ (f --> t) x ∧ (g Cts t)  ⇒ ((λx⦁g (f x)) --> g t ) x⌝);
a(rewrite_tac[lim_fun_lim_seq_thm] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [cts_lim_seq_thm]);
a(rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cts_lim_fun_thm⦎ = save_thm ( "cts_lim_fun_thm", (
set_goal([], ⌜∀f x⦁ (f Cts x)  ⇒ (f --> f x) x⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule[η_axiom]
	⌜(f --> f x) = ((λ x⦁ f ((λx⦁x)x)) --> f x)⌝]);
a(bc_thm_tac comp_lim_fun_thm);
a(asm_rewrite_tac[id_lim_fun_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏comp_lim_fun_thm1⦎ = save_thm ( "comp_lim_fun_thm1", (
set_goal([], ⌜∀f t x g⦁ (g --> t) (f x) ∧ (f Cts x) ∧ (∀y⦁ f y = f x ⇔ y = x)
	⇒ ((λx⦁g (f x)) -->  t) x⌝);
a(rewrite_tac[lim_fun_lim_seq_thm] THEN REPEAT strip_tac);
a(all_fc_tac[cts_lim_seq_thm1]);
a(lemma_tac⌜∀m⦁ ¬(λm⦁f(s m)) m = f x⌝ THEN1 asm_rewrite_tac[]);
a(ALL_ASM_FC_T  (MAP_EVERY ante_tac)[]);
a(rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏poly_lim_fun_thm⦎ = save_thm ( "poly_lim_fun_thm", (
set_goal([], ⌜∀f x⦁ f ∈ PolyFunc ⇒ (f --> f x) x⌝);
a(REPEAT strip_tac);
a(poly_induction_tac ⌜f⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[const_lim_fun_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[id_lim_fun_thm]);
(* *** Goal "3" *** *)
a(ALL_FC_T (MAP_EVERY ante_tac) [plus_lim_fun_thm]);
a(rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "4" *** *)
a(ALL_FC_T (MAP_EVERY ante_tac) [times_lim_fun_thm]);
a(rewrite_tac[] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_upper_bound_thm⦎ = save_thm ( "lim_fun_upper_bound_thm", (
set_goal([], ⌜∀u d c t x⦁
	ℕℝ 0 < d
∧	(∀y⦁Abs(y - x) <  d ∧ ¬y = x⇒ u y ≤  c) ∧ (u --> t) x
⇒	t ≤ c⌝);
a(rewrite_tac[lim_fun_lim_seq_thm] THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜d⌝](rewrite_rule[]lim_seq_¬_eq_thm1)));
a(bc_thm_tac lim_seq_upper_bound_thm);
 a(∃_tac⌜λm⦁u (s m)⌝ THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_unique_thm⦎ = save_thm ( "lim_fun_unique_thm", (
set_goal([], ⌜∀u s t x⦁ (u --> s) x ∧ (u --> t) x ⇒ s = t⌝);
a(rewrite_tac[lim_fun_def] THEN contr_tac);
a(lemma_tac⌜s < t ∨ t < s⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1" *** *)
a(lemma_tac⌜ℕℝ 0 < (1/2)*(t + ~s)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4, 5] all_fc_tac);
a(lemma_tac⌜∃d1⦁ℕℝ 0 < d1 ∧ ℕℝ 0 ≤ d1 ∧ d1 < d ∧ d1 < d'⌝ THEN1
	(cases_tac ⌜d ≤ d'⌝ THEN_LIST [∃_tac⌜(1/2)*d⌝, ∃_tac⌜(1/2)*d'⌝]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LIST_DROP_NTH_ASM_T [5, 7] (MAP_EVERY (ante_tac o ∀_elim⌜d1 + x⌝)));
a(asm_rewrite_tac[ℝ_plus_assoc_thm, ℝ_abs_def]);
a(cases_tac⌜ℕℝ 0 ≤ u (d1 + x) + ~ t⌝ THEN cases_tac ⌜ℕℝ 0 ≤ u (d1 + x) + ~ s⌝ THEN
	asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜ℕℝ 0 < (1/2)*(s + ~t)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4, 5] all_fc_tac);
a(lemma_tac⌜∃d1⦁ℕℝ 0 < d1 ∧ ℕℝ 0 ≤ d1 ∧ d1 < d ∧ d1 < d'⌝ THEN1
	(cases_tac ⌜d ≤ d'⌝ THEN_LIST [∃_tac⌜(1/2)*d⌝, ∃_tac⌜(1/2)*d'⌝]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LIST_DROP_NTH_ASM_T [5, 7] (MAP_EVERY (ante_tac o ∀_elim⌜d1 + x⌝)));
a(asm_rewrite_tac[ℝ_plus_assoc_thm, ℝ_abs_def]);
a(cases_tac⌜ℕℝ 0 ≤ u (d1 + x) + ~ t⌝ THEN cases_tac ⌜ℕℝ 0 ≤ u (d1 + x) + ~ s⌝ THEN
	asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_local_thm⦎ = save_thm ( "lim_fun_local_thm", (
set_goal([], ⌜∀u v s t x a b ⦁
	(u --> s) x
∧	a < x ∧ x < b
∧	(∀t⦁a < t ∧ t < b ∧ ¬t = x ⇒ u t = v t)
⇒	(v --> s) x⌝);
a(rewrite_tac[lim_fun_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(lemma_tac⌜∃d1⦁ℕℝ 0 < d1 ∧ d1 < x + ~a ∧ d1 < b + ~x ∧ d1 < d⌝ THEN1 
	(bc_thm_tac ℝ_bound_below_3_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜d1⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜a < y ∧ y < b⌝ THEN1
	(DROP_NTH_ASM_T 2 ante_tac THEN cases_tac⌜ℕℝ 0 ≤ y + ~x⌝
		THEN asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜Abs(y + ~x) < d⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [10] (ALL_FC_T (MAP_EVERY ante_tac)));
a(LIST_DROP_NTH_ASM_T [12] (ALL_FC_T rewrite_tac));
pop_thm()
));

=TEX
%%%%
%%%% A variant on {\em deriv\_lim\_fun\_thm} expressed in terms of reciprocals:
%%%%
=SML
set_goal([], ⌜∀ f c x⦁ (f Deriv c) x ⇔ ((λ y⦁ (f y - f x) * (y - x)⋏-⋏1) --> c) x⌝);
a(rewrite_tac[deriv_lim_fun_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac lim_fun_local_thm);
a(MAP_EVERY ∃_tac [⌜x + ℕℝ 1⌝, ⌜x + ~(ℕℝ 1)⌝,
	⌜λ y⦁ (f y + ~ (f x)) / (y + ~ x)⌝]
	THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
a(lemma_tac⌜¬t + ~x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac (fc_canon ℝ_over_times_recip_thm));
(* *** Goal "2" *** *)
a(bc_thm_tac lim_fun_local_thm);
a(MAP_EVERY ∃_tac [⌜x + ℕℝ 1⌝, ⌜x + ~(ℕℝ 1)⌝,
	⌜λ y⦁ (f y + ~ (f x)) * (y + ~ x)⋏-⋏1⌝]
	THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
a(lemma_tac⌜¬t + ~x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac (fc_canon ℝ_over_times_recip_thm));
val ⦏deriv_lim_fun_thm1⦎ = 
save_pop_thm"deriv_lim_fun_thm1";
=TEX

%%%%
%%%%
=SML

val ⦏comp_lim_fun_thm2⦎ = save_thm ( "comp_lim_fun_thm2", (
set_goal([], ⌜∀f a b t x g⦁
	x ∈ OpenInterval a b
∧	 (g --> t) (f x)
∧	(f Cts x)
∧	(∀y⦁ y ∈ OpenInterval a b ⇒ (f y = f x ⇔ y = x))
⇒	((λx⦁g (f x)) -->  t) x⌝);
a(rewrite_tac[open_interval_def] THEN REPEAT strip_tac THEN bc_thm_tac lim_fun_local_thm);
a(lemma_tac⌜∃h⦁(∀t⦁a < t ∧ t < b ⇒ h t = f t) ∧ (∀t⦁h t = h x ⇔ t = x)⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜λt⦁if a < t ∧ t < b then f t else f x + ℕℝ 1⌝ THEN rewrite_tac[] THEN
	REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a(POP_ASM_T ante_tac THEN cases_tac⌜a < t' ∧ t' < b⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(MAP_EVERY ∃_tac [⌜b⌝, ⌜a⌝, ⌜λx⦁g(h x)⌝]);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac comp_lim_fun_thm1 THEN asm_rewrite_tac[]);
a(ALL_ASM_FC_T asm_rewrite_tac[]);
a(bc_thm_tac cts_local_thm);
a(MAP_EVERY ∃_tac [⌜f⌝, ⌜b⌝, ⌜a⌝]);
a(REPEAT strip_tac);
a(ALL_ASM_FC_T rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX

The theorems on limits above have the following consequence concerning
the differentiability of an inverse function:
=TEX
%%%%
%%%%
=SML

val ⦏inverse_deriv_thm⦎ = save_thm ( "inverse_deriv_thm", (
set_goal([], ⌜∀f g a b x c⦁ 
	x ∈ OpenInterval a b
∧	(∀y⦁y ∈ OpenInterval a b ⇒ f(g y) = y)
∧	(f Deriv c) (g x)
∧	(g Cts x)
∧	¬c = ℕℝ 0
⇒	(g Deriv c ⋏-⋏1) x
⌝);
a(rewrite_tac[deriv_lim_fun_thm] THEN REPEAT strip_tac);
a(lemma_tac⌜∀ y⦁ y ∈ OpenInterval a b ⇒ (g y = g x ⇔ y = x)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜y = f(g y) ∧ x = f(g x)⌝ once_rewrite_thm_tac THEN1
	(REPEAT strip_tac THEN ALL_ASM_FC_T rewrite_tac[]));
a(POP_ASM_T rewrite_thm_tac);
(* *** Goal "2" *** *)
a(POP_ASM_T rewrite_thm_tac);
(* *** Goal "3" *** *)
a(all_fc_tac[comp_lim_fun_thm2]);
a(DROP_NTH_ASM_T 5 discard_tac);
a(all_fc_tac [recip_lim_fun_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[] THEN strip_tac);
a(bc_thm_tac lim_fun_local_thm);
a(MAP_EVERY ∃_tac [⌜b⌝, ⌜a⌝, ⌜(λ x'⦁ ((f (g x') + ~ (f (g x))) / (g x' + ~ (g x))) ⋏-⋏1)⌝]);
a(GET_NTH_ASM_T 7 (asm_rewrite_thm_tac o rewrite_rule[open_interval_def]));
a(REPEAT strip_tac);
a(lemma_tac⌜t ∈ OpenInterval a b⌝ THEN1 asm_rewrite_tac[open_interval_def]);
a(LIST_GET_NTH_ASM_T [10] (ALL_FC_T rewrite_tac));
a(lemma_tac⌜¬g t = g x⌝);
(* *** Goal "3.1" *** *)
a(swap_nth_asm_concl_tac 2);
a(LEMMA_T⌜f(g t) = f(g x)⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(LIST_GET_NTH_ASM_T [10] (ALL_FC_T rewrite_tac));
(* *** Goal "3.2" *** *)
a(lemma_tac⌜¬t + ~x = ℕℝ 0 ∧ ¬g t + ~(g x) = ℕℝ 0⌝ THEN1
	PC_T1 "ℝ_lin_arith"asm_prove_tac[]);
a(all_fc_tac[ℝ_¬_recip_0_thm]);
a(rename_tac[(⌜x⌝, "X")] THEN
	ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm, ℝ_recip_clauses]);
a(conv_tac(LEFT_C (once_rewrite_conv[ℝ_times_comm_thm])) THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Uniform Convergence}
%%%%
%%%%
%%%%
%%%%
We now prove some basic facts about limits of locally uniformly convergent
sequences of functions.

Firstly, constant sequences are uniformly convergent at $x$ on any
iset $X$
%%%%
%%%%
=SML

val ⦏const_unif_lim_seq_thm⦎ = save_thm ( "const_unif_lim_seq_thm", (
set_goal([], ⌜∀h X⦁ ((λm⦁ h) ---> h) X⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[unif_lim_seq_def]);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
If two uniformly convergent
sequences of functions each have a limit, then so does their
sum and its limit is the sum of the limits.
Thee proof is a cut-and-paste generalisation of the analogous proof
for the limit of sequences of numbers.
%%%%
%%%%
=SML

val ⦏plus_unif_lim_seq_thm⦎ = save_thm ( "plus_unif_lim_seq_thm", (
set_goal([], ⌜∀u1 h1 X u2 h2⦁
	(u1 ---> h1) X
∧	(u2 ---> h2) X
⇒	((λm y⦁u1 m y + u2 m y) ---> (λy⦁h1 y + h2 y)) X⌝);
a(rewrite_tac[unif_lim_seq_def] THEN REPEAT strip_tac);
a(lemma_tac ⌜ℕℝ 0 < e / ℕℝ 2 ⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 4 ⌜e / ℕℝ 2⌝ THEN spec_nth_asm_tac 4  ⌜e / ℕℝ 2⌝);
a(∃_tac⌜n + n'⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n ≤ m ∧ n' ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_GET_NTH_ASM_T [5, 6] all_fc_tac);
a(LEMMA_T ⌜
	(u1 m y + u2 m y) + ~(h1 y) + ~(h2 y) =
	(u1 m y + ~(h1 y)) + (u2 m y + ~(h2 y))⌝
	rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac ℝ_≤_less_trans_thm);
a(∃_tac⌜Abs (u1 m y + ~ (h1 y)) + Abs (u2 m y + ~(h2 y))⌝ THEN rewrite_tac[ℝ_abs_plus_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
We now want to give the analogous result on the product of two bounded sequences
of functions with uniform limits. Some preparation is required.
It is useful to know that the limit of a uniformly convergent and bounded sequence of functions
is itself bounded: 
%%%%
%%%%
=SML

val ⦏bounded_unif_limit_thm⦎ = save_thm ( "bounded_unif_limit_thm", (
set_goal([], ⌜∀u g X c⦁
	(u ---> g)  X
∧	(∀y m⦁y ∈ X ⇒ Abs(u m y) < c)
⇒	(∃d⦁ ∀y⦁y ∈ X ⇒ Abs(g y) < d)⌝);
a(rewrite_tac[unif_lim_seq_def] THEN REPEAT strip_tac);
a(cases_tac⌜X = {}⌝ THEN1 asm_rewrite_tac[]);
a(POP_ASM_T (PC_T1 "sets_ext1" strip_asm_tac));
a(lemma_tac⌜ℕℝ 0 < c⌝ THEN1
	(DROP_NTH_ASM_T 2 (ante_tac o list_∀_elim[⌜x⌝, ⌜m:ℕ⌝]) THEN
	asm_rewrite_tac[ℝ_≤_def] THEN strip_asm_tac (∀_elim⌜u m x⌝ℝ_0_≤_abs_thm)
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(DROP_NTH_ASM_T 2 discard_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜ℕℝ 2*c⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[] o ∀_elim⌜n⌝));
a(LIST_DROP_NTH_ASM_T [1, 4] all_fc_tac);
a(DROP_NTH_ASM_T 1 (strip_asm_tac o ∀_elim⌜n⌝));
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜ Abs( ~(u n y + ~ (g y)) + u n y )⌝);
a(strip_tac THEN1 (conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac));
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜ Abs( ~(u n y + ~ (g y)) ) + Abs(u n y)⌝);
a(rewrite_tac[ℝ_abs_plus_thm, ℝ_abs_minus_thm]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
We now want to give the analogous result on the product of two sequences
of functions with uniform limits.  We need two algebraic lemmas:
%%%%
%%%%
=SML
set_goal([], ⌜∀U G V H D B E C:ℝ⦁
	Abs(U + ~G) < D ∧ Abs(U + G) < B
∧	Abs(V + ~H) < E ∧ Abs(V + H) < C
⇒	Abs(U*V + ~(G*H)) < (1/2)*(B * E + C * D)
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜U*V + ~(G*H) = (1/2)*((U + G)*(V + ~H) + (V + H)*(U + ~G))⌝
	rewrite_thm_tac THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(rewrite_tac[ℝ_abs_times_thm,
	pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b⦁ (1/2)*a < (1/2)*b ⇔ a < b⌝]);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN
	∃_tac⌜Abs ((U + G) * (V + ~ H)) + Abs((V + H) * (U + ~ G))⌝
	THEN rewrite_tac[ℝ_abs_plus_thm, ℝ_abs_times_thm]);
a(bc_thm_tac (pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b x y:ℝ⦁ a < b ∧ x < y ⇒ a + x < b + y⌝));
a(ALL_FC_T rewrite_tac[ℝ_abs_less_times_thm]);
val ⦏times_unif_lemma1⦎ = pop_thm();
=TEX

%%%%
%%%%
=SML
set_goal([], ⌜∀B C  e⦁
	ℕℝ 0 < B ∧ ℕℝ 0 <  C ∧ ℕℝ 0 <  e
⇒	∃D E⦁ ℕℝ 0 < D ∧ ℕℝ 0 < E ∧ (1/2)*(B * E + C * D) < e
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (B + C)⋏-⋏1⌝ THEN1
	(bc_thm_tac ℝ_0_less_0_less_recip_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ 0 < e * (B + C)⋏-⋏1⌝ THEN1
	(bc_thm_tac ℝ_0_less_0_less_times_thm THEN REPEAT strip_tac));
a(REPEAT_N 2 (∃_tac⌜e*((B + C)⋏-⋏1)⌝) THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[] ⌜∀a b c d:ℝ⦁c*(a*b) + d*(a*b) = a*b*(c + d)⌝]);
a(lemma_tac⌜¬B + C = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏times_unif_lemma2⦎ = pop_thm();
=TEX
We now give result on the product of two sequences of functions with uniform limits. 
%%%%
%%%%
=SML

val ⦏times_unif_lim_seq_thm⦎ = save_thm ( "times_unif_lim_seq_thm", (
set_goal([], ⌜∀u g v h X c d⦁
	(u ---> g)  X
∧	(v ---> h)  X
∧	(∀y m⦁ y ∈ X ⇒ Abs(u m y) < c)
∧	(∀y m⦁ y ∈ X ⇒ Abs(v m y) < d)
⇒	((λm y⦁u m y*v m y) ---> (λy⦁g y*h y)) X⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃B⦁∀y m⦁ y ∈ X ⇒ Abs(u m y + g y) < B⌝);
(* *** Goal "1" *** *)
a(all_fc_tac[bounded_unif_limit_thm]);
a(∃_tac⌜c + d''⌝ THEN REPEAT strip_tac THEN
	bc_thm_tac ℝ_≤_less_trans_thm THEN
	∃_tac⌜Abs(u m y) + Abs(g y)⌝ THEN rewrite_tac[ℝ_abs_plus_thm]);
a(bc_thm_tac (pc_rule1"ℝ_lin_arith" prove_rule[] ⌜∀a b x y:ℝ⦁ a < b ∧ x < y ⇒ a + x < b + y⌝));
a(LIST_GET_NTH_ASM_T [2, 5] (ALL_FC_T rewrite_tac));
(* *** Goal "2" *** *)
a(lemma_tac⌜∃C⦁∀y m⦁y ∈ X ⇒ Abs(v m y + h y) < C⌝);
(* *** Goal "2.1" *** *)
a(all_fc_tac[bounded_unif_limit_thm]);
a(∃_tac⌜d + d'⌝ THEN REPEAT strip_tac THEN
	bc_thm_tac ℝ_≤_less_trans_thm THEN
	∃_tac⌜Abs(v m y) + Abs(h y)⌝ THEN rewrite_tac[ℝ_abs_plus_thm]);
a(bc_thm_tac (pc_rule1"ℝ_lin_arith" prove_rule[] ⌜∀a b x y:ℝ⦁ a < b ∧ x < y ⇒ a + x < b + y⌝));
a(LIST_GET_NTH_ASM_T [3, 5] (ALL_FC_T rewrite_tac));
(* *** Goal "2.2" *** *)
a(LIST_DROP_NTH_ASM_T [5, 6] (MAP_EVERY ante_tac));
a(rewrite_tac[unif_lim_seq_def] THEN REPEAT strip_tac);
a(cases_tac⌜X = {}⌝ THEN1 asm_rewrite_tac[]);
a(POP_ASM_T (PC_T1 "sets_ext1" strip_asm_tac));
a(lemma_tac⌜ℕℝ 0 < B⌝ THEN1
	(DROP_NTH_ASM_T 6 (ante_tac o list_∀_elim[⌜x⌝, ⌜m:ℕ⌝]) THEN
	asm_rewrite_tac[ℝ_≤_def] THEN
	strip_asm_tac (∀_elim⌜u m x + g x⌝ℝ_0_≤_abs_thm) THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ 0 < C⌝ THEN1
	(DROP_NTH_ASM_T 6 (ante_tac o list_∀_elim[⌜x⌝, ⌜m:ℕ⌝]) THEN
	asm_rewrite_tac[ℝ_≤_def] THEN
	strip_asm_tac (∀_elim⌜v m x + h x⌝ℝ_0_≤_abs_thm) THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(DROP_NTH_ASM_T 3 discard_tac);
a(lemma_tac⌜∃D E⦁ ℕℝ 0 < D ∧ ℕℝ 0 < E ∧ (1/2)*(B * E + C * D) < e⌝ THEN1
	(bc_thm_tac times_unif_lemma2 THEN REPEAT strip_tac));
a(DROP_NTH_ASM_T 8 (strip_asm_tac o ∀_elim⌜D⌝));
a(DROP_NTH_ASM_T 8 (strip_asm_tac o ∀_elim⌜E⌝));
a(∃_tac⌜n+n'⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜1 / 2 * (B * E + C * D)⌝
	THEN REPEAT strip_tac);
a(lemma_tac⌜n ≤ m ∧ n' ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(bc_thm_tac times_unif_lemma1 THEN REPEAT strip_tac THEN  all_asm_fc_tac[]
	THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
Now we show that a sequence of functions converging uniformly on a closed interval
with a continuous limit is uniformly bounded:
%%%%
%%%%
=SML

val ⦏unif_lim_seq_bounded_thm⦎ = save_thm ( "unif_lim_seq_bounded_thm", (
set_goal([], ⌜∀u h a b⦁
	a < b
∧	(u ---> h)  (ClosedInterval a b)
∧	(∀y⦁a ≤ y ∧ y ≤ b ⇒ h Cts y)
⇒	(∃c n⦁∀m y⦁n ≤ m ∧ a ≤ y ∧ y ≤ b ⇒ Abs(u m y) < c)⌝);
a(rewrite_tac[unif_lim_seq_def, closed_interval_def] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T  2 (strip_asm_tac o ∀_elim⌜ℕℝ 1⌝));
a(lemma_tac⌜a ≤ b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[cts_abs_bounded_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ c⌝ THEN1
	(SPEC_NTH_ASM_T 1 ⌜a⌝ ante_tac THEN
	strip_asm_tac(∀_elim⌜h a⌝ℝ_0_≤_abs_thm) THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜ℕℝ 1 + c⌝ THEN ∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜u m y + ~(h y)⌝, ⌜h y⌝] ℝ_abs_plus_thm));
a(rewrite_tac[ℝ_plus_assoc_thm] THEN strip_tac);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜Abs (u m y + ~ (h y)) + Abs (h y)⌝
	THEN REPEAT strip_tac);
a(all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Now we show that a sequence of functions converging uniformly on a closed interval
with a continuous limit is uniformly bounded:
%%%%
%%%%
=SML

val ⦏unif_lim_seq_⊆_thm⦎ = save_thm ( "unif_lim_seq_⊆_thm", (
set_goal([], ⌜∀u h X Y⦁
	(u ---> h)  X
∧	Y ⊆ X
⇒	(u ---> h) Y⌝);
a(rewrite_tac[unif_lim_seq_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(all_asm_fc_tac[] THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
The following ``shift theorem'' is analogous to the one for sequences of terms:
%%%%
%%%%
=SML

val ⦏unif_lim_seq_shift_thm⦎ = save_thm ( "unif_lim_seq_shift_thm", (
set_goal([], ⌜∀m u h X ⦁ (u ---> h) X ⇔ ((λn⦁u (n + m)) --->h) X⌝);
a(rewrite_tac[unif_lim_seq_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[] THEN ∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜n ≤ m'+m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[] THEN ∃_tac⌜n + m⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[≤_def]) THEN all_var_elim_asm_tac1);
a(SPEC_NTH_ASM_T 2 ⌜n+i⌝ ante_tac THEN
	conv_tac (ONCE_MAP_C anf_conv) THEN
	REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
Now one of the main results of this section: if a sequence
of functions, all continuous at some point $x$, is uniformly convergent in an open interval containing $x$
at $x$, then the limit function is continuous at $x$.
We prove a little lemma first:
%%%%
%%%%
=SML
set_goal([], ⌜∀a b c d:ℝ⦁Abs(a - d) ≤ Abs(a - b) + Abs(b - c) + Abs(c - d)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜Abs(b - d) ≤ Abs(b - c) + Abs(c - d)⌝ THEN1
	(pure_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
		⌜b - d = (b - c) + (c - d)⌝, ℝ_abs_plus_thm]));
a(lemma_tac⌜Abs(a - d) ≤ Abs(a - b) + Abs(b - d)⌝ THEN1
	(pure_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
		⌜a - d = (a - b) + (b - d)⌝, ℝ_abs_plus_thm]));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏abs_abcd_thm⦎ = pop_thm ();
=TEX
Now we prove the main result on the continuity of limits of sequences of
functions. We use
the $\epsilon$-$\delta$ definition of continuity directly --- to use
the alternative characterisation in terms of sequences involves too
many subscripts for comfort!
%%%%
%%%%
=SML

val ⦏unif_lim_seq_cts_thm⦎ = save_thm ( "unif_lim_seq_cts_thm", (
set_goal([], ⌜∀u h x a b⦁
	(u ---> h) (OpenInterval a b) ∧ a < x ∧ x < b ∧ (∀m⦁u m Cts x) ⇒ h Cts x⌝);
a(rewrite_tac[cts_def, unif_lim_seq_def, lim_seq_def, open_interval_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/3)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 6 ⌜(1/3)*e⌝);
a(SPEC_NTH_ASM_T 1 ⌜n⌝ ante_tac THEN rewrite_tac[] THEN REPEAT strip_tac);
a(list_spec_nth_asm_tac 5 [⌜n⌝, ⌜(1/3)*e⌝]);
a(strip_asm_tac(list_∀_elim[⌜a⌝, ⌜x⌝, ⌜b⌝, ⌜d⌝]axbd_thm));
a(∃_tac⌜c⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac ⌜
	Abs(h y - u n y) + Abs(u n y - u n x) + Abs(u n x - h x)⌝
	THEN rewrite_tac[rewrite_rule[]abs_abcd_thm] THEN REPEAT strip_tac);
a(lemma_tac ⌜Abs(h y + ~(u n y)) < (1/3)*e
	∧ Abs(u n y + ~(u n x)) < (1/3)*e
	∧ Abs(u n x + ~(h x)) < (1/3)*e⌝
	THEN_LIST [id_tac, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(pure_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀z⦁h y + ~z = ~(z + ~(h y))⌝,
	ℝ_abs_minus_thm]);
a(GET_NTH_ASM_T 7 bc_thm_tac);
a(LIST_GET_NTH_ASM_T [2] (ALL_FC_T rewrite_tac));
(* *** Goal "2" *** *)
a(GET_NTH_ASM_T 5 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(GET_NTH_ASM_T 7 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Any uniformly convergent sequence of functions is a Cauchy sequence:
%%%%
%%%%
=SML

val ⦏unif_lim_seq_cauchy_seq_thm ⦎ = save_thm ( "unif_lim_seq_cauchy_seq_thm ", (
set_goal([], ⌜∀u f X⦁
	(u ---> f) X
⇒	∀e⦁ ℕℝ 0 < e ⇒∃n⦁∀k m⦁n ≤ k ∧ n ≤ m ⇒ ∀y⦁y ∈ X ⇒ Abs(u k y - u m y) < e⌝);
a(rewrite_tac[unif_lim_seq_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_asm_fc_tac[]);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 6 discard_tac THEN all_asm_fc_tac[]);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜Abs(u k y + ~(f y)) + Abs(~(u m y + ~(f y)))⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ℝ_abs_plus_bc_thm);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (rewrite_tac[ℝ_abs_minus_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Uniform Cauchy sequences of functions converge uniformly. This is a bit easier than
the equivalent result for numeric sequences, because that result is now available to give
us the pointwise limit functon with little extra work. We just then have to show that
the uniform Cauchy condition implies that the convergence to the point-wise limit is uniform.
%%%%
%%%%
=SML

val ⦏cauchy_seq_unif_lim_seq_thm ⦎ = save_thm ( "cauchy_seq_unif_lim_seq_thm ", (
set_goal([], ⌜∀u X⦁
	(∀e⦁ ℕℝ 0 < e ⇒∃n⦁∀k m⦁n ≤ k ∧ n ≤ m ⇒ ∀y⦁ y ∈ X ⇒ Abs(u k y - u m y) < e)
⇒	∃f⦁(u ---> f) X⌝);
a(rewrite_tac[unif_lim_seq_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∃f⦁∀y⦁ y ∈ X ⇒ (λm⦁u m y) -> f y⌝ THEN1 prove_∃_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(cases_tac⌜y' ∈ X⌝ THEN asm_rewrite_tac[]);
a(bc_thm_tac cauchy_seq_lim_seq_thm THEN REPEAT strip_tac THEN rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜f⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [2, 4] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [5] (ALL_FC_T (MAP_EVERY ante_tac)));
a(rewrite_tac[lim_seq_def] THEN STRIP_T (fn th => all_fc_tac[th]));
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜n' + m⌝));
a(lemma_tac ⌜Abs (u m y + ~ (u (n'+m) y)) < 1 / 2 * e⌝);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 4 (ante_tac o list_∀_elim[⌜m⌝, ⌜n'+m⌝]));
a(LEMMA_T ⌜n ≤ n' + m⌝ asm_rewrite_thm_tac THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(STRIP_T (strip_asm_tac o ∀_elim⌜y⌝));
(* *** Goal "2.2" *** *)
a(bc_thm_tac ℝ_≤_less_trans_thm THEN
	∃_tac⌜Abs (u m y + ~ (u (n' + m) y)) + Abs (u (n' + m) y + ~ (f y))⌝);
a(REPEAT strip_tac THEN_LIST
	[bc_thm_tac ℝ_≤_trans_thm, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(∃_tac⌜Abs ((u m y + ~ (u (n' + m) y)) + (u (n' + m) y + ~ (f y)))⌝
	THEN rewrite_tac[ℝ_abs_plus_thm]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏unif_lim_seq_pointwise_lim_seq_thm⦎ = save_thm ( "unif_lim_seq_pointwise_lim_seq_thm", (
set_goal([], ⌜∀u f X x⦁
	(u ---> f) X
∧	x ∈ X
⇒	(λm⦁u m x) -> f x⌝);
a(rewrite_tac[unif_lim_seq_def, lim_seq_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏unif_lim_seq_pointwise_unique_thm⦎ = save_thm ( "unif_lim_seq_pointwise_unique_thm", (
set_goal([], ⌜∀u f g X x c⦁
	(u ---> f) X
∧	x ∈ X
∧	(λm⦁ u m x) -> c
⇒	f x = c⌝);
a(REPEAT strip_tac THEN all_fc_tac[unif_lim_seq_pointwise_lim_seq_thm]);
a(all_fc_tac[lim_seq_unique_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏unif_lim_seq_unique_thm ⦎ = save_thm ( "unif_lim_seq_unique_thm ", (
set_goal([], ⌜∀u f g X x⦁
	(u ---> f) X
∧	(u ---> g) X
∧	x ∈ X
⇒	f x = g x⌝);
a(REPEAT strip_tac THEN all_fc_tac[unif_lim_seq_pointwise_lim_seq_thm]);
a(all_fc_tac[lim_seq_unique_thm]);
pop_thm()
));

=TEX
The following is theorem 7.11 from Rudin \cite{Rudin76} (p. 149) which says if a sequence
of functions $u_m$ converges uniformly to a limit $f$ on some set $E$ and
if $x$ is a limit point of $E$ such that $u_m(y)$ tends to some limiit
$s_m$ for each $m$ as $y$ tends to $x$, then the sequence $s_m$ 
converges to a limit $c$ and $f(y)$ tends to $c$ as $y$ tends to $x$.
I.e., under the given hypotheses, the operations of taking limits as $y$
tends to $x$ and taking limits as $m$ tends to infinity can be interchanged.

We do the special case where $E$ is the set obtained by deleting $x$ from
an open interval containing $x$, which is expected to be the most important
one in applications --- it certainly suffices for the theorem about differentiability
of limits that is Rudin's theorem 7.17. 

%%%%
%%%%
=SML

val ⦏lim_fun_lim_seq_interchange_thm⦎ = save_thm ( "lim_fun_lim_seq_interchange_thm", (
set_goal([], ⌜∀u f a b x s⦁
	(u ---> f) (OpenInterval a b \ {x})
∧	a < x ∧ x < b
∧	(∀m⦁ (u m --> s m) x)
⇒	∃c⦁ (f --> c) x ∧ s -> c
⌝);
a(REPEAT strip_tac THEN lemma_tac⌜∃c⦁s -> c⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[lim_seq_⇔_cauchy_seq_thm] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_fc_tac[unif_lim_seq_cauchy_seq_thm]);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o
	pc_rule1 "sets_ext1" rewrite_rule[open_interval_def] o list_∀_elim[⌜k⌝, ⌜m⌝]));
a(lemma_tac⌜((λz⦁~(u m z)) -->  ~(s m)) x⌝ THEN1
	(bc_thm_tac comp_lim_fun_thm
	THEN asm_rewrite_tac[minus_cts_thm]));
a(lemma_tac⌜((λz⦁ (λz⦁u k z) z + (λz⦁~(u m z)) z) -->  s k + ~(s m)) x⌝ THEN1
	(bc_thm_tac plus_lim_fun_thm
	THEN asm_rewrite_tac[η_axiom]));
a(LEMMA_T⌜( (λz⦁Abs((λz⦁ (λz⦁u k z) z + (λz⦁~(u m z)) z)z)) -->  Abs(s k + ~(s m)) ) x⌝
	ante_tac THEN1
	(bc_thm_tac comp_lim_fun_thm
	THEN asm_rewrite_tac[abs_cts_thm]));
a(rewrite_tac[] THEN strip_tac THEN all_fc_tac[axbd_thm]);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜(1/2)*e⌝ THEN REPEAT strip_tac
	THEN_LIST[id_tac, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(bc_thm_tac lim_fun_upper_bound_thm);
a(∃_tac⌜λ z⦁ Abs (u k z + ~ (u m z))⌝ THEN ∃_tac⌜x⌝ THEN ∃_tac⌜c⌝);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(rewrite_tac[ℝ_≤_def] THEN ∨_left_tac);
a(lemma_tac⌜y < x ∨ x < y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.1" *** *)
a(DROP_NTH_ASM_T 10 (bc_thm_tac o rewrite_rule[]));
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 10 (bc_thm_tac o rewrite_rule[]));
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(∃_tac⌜c⌝ THEN asm_rewrite_tac[lim_fun_def] THEN REPEAT strip_tac);
a(POP_ASM_T (fn th => lemma_tac⌜ℕℝ 0 < (1/3)*e⌝ THEN1
	(ante_tac th THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[])));
a(DROP_NTH_ASM_T 6 (fn th => all_fc_tac
	[pc_rule1"sets_ext1" rewrite_rule[unif_lim_seq_def, open_interval_def]th]));
a(DROP_NTH_ASM_T 3 (fn th => all_fc_tac[rewrite_rule[lim_seq_def]th]));
a(DROP_NTH_ASM_T 4 (fn th => all_fc_tac[rewrite_rule[lim_fun_def](∀_elim⌜n'⌝th)]));
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜n+n'⌝));
a(DROP_NTH_ASM_T 5 discard_tac THEN all_fc_tac[axbd_thm]);
a(∃_tac⌜c'⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac ⌜
	Abs(f y - u  (n+n') y) + Abs(u (n+n') y - s (n+n')) + Abs(s(n+n') - c)⌝
	THEN rewrite_tac[rewrite_rule[]abs_abcd_thm] THEN REPEAT strip_tac);
a(lemma_tac ⌜Abs(f y + ~(u (n+n') y)) < (1/3)*e
	∧ Abs(u (n+n') y + ~(s(n+n'))) < (1/3)*e
	∧ Abs(s(n+n') + ~c) < (1/3)*e⌝
	THEN_LIST [id_tac, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LEMMA_T ⌜f y + ~ (u (n + n' ) y) =~ ((u (n + n') y) + ~(f y))⌝
	(fn th => pure_rewrite_tac[th, ℝ_abs_minus_thm]) THEN1
	PC_T1 "ℝ_lin_arith" prove_tac[]);
a(lemma_tac⌜y < x ∨ x < y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.1" *** *)
a(DROP_NTH_ASM_T 10 (bc_thm_tac o rewrite_rule[]));
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac THEN REPEAT strip_tac);
(* *** Goal "2.1.2" *** *)
a(DROP_NTH_ASM_T 10 (bc_thm_tac o rewrite_rule[]));
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 6 bc_thm_tac THEN REPEAT strip_tac);
a(PC_T1"ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.3" *** *)
a(DROP_NTH_ASM_T 8 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
We now embark on our variant of theorem 7.17 from Rudin (p. 152)
which says that if the derivatives of a sequence of differentiable functtions
converge uniformly in an interval and if the values of the sequence of functions
converges at some point in the interval then the sequence of functions converges
uniformly in the interval and the derivative of the limit is the limit of the derivatives.
Since our notions of continuity etc. are two-sided, we prove the theorem for
an open interval rather than a closed one. This is not expected to make much
difference in typical applications.
%%%%
%%%%
=SML

val ⦏unif_lim_seq_deriv_estimate_thm⦎ = save_thm ( "unif_lim_seq_deriv_estimate_thm", (
set_goal([], ⌜∀du df x0 y0 A B u e ⦁
	(du ---> df) (OpenInterval A B)
∧	(∀y m⦁ A < y ∧ y < B ⇒ (u m Deriv du m y) y)
∧	A < x0 ∧ x0 < B
∧	((λm⦁ u m x0) ->  y0)
∧	ℕℝ 0 < e
⇒	∃N⦁ 	∀n m x t⦁ N ≤ n ∧ N ≤ m ∧ A < x ∧ x < B ∧ A < t ∧ t < B
	⇒	Abs(u n t + ~ (u m t) + ~(u n x) + u m x) ≤ Abs(t + ~x)*e
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac ⌜
	∀e⦁ ℕℝ 0 < e ⇒ ∃N⦁ ∀n m x t⦁ N ≤ n ∧ N ≤ m ∧ A < x ∧ x < t ∧ t < B ⇒
		Abs(u n t + ~ (u m t) + ~(u n x) + u m x) ≤ (t + ~x)*e
⌝);
(* *** Goal "1" *** *)
a(POP_ASM_T discard_tac);
a(REPEAT strip_tac THEN all_fc_tac[unif_lim_seq_cauchy_seq_thm]);
a(POP_ASM_T (strip_asm_tac o pc_rule1 "sets_ext1" rewrite_rule[open_interval_def]));
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜∀r⦁ x ≤ r ∧ r ≤ t ⇒
	((λw⦁u n' w + ~(u m w)) Deriv
		(λs⦁du n' s + ~(du m s)) r) r⌝
	THEN1 (REPEAT strip_tac THEN rewrite_tac[]
	THEN (lemma_tac⌜A < r ∧ r < B⌝
		THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[])
	THEN RAT_DERIV_T ante_tac
	THEN rewrite_tac[] THEN STRIP_T (ante_tac o list_∀_elim[⌜du n' r⌝, ⌜du m r⌝])
	THEN conv_tac (ONCE_MAP_C ℝ_anf_conv)
	THEN ALL_ASM_FC_T rewrite_tac[]));
a(LEMMA_T⌜∃ z⦁
		x < z ∧ z < t
	∧	(λw⦁u n' w + ~(u m w)) t + ~ ((λw⦁u n' w + ~(u m w)) x)
		= (t + ~ x) * ((λs⦁du n' s + ~(du m s)) z)
⌝ (strip_asm_tac o rewrite_rule[]) THEN1 bc_thm_tac (rewrite_rule[]mean_value_thm1));
(* *** Goal "1.1" *** *)
a(pure_asm_rewrite_tac[] THEN rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(POP_ASM_T (rewrite_thm_tac o rewrite_rule[ℝ_plus_assoc_thm]));
a(LEMMA_T⌜ℕℝ 0 ≤ t + ~ x⌝
	(fn th => rewrite_tac[ℝ_abs_times_thm, th, ∀_elim⌜t + ~x⌝ ℝ_abs_def])
	THEN1  PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(once_rewrite_tac[ℝ_≤_0_≤_thm]);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b c:ℝ⦁a*b + ~(a*c) = a* (b + ~c)⌝]);
a(bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜Abs (du n' z + ~ (du m z)) < e ⌝
	(fn th => ante_tac th  THEN  PC_T1 "ℝ_lin_arith"  prove_tac[]));
a(lemma_tac ⌜A < z ∧ z < B⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_GET_NTH_ASM_T [11] (all_fc_tac o map (rewrite_rule[])));
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(∃_tac⌜N⌝ THEN REPEAT strip_tac);
a(strip_asm_tac (list_∀_elim[⌜x⌝, ⌜t⌝]ℝ_less_cases_thm));
(* *** Goal "2.1" *** *)
a(LEMMA_T ⌜ℕℝ 0 ≤ t + ~x⌝ (fn th => conv_tac(RIGHT_C (rewrite_conv[th, ℝ_abs_def])))
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [8] all_fc_tac);
(* *** Goal "2.2" *** *)
a(all_var_elim_asm_tac THEN conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN rewrite_tac[]);
(* *** Goal "2.3" *** *)
a(pure_rewrite_tac[
	pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜
		u n t + ~ (u m t) + ~ (u n x) + u m x
	=	~ (u n x + ~ (u m x) + ~ (u n t) + u m t)
	∧	t + ~x = ~(x + ~t)⌝,
	ℝ_abs_minus_thm]);
a(LEMMA_T ⌜ℕℝ 0 ≤ x + ~t⌝ (fn th => conv_tac(RIGHT_C (rewrite_conv[th, ℝ_abs_def])))
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 8 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX

%%%%
%%%%
=SML
set_goal([], ⌜∀du df x0 y0 A B u ⦁
	(du ---> df) (OpenInterval A B)
∧	(∀y m⦁ A < y ∧ y < B ⇒ (u m Deriv du m y) y)
∧	A <  x0 ∧ x0 < B
∧	((λm⦁ u m x0) ->  y0)
⇒	∃f⦁ (u ---> f)  (OpenInterval A B)
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac cauchy_seq_unif_lim_seq_thm THEN REPEAT strip_tac);
a(PC_T1"sets_ext1" rewrite_tac[open_interval_def]);
a(LEMMA_T⌜ℕℝ 0 < (1/2)*e⌝
	(fn th => POP_ASM_T discard_tac THEN strip_asm_tac th
	THEN all_fc_tac[lim_seq_cauchy_seq_thm]
	THEN POP_ASM_T (strip_asm_tac o rewrite_rule[]))
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ℕℝ 0 < (1/2)*e*(B + ~A)⋏-⋏1⌝
	(fn th => DROP_NTH_ASM_T 2 discard_tac THEN strip_asm_tac th
	THEN all_fc_tac[unif_lim_seq_deriv_estimate_thm]));
(* *** Goal "1" *** *)
a(REPEAT (bc_thm_tac ℝ_0_less_0_less_times_thm THEN REPEAT strip_tac)
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_0_less_0_less_recip_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜n + N⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜
	Abs(u k x0 + ~(u m x0)) + Abs(u k y + ~(u m y) + ~(u k x0) + u m x0)⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[] THEN bc_thm_tac  ℝ_≤_trans_thm THEN
	∃_tac⌜Abs((u k x0 + ~(u m x0)) + (u k y + ~(u m y) + ~(u k x0) + u m x0))⌝);
a(rewrite_tac[ℝ_abs_plus_thm]);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜e = (1/2)*e + (1/2)*e⌝]
	THEN bc_thm_tac ℝ_plus_mono_thm2 THEN REPEAT strip_tac
	THEN1 (GET_NTH_ASM_T 7 bc_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(lemma_tac⌜N ≤ k ∧ N ≤ m⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_≤_less_trans_thm);
a(∃_tac⌜Abs (y + ~ x0) * 1 / 2 * e * (B + ~ A) ⋏-⋏1⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 7 bc_thm_tac);
a(REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal ".2.2.2" *** *)
a(pure_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁x * (1/2) * e * y = ((1/2)*e) * x * y⌝]);
a(pure_once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁x<  y ⇔ x < y * ℕℝ 1⌝]);
a(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
(* *** Goal ".2.2.2.1" *** *)
a(bc_thm_tac ℝ_≤_less_trans_thm);
a(∃_tac ⌜Abs(u n x0 + ~(u n x0))⌝ THEN pure_rewrite_tac [ℝ_0_≤_abs_thm]);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 9 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.2.2.2" *** *)
a(lemma_tac ⌜¬B + ~A  = ℕℝ 0 ∧ ℕℝ 0 < B + ~A⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[∀_elim⌜B + ~A⌝ ℝ_times_mono_⇔_thm]);
a(pure_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x y⦁(B + ~A)*x *y = x*y*(B + ~A)⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(cases_tac⌜ℕℝ 0 ≤ y + ~x0⌝ THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏unif_lim_seq_deriv_lemma⦎ = pop_thm();
=TEX

Now the main theorem.
(For historical reasons the proof works with a mixture of statements about
membership of open intervals and explicit inequalities; the fiddling around
in the first three tactic applications puts the goal in the form expected by
the rest of the proof.)
%%%%
%%%%
=SML

val ⦏unif_lim_seq_deriv_thm⦎ = save_thm ( "unif_lim_seq_deriv_thm", (
set_goal([], ⌜∀u du df A B x0 y0 ⦁
	(du ---> df) (OpenInterval A B)
∧	(∀y m⦁ y ∈ OpenInterval A B ⇒ (u m Deriv du m y) y)
∧	x0 ∈ OpenInterval A B
∧	((λm⦁ u m x0) ->  y0)
⇒	∃f⦁ (u ---> f)  (OpenInterval A B) ∧ ∀y⦁ y ∈ OpenInterval A B ⇒ (f Deriv df y) y
⌝);
a(REPEAT ∀_tac);
a(conv_tac(LEFT_C (RIGHT_C (rewrite_conv[open_interval_def]))));
a(conv_tac(RIGHT_C (BINDER_C(RIGHT_C (rewrite_conv[open_interval_def])))));
a(REPEAT strip_tac);
a(all_fc_tac[unif_lim_seq_deriv_lemma]);
a(∃_tac⌜f⌝ THEN GET_NTH_ASM_T 5 ante_tac);
a(rewrite_tac[deriv_lim_fun_thm] THEN REPEAT strip_tac);
a(lemma_tac
	⌜∃g⦁((λm⦁λ y'⦁ (u m y' + ~ (u m y)) / (y' + ~ y)) ---> g) (OpenInterval A B \ {y})⌝);
(* *** Goal "1" *** *)
a(bc_thm_tac cauchy_seq_unif_lim_seq_thm THEN rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac);
a(all_fc_tac[unif_lim_seq_deriv_estimate_thm]);
a(∃_tac⌜N⌝ THEN PC_T1 "sets_ext1" rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
a(lemma_tac⌜y' < y ∨ y < y'⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.1" *** *)
a(list_spec_nth_asm_tac 7 [⌜k⌝, ⌜m⌝, ⌜y⌝, ⌜y'⌝]);
a(lemma_tac⌜¬y' + ~y = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac [ℝ_over_times_recip_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c d e: ℝ⦁
	(a + b) * c + ~((d + ~e) * c) = (a + ~d + b + e)*c⌝, 	ℝ_abs_times_thm]);
a(ALL_FC_T rewrite_tac [ℝ_abs_recip_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ Abs (y' + ~ y)⌝ THEN1 rewrite_tac [ℝ_0_≤_abs_thm]);
a(lemma_tac⌜¬Abs (y' + ~ y) = ℕℝ 0⌝ THEN1 asm_rewrite_tac [ℝ_abs_eq_0_thm]);
a(lemma_tac⌜ℕℝ 0 < Abs (y' + ~ y)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac [∀_elim⌜Abs(y' + ~y)⌝ ℝ_times_mono_⇔_thm]);
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c: ℝ⦁ a*b*c = b*a*c⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(bc_thm_tac ℝ_≤_less_trans_thm);
a(∃_tac⌜Abs (y' + ~ y) * 1 / 2 * e⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_times_mono_thm);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(list_spec_nth_asm_tac 7 [⌜k⌝, ⌜m⌝, ⌜y⌝, ⌜y'⌝]);
a(lemma_tac⌜¬y' + ~y = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac [ℝ_over_times_recip_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c d e: ℝ⦁
	(a + b) * c + ~((d + ~e) * c) = (a + ~d + b + e)*c⌝, 	ℝ_abs_times_thm]);
a(ALL_FC_T rewrite_tac [ℝ_abs_recip_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ Abs (y' + ~ y)⌝ THEN1 rewrite_tac [ℝ_0_≤_abs_thm]);
a(lemma_tac⌜¬Abs (y' + ~ y) = ℕℝ 0⌝ THEN1 asm_rewrite_tac [ℝ_abs_eq_0_thm]);
a(lemma_tac⌜ℕℝ 0 < Abs (y' + ~ y)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac [∀_elim⌜Abs(y' + ~y)⌝ ℝ_times_mono_⇔_thm]);
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c: ℝ⦁ a*b*c = b*a*c⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(bc_thm_tac ℝ_≤_less_trans_thm);
a(∃_tac⌜Abs (y' + ~ y) * 1 / 2 * e⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_times_mono_thm);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜∃s⦁∀m⦁s m = du m y⌝ (strip_asm_tac o  conv_rule (ONCE_MAP_C eq_sym_conv))
	THEN1 prove_∃_tac);
a(DROP_NTH_ASM_T 5 (ante_tac o ∀_elim⌜y⌝));
a(LIST_GET_NTH_ASM_T [1, 3, 4] rewrite_tac);
a(pure_once_rewrite_tac[prove_rule[]
	⌜	(λ y'⦁ (u m y' + ~ (u m y)) / (y' + ~ y))
	=	(λm y'⦁ (u m y' + ~ (u m y)) / (y' + ~ y)) m⌝]);
a(REPEAT strip_tac THEN all_fc_tac[lim_fun_lim_seq_interchange_thm]);
a(lemma_tac⌜∀t⦁A < t ∧ t < B ∧ ¬t = y ⇒ g t = (λ y'⦁ (f y' + ~ (f y)) / (y' + ~ y)) t⌝);
(* *** Goal "2.1" *** *)
a(PC_T1 "predicates"  REPEAT strip_tac THEN bc_thm_tac unif_lim_seq_pointwise_unique_thm);
a(∃_tac⌜OpenInterval A B \ {y}⌝ THEN
	∃_tac⌜(λ m y'⦁ (u m y' + ~ (u m y)) / (y' + ~ y))⌝ THEN
	REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(PC_T1 "sets_ext1" rewrite_tac[open_interval_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(lemma_tac⌜¬t + ~y = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(ho_bc_thm_tac times_lim_seq_thm);
a(rewrite_tac[const_lim_seq_thm]);
a(ho_bc_thm_tac plus_lim_seq_thm);
a(conv_tac (RIGHT_C(once_rewrite_conv[minus_lim_seq_thm])) THEN rewrite_tac[]);
a(lemma_tac⌜t ∈ OpenInterval A B ∧ y ∈ OpenInterval A B⌝
	THEN1 (PC_T1 "sets_ext1" rewrite_tac[open_interval_def]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[unif_lim_seq_pointwise_lim_seq_thm] THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜s -> df y⌝);
(* *** Goal "2.2.1" *** *)
a(LEMMA_T⌜s = λm⦁du m y⌝ rewrite_thm_tac THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜y ∈ OpenInterval A B ⌝
	THEN1 (PC_T1 "sets_ext1" rewrite_tac[open_interval_def]
		THEN REPEAT strip_tac));
a(all_fc_tac[unif_lim_seq_pointwise_lim_seq_thm] THEN REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a(all_fc_tac[lim_seq_unique_thm] THEN all_var_elim_asm_tac1);
a(bc_thm_tac lim_fun_local_thm);
a(MAP_EVERY ∃_tac[⌜B⌝, ⌜A⌝, ⌜g⌝] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] (ALL_FC_T rewrite_tac));
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Series and Power Series}
%%%%
%%%%
%%%%
%%%%
We now prove some basic facts about series and power series.
These depend on some facts about limits of particular sequences
that could have been given earlier, but may conveniently be given now.
To warm up, we prove equations showing that our
notions of series and power series are interdefinable:
=TEX
%%%%
%%%%
=SML

val ⦏power_series_series_thm⦎ = save_thm ( "power_series_series_thm", (
set_goal([], ⌜∀s⦁ PowerSeries s = λn⦁ λ x⦁Series (λm⦁ s m*x^m) n⌝);
a(REPEAT strip_tac);
a(rewrite_tac[power_series_def]);
a(induction_tac⌜x⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[to_def, series_def, poly_eval_def]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[to_def, series_def, poly_eval_def, poly_eval_append_thm,
	length_to_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏series_power_series_thm⦎ = save_thm ( "series_power_series_thm", (
set_goal([], ⌜∀s⦁ Series s = λn⦁ PowerSeries s n (ℕℝ 1)⌝);
a(REPEAT strip_tac THEN rewrite_tac[power_series_def]);
a(induction_tac⌜x⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[to_def, series_def, poly_eval_def]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[to_def, series_def, poly_eval_def, poly_eval_append_thm,
	length_to_thm, ℝ_ℕ_exp_0_1_thm]);
pop_thm()
));

=TEX
It is useful to know the value taken by the partial sums of a power series
when the argument is 0:
%%%%
%%%%
=SML

val ⦏power_series_0_arg_thm⦎ = save_thm ( "power_series_0_arg_thm", (
set_goal([], ⌜
	(∀s⦁ PowerSeries s 0 (ℕℝ 0) = ℕℝ 0)
∧	∀s m⦁ PowerSeries s (m+1) (ℕℝ 0) = s 0⌝);
a(rewrite_tac[power_series_series_thm] THEN REPEAT strip_tac
	THEN1 rewrite_tac[series_def, to_def]);
a(induction_tac⌜m⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[to_def, series_def]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[to_def, series_def, ℝ_ℕ_exp_0_1_thm]);
pop_thm()
));

=TEX
With the previous theorem we can readily prove our first result on convergence
of power series --- a trivial but useful one:
%%%%
%%%%
=SML

val ⦏power_series_limit_0_thm⦎ = save_thm ( "power_series_limit_0_thm", (
set_goal([], ⌜∀s⦁ (λ m⦁ PowerSeries s m (ℕℝ 0)) -> s 0⌝);
a(REPEAT strip_tac);
a(once_rewrite_tac[∀_elim⌜1⌝ lim_seq_shift_thm]);
a(rewrite_tac[power_series_0_arg_thm, const_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_series_thm⦎ = save_thm ( "plus_series_thm", (
set_goal([], ⌜∀s1 s2⦁ Series (λm⦁s1 m + s2 m) = (λn⦁ Series s1 n + Series s2 n)⌝);
a(REPEAT strip_tac THEN induction_tac⌜x:ℕ⌝ THEN asm_rewrite_tac[series_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏series_0_thm⦎ = save_thm ( "series_0_thm", (
set_goal([], ⌜Series (λm⦁ℕℝ 0) = (λm⦁ ℕℝ 0)⌝);
a(REPEAT strip_tac THEN induction_tac⌜x:ℕ⌝ THEN asm_rewrite_tac[series_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏const_times_series_thm⦎ = save_thm ( "const_times_series_thm", (
set_goal([], ⌜∀s c⦁ Series (λm⦁c * s m) = (λn⦁c * Series s n)⌝);
a(REPEAT strip_tac THEN induction_tac⌜x:ℕ⌝ THEN asm_rewrite_tac[series_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜(λm⦁ ℕℝ (m+1) ⋏-⋏1) -> ℕℝ 0⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(all_fc_tac[ℝ_archimedean_recip_thm]);
a(DROP_NTH_ASM_T 2 discard_tac THEN ∃_tac⌜m+1⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜ℕℝ (m + 1) ⋏-⋏1⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < ℕℝ(m'+1)⌝ THEN1 rewrite_tac[ℕℝ_less_thm]);
a(lemma_tac⌜¬ℕℝ(m'+1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(ALL_FC_T rewrite_tac [ℝ_abs_recip_thm]);
a(bc_thm_tac ℝ_less_recip_less_thm);
a(rewrite_tac[ℕℝ_less_thm]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
val ⦏lim_seq_ℕℝ_recip_eq_0_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_ℕℝ_recip_eq_0_thm⦎ = save_thm ( "lim_seq_ℕℝ_recip_eq_0_thm", (
set_goal([], ⌜(λm⦁ ℕℝ m ⋏-⋏1) -> ℕℝ 0⌝);
a(once_rewrite_tac[∀_elim⌜1⌝ lim_seq_shift_thm]);
a(rewrite_tac[lim_seq_ℕℝ_recip_eq_0_lemma]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀x⦁ ℕℝ 0 < x ∧ x < ℕℝ 1 ⇒ (λm:ℕ⦁ x^m) -> ℕℝ 0⌝);
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∀m⦁ℕℝ 0 ≤ x^(m:ℕ)⌝ THEN1
	(rewrite_tac[ℝ_≤_def] THEN FC_T rewrite_tac[ℝ_ℕ_exp_0_less_thm]));
a(asm_rewrite_tac[ℝ_abs_def]);
a(all_fc_tac[ℝ_ℕ_exp_tends_to_0_thm]);
a(∃_tac⌜m+1⌝ THEN REPEAT strip_tac);
a(lemma_tac ⌜m < m''⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac ⌜x^m⌝ THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_ℕ_exp_less_1_mono_thm1 THEN REPEAT strip_tac);
val ⦏lim_seq_ℝ_ℕ_exp_eq_0_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_ℝ_ℕ_exp_eq_0_thm⦎ = save_thm ( "lim_seq_ℝ_ℕ_exp_eq_0_thm", (
set_goal([], ⌜∀x⦁~(ℕℝ 1) < x ∧ x < ℕℝ 1 ⇒ (λm:ℕ⦁ x^m) -> ℕℝ 0⌝);
a(REPEAT strip_tac);
a(cases_tac⌜x = ℕℝ 0⌝ THEN1
	(once_rewrite_tac[∀_elim⌜1⌝ lim_seq_shift_thm] THEN
		asm_rewrite_tac[ℝ_ℕ_exp_0_1_thm, const_lim_seq_thm]));
a(cases_tac⌜ℕℝ 0 < x⌝ THEN1 all_fc_tac[lim_seq_ℝ_ℕ_exp_eq_0_lemma]);
a(once_rewrite_tac[∀_elim⌜1⌝ lim_seq_shift_thm] THEN rewrite_tac[]);
a(lemma_tac⌜ℕℝ 0 < ~x ∧ ~x < ℕℝ 1⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[lim_seq_ℝ_ℕ_exp_eq_0_lemma]);
a(POP_ASM_T ante_tac);
a(pure_once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀x⦁~x  = ~(ℕℝ 1) * x⌝]);
a(pure_rewrite_tac[ℝ_ℕ_exp_times_thm]);
a(DROP_ASMS_T discard_tac THEN rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o ∀_elim⌜m+1⌝)
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(POP_ASM_T ante_tac);
a(rewrite_tac[ℝ_abs_times_thm]);
a(LEMMA_T⌜Abs (~ (ℕℝ 1) ^ (m + 1)) = ℕℝ 1⌝ rewrite_thm_tac);
a(rewrite_tac[ℝ_abs_ℝ_ℕ_exp_thm, ℝ_ℕ_exp_0_1_thm]);
pop_thm()
));

=TEX
The next theorem gives the identity relating a series to a trailing subseries:
%%%%
%%%%
=SML

val ⦏series_shift_thm⦎ = save_thm ( "series_shift_thm", (
set_goal([], ⌜
	∀n s⦁ (Series (λm⦁ s (m + n))  = λm⦁Series s (m+n) - Series s n)
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜x:ℕ⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[series_def]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[series_def]);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]⌜(x+1)+n=(x+n)+1⌝, series_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
A series is convergent iff. some trailing subseries is convergent.
We first state and prove this with an explicit formula for the limit:
%%%%
%%%%
=SML

val ⦏lim_series_shift_thm⦎ = save_thm ( "lim_series_shift_thm", (
set_goal([], ⌜
	∀n s x⦁ 
	(Series s ->  x)
⇔	(Series (λm⦁ s (m + n)) -> x - Series s n)
⌝);
a(REPEAT ∀_tac);
a(rewrite_tac[series_shift_thm]);
a(conv_tac(LEFT_C(once_rewrite_conv[∀_elim⌜n⌝ lim_seq_shift_thm])));
a(rewrite_tac[lim_seq_def]);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b c:ℝ⦁ (a + ~b) + c + b = a + c⌝]);
pop_thm()
));

=TEX
As a technical convenience it is also useful to have a pure existence version of
the above theorem:
%%%%
%%%%
=SML

val ⦏lim_series_shift_∃_thm⦎ = save_thm ( "lim_series_shift_∃_thm", (
set_goal([], ⌜
	∀n s⦁ 
	(∃x⦁Series s ->  x)
⇔	(∃x⦁ Series (λm⦁ s (m + n)) -> x)
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜x - Series s n⌝);
a(bc_thm_tac lim_series_shift_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(∃_tac⌜x + Series s n⌝);
a(once_rewrite_tac[∀_elim⌜n⌝ lim_series_shift_thm]);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏lim_series_bounded_thm⦎ = save_thm ( "lim_series_bounded_thm", (
set_goal([], ⌜
	∀e s c⦁ 
	ℕℝ 0 < e
∧	Series s -> c
⇒	∃m⦁ ∀n⦁m ≤ n ⇒ Abs(s n) < e
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[lim_seq_diffs_tend_to_0_thm]);
a(POP_ASM_T ante_tac THEN POP_ASM_T discard_tac);
a(rewrite_tac[series_def] THEN conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜e⌝));
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
The following gives the identity for summing a geometric series.
%%%%
%%%%
=SML

val ⦏geometric_sum_thm1⦎ = save_thm ( "geometric_sum_thm1", (
set_goal([], ⌜
	∀n x⦁ 
	¬x = ℕℝ 1
⇒	PolyEval ((λm⦁ℕℝ 1) To (n+1)) x = (ℕℝ 1 - x^(n+1)) / (ℕℝ 1 - x)
⌝);
a(REPEAT strip_tac);
a(ante_tac(rewrite_rule[rev_const_to_thm,ℝ_ℕ_exp_0_1_thm]
	(list_∀_elim[⌜n⌝, ⌜x⌝,  ⌜ℕℝ 1⌝] poly_diff_powers_thm)));
a(lemma_tac⌜¬x + ~(ℕℝ 1) = ℕℝ 0 ∧ ¬ℕℝ 1 + ~x = ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[∀_elim⌜x + ~(ℕℝ 1)⌝ ℝ_over_times_recip_thm]);
a(ALL_FC_T rewrite_tac[∀_elim⌜(ℕℝ 1 + ~x)⌝ ℝ_over_times_recip_thm]);
a(REPEAT strip_tac);
a(pure_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀t⦁ℕℝ 1 + ~t = ~(t + ~(ℕℝ 1))⌝]);
a(ALL_FC_T pure_rewrite_tac[ℝ_minus_recip_thm]);
a(pure_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁ ~a * ~b = a*b⌝]);
a(LEMMA_T⌜∀a b⦁a = b ⇒ (x + ~ (ℕℝ 1)) ⋏-⋏1 * a = b * (x + ~ (ℕℝ 1)) ⋏-⋏1⌝
	(fn th => all_fc_tac[th]) THEN1
	(REPEAT strip_tac THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(POP_ASM_T ante_tac);
a(asm_rewrite_tac[ℝ_times_assoc_thm1]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
The following gives the identity for summing a geometric series.
%%%%
%%%%
=SML

val ⦏geometric_sum_thm⦎ = save_thm ( "geometric_sum_thm", (
set_goal([], ⌜
	∀n x⦁ 
	¬x = ℕℝ 1
⇒	Series (λ m⦁ x ^ m) (n+1) = (ℕℝ 1 - x^(n+1)) / (ℕℝ 1 - x)
⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜Series (λ m⦁ x ^ m) (n+1) = PowerSeries (λm⦁ℕℝ 1) (n+1) x⌝
	(fn th => rewrite_tac[th, power_series_def])
	THEN1 rewrite_tac[power_series_series_thm]);
a(ALL_FC_T rewrite_tac[geometric_sum_thm1]);
pop_thm()
));

=TEX
We can now show that geometric series converge for arguments of absolute value
less than 1.
%%%%
%%%%
=SML

val ⦏geometric_series_thm⦎ = save_thm ( "geometric_series_thm", (
set_goal([], ⌜
	∀x⦁ 
	~(ℕℝ 1) < x ∧ x < ℕℝ 1
⇒	(λn⦁ PowerSeries (λm⦁ℕℝ 1) n x) -> ℕℝ 1 / (ℕℝ 1 - x)
⌝);
a(REPEAT strip_tac THEN lemma_tac ⌜¬x = ℕℝ 1⌝ THEN1 PC_T1 "ℝ_lin_arith"
	asm_prove_tac[]);
a(rewrite_tac[power_series_series_thm]);
a(once_rewrite_tac[∀_elim⌜1⌝ lim_seq_shift_thm]);
a(FC_T rewrite_tac[geometric_sum_thm]);
a(lemma_tac⌜¬ℕℝ 1 + ~x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[∀_elim⌜(ℕℝ 1 + ~x)⌝ ℝ_over_times_recip_thm]);
a(rewrite_tac[ℝ_times_plus_distrib_thm]);
a(conv_tac (RIGHT_C (once_rewrite_conv[prove_rule[]⌜∀x⦁x = x + ℕℝ 0⌝])));
a(ho_bc_thm_tac plus_lim_seq_thm THEN rewrite_tac[const_lim_seq_thm]);
a(once_rewrite_tac[prove_rule[]⌜ℕℝ 0 = ℕℝ 0 * (ℕℝ 1 + ~ x) ⋏-⋏1⌝]);
a(ho_bc_thm_tac times_lim_seq_thm THEN rewrite_tac[const_lim_seq_thm]);
a(once_rewrite_tac[prove_rule[]⌜ℕℝ 0 = ~(ℕℝ 0)⌝]);
a(ho_bc_thm_tac minus_lim_seq_thm);
a(bc_thm_tac( rewrite_rule[]
	(once_rewrite_rule[∀_elim⌜1⌝ lim_seq_shift_thm] lim_seq_ℝ_ℕ_exp_eq_0_thm)));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
A simpler formula for a geometric series is often useful:
%%%%
%%%%
=SML

val ⦏geometric_series_series_thm⦎ = save_thm ( "geometric_series_series_thm", (
set_goal([], ⌜
	∀x⦁ (λn⦁ PowerSeries (λm⦁ℕℝ 1) n x) = Series (λm⦁x^m)
⌝);
a(REPEAT strip_tac THEN rewrite_tac[power_series_def]);
a(induction_tac⌜x':ℕ⌝ THEN rewrite_tac[series_def, poly_eval_def, to_def]);
a(asm_rewrite_tac [poly_eval_append_thm, length_to_thm, poly_eval_def]);
pop_thm()
));

=TEX
The theorem about the convergence of a geometric series then simplifies:
%%%%
%%%%
=SML

val ⦏geometric_series_thm1⦎ = save_thm ( "geometric_series_thm1", (
set_goal([], ⌜
	∀x⦁ 
	~(ℕℝ 1) < x ∧ x < ℕℝ 1
⇒	Series (λm⦁x^m) -> ℕℝ 1 / (ℕℝ 1 - x)
⌝);
a(ante_tac geometric_series_thm THEN rewrite_tac[geometric_series_series_thm]);
pop_thm()
));

=TEX
The Weierstrass uniform convergence test: a series of functions with absolute
values dominated by a convergent series on some set of values converges uniformly
to a limit function on that set.
%%%%
%%%%
=SML

val ⦏weierstrass_test_thm⦎ = save_thm ( "weierstrass_test_thm", (
set_goal([], ⌜
	∀u X s c⦁ 
	(∀m x⦁x ∈ X ⇒ Abs(u m x) ≤ s m)
∧	(Series s -> c)
⇒	∃f⦁ ((λm⦁λx⦁Series (λm⦁u m x) m) ---> f) X
⌝);
a(REPEAT strip_tac);
a(fc_tac[lim_seq_cauchy_seq_thm]);
a(bc_thm_tac cauchy_seq_unif_lim_seq_thm);
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 ante_tac THEN rewrite_tac[]);
a(REPEAT strip_tac);
a(lemma_tac⌜Abs (Series s k + ~ (Series s m)) < e⌝
	THEN1 LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜Abs (Series s k + ~ (Series s m))⌝
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T ((interval 1 7) less 3) discard_tac);
a(lemma_tac  ⌜∀k m⦁ m ≤ k ⇒
	Abs (Series (λ m⦁ u m y) k + ~ (Series (λ m⦁ u m y) m))
		≤ Series s k + ~ (Series s m)⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1);
a(induction_tac ⌜i⌝ THEN rewrite_tac[series_def, plus_assoc_thm1, ℝ_plus_assoc_thm1]);
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c:ℝ⦁ (a+b) + ~c = b + a + ~c⌝]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜
	Abs(u (m+i) y) + Abs(Series (λ m⦁ u m y) (m + i) + ~ (Series (λ m⦁ u m y) m)) ⌝);
a(rewrite_tac[ℝ_abs_plus_thm]);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c d:ℝ⦁a ≤ b ∧ c ≤ d ⇒ a + c ≤ b + d⌝));
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(lemma_tac  ⌜∀m⦁ ℕℝ 0 ≤ s m⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac THEN bc_thm_tac ℝ_≤_trans_thm
	THEN ∃_tac ⌜Abs(u m y)⌝);
a(rewrite_tac[ℝ_0_≤_abs_thm] THEN GET_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac  ⌜∀k m⦁ m ≤ k ⇒ ℕℝ 0 ≤ Series s k + ~ (Series s m)⌝);
(* *** Goal "2.2.1" *** *)
a(REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1);
a(induction_tac ⌜i⌝ THEN rewrite_tac[series_def, plus_assoc_thm1]);
a(spec_nth_asm_tac 2 ⌜m+i⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac ⌜k ≤ m ∨ m ≤ k⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.2.1" *** *)
a(once_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁a + ~b = ~(b + ~a)⌝]);
a(pure_rewrite_tac[ℝ_abs_minus_thm]) (* Makes it same as 2.2.2.2! *);
a(conv_tac (RIGHT_C (rewrite_conv[ℝ_abs_def])));
a(LIST_DROP_NTH_ASM_T [2] (ALL_FC_T rewrite_tac));
a(GET_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
The comparison test: a series whose absolute values are dominated by a convergent
series is convergent (this is often stated in the special case when the dominated series
is a series of non-negative values, but the general case is just as easy in the present context):
%%%%
%%%%
=SML

val ⦏comparison_test_thm⦎ = save_thm ( "comparison_test_thm", (
set_goal([], ⌜
	∀s1 s2 c2⦁ 
	(∀m⦁Abs(s1 m) ≤ s2 m)
∧	(Series s2 ->  c2)
⇒	∃c1⦁ Series s1 -> c1
⌝);
a(REPEAT strip_tac);
a(ante_tac (list_∀_elim [⌜λm; x:ℝ⦁s1 m⌝, ⌜Universe:ℝ SET⌝, ⌜s2⌝, ⌜c2⌝] weierstrass_test_thm));
a(asm_rewrite_tac[lim_seq_def, unif_lim_seq_def, ∀_elim⌜s1⌝ η_axiom] THEN REPEAT strip_tac);
a(∃_tac⌜f x⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
pop_thm()
));

=TEX
The root test without tears (or roots!). The usual statement of this is that a series $\Sigma s_m$ converges
if $ \LimSup\,\sqrt[m]{\Abs{s_m}} < 1$. The proof of this fact immediately translates
the condition into the assertion that $\Abs{s_m}$ is bounded by $b^m$ for some $b$, $0 < b < 1$,
for all large enough $m$. Since the latter assertion is exactly what you have to prove to show that
$ \LimSup\,\sqrt[m]{\Abs{s_m}} < 1$, we just use it directly in our statement of the theorem.
This form given is just as easy to use in most applications (and better captures the essence of what is actually going
on, in my opinion).
%%%%
%%%%
=SML

val ⦏simple_root_test_thm⦎ = save_thm ( "simple_root_test_thm", (
set_goal([], ⌜
	∀s b m⦁ 
	ℕℝ 0 < b ∧ b  < ℕℝ 1 
∧	(∀n⦁m ≤ n ⇒ Abs(s n) ≤ b^n)
⇒	∃c⦁ Series s -> c
⌝);
a(REPEAT strip_tac);
a(once_rewrite_tac[∀_elim⌜m⌝lim_series_shift_∃_thm]);
a(bc_thm_tac comparison_test_thm);
a(∃_tac⌜(ℕℝ 1 / (ℕℝ 1 + ~ b)) *  b^m⌝ THEN ∃_tac ⌜λk⦁b ^(k + m)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[] THEN POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(rewrite_tac[ℝ_ℕ_exp_plus_thm]);
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(rewrite_tac[
	conv_rule(ONCE_MAP_C β_conv)(∀_elim⌜λk:ℕ⦁b^k⌝ const_times_series_thm)]);
a(ho_bc_thm_tac times_lim_seq_thm);
a(rewrite_tac[const_lim_seq_thm]);
a(lemma_tac⌜~(ℕℝ 1) < b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ho_bc_thm_tac (rewrite_rule[]geometric_series_thm1));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
The root test as formulated above will also tolerate a multiplicative constant in the estimate.
Moreover there is no need to assume that either of the constants is positive. This gives
the following generalisation which is what we will typically use in practice.
%%%%
%%%%
=SML

val ⦏root_test_thm⦎ = save_thm ( "root_test_thm", (
set_goal([], ⌜
	∀s b d m⦁ 
	b  < ℕℝ 1 
∧	(∀n:ℕ⦁m ≤ n ⇒ Abs(s n) ≤ d*b^n)
⇒	∃c⦁ Series s -> c
⌝);
a(REPEAT strip_tac THEN  CASES_T ⌜b = ℕℝ 0 ∨ d = ℕℝ 0⌝ asm_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜∀n⦁d*b^(n+1) = ℕℝ 0⌝ THEN1 (POP_ASM_T strip_asm_tac THEN
	asm_rewrite_tac[ℝ_ℕ_exp_0_1_thm]));
a(LEMMA_T⌜∀n⦁m ≤ n ⇒ Abs(s(n+1)) ≤ d*b^(n+1)⌝ ante_tac THEN1 (
	REPEAT strip_tac THEN
		DROP_NTH_ASM_T 4 bc_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(asm_rewrite_tac[ℝ_abs_≤_0_thm] THEN strip_tac);
a(once_rewrite_tac[∀_elim⌜m+1⌝ lim_series_shift_∃_thm]);
a(∃_tac⌜ℕℝ 0⌝);
a(LEMMA_T ⌜(λk⦁s(k + m + 1)) = (λm⦁ℕℝ 0)⌝ 
	(fn th => rewrite_tac[th, series_0_thm, const_lim_seq_thm]));
a(REPEAT strip_tac THEN rewrite_tac[plus_assoc_thm1]);
a(POP_ASM_T bc_thm_tac THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T strip_asm_tac);
a(spec_nth_asm_tac 3 ⌜m⌝);
a(GET_NTH_ASM_T 4 (strip_asm_tac o rewrite_rule[ℝ_ℕ_exp_def] o ∀_elim⌜m + 1⌝));
a(lemma_tac⌜¬b^m = ℕℝ 0 ⌝ THEN1
	(bc_thm_tac ℝ_ℕ_exp_¬_eq_0_thm THEN REPEAT strip_tac));
a(lemma_tac⌜¬d * b ^ m = ℕℝ 0 ∧ ¬d * b *b^m = ℕℝ 0⌝ THEN1
	(asm_rewrite_tac[ℝ_times_eq_0_thm]));
a(lemma_tac⌜ℕℝ 0 ≤ d*b^m⌝ THEN1
	(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac ⌜Abs (s m)⌝
		THEN asm_rewrite_tac[ℝ_0_≤_abs_thm]));
a(lemma_tac⌜ℕℝ 0 ≤ d* b * b^m⌝ THEN1
	(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac ⌜Abs (s (m+1))⌝
		THEN asm_rewrite_tac[ℝ_0_≤_abs_thm]));
a(lemma_tac⌜ℕℝ 0 < d* b^m ∧ ℕℝ 0 < d* b * b^m⌝ THEN1
	(PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ 0 < (d*b^m)⋏-⋏1⌝ THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(LEMMA_T⌜ℕℝ 0 < (d*b*b^m)*(d*b^m)⋏-⋏1⌝ ante_tac
		THEN1 all_fc_tac[ℝ_0_less_0_less_times_thm]);
a(ALL_FC_T rewrite_tac [ℝ_recip_clauses]);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b c d e:ℝ⦁(a*b*c)*d *e = b*a*d*c*e⌝]);
a(ALL_FC_T rewrite_tac [ℝ_recip_clauses]);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 <  b^m ⌝ THEN1
	(bc_thm_tac ℝ_ℕ_exp_0_less_thm THEN REPEAT strip_tac));
a(lemma_tac⌜ℕℝ 0 < (b^m)⋏-⋏1⌝ THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(LEMMA_T⌜ℕℝ 0 < (d*b^m) * (b^m) ⋏-⋏1 ⌝ ante_tac THEN1 all_fc_tac[ℝ_0_less_0_less_times_thm]);
a(rewrite_tac[ℝ_times_assoc_thm] THEN  ALL_FC_T rewrite_tac [ℝ_recip_clauses]);
a(REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [1, 4, 15, 17, 18] (MAP_EVERY ante_tac)
	THEN DROP_ASMS_T discard_tac THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < d ⋏-⋏1⌝ THEN1
	(bc_thm_tac ℝ_0_less_0_less_recip_thm THEN REPEAT strip_tac));
a(lemma_tac⌜∃k:ℕ⦁b^k < d ⋏-⋏1⌝ THEN1
	(bc_thm_tac ℝ_ℕ_exp_tends_to_0_thm THEN REPEAT strip_tac));
a(once_rewrite_tac [∀_elim⌜k⌝ lim_series_shift_∃_thm]);
a(bc_thm_tac simple_root_test_thm);
a(∃_tac⌜m⌝ THEN ∃_tac⌜b⌝ THEN rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac ⌜m ≤ n + k⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 8 ⌜n+k⌝);
a(REPEAT strip_tac THEN bc_thm_tac ℝ_≤_trans_thm THEN
	∃_tac⌜d * b^(n+k)⌝ THEN REPEAT strip_tac);
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(rewrite_tac[ℝ_ℕ_exp_plus_thm, ℝ_times_assoc_thm]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜b^n * ℕℝ 1⌝);
a(conv_tac(RIGHT_C (rewrite_conv[])) THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_≤_times_mono_thm THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[ℝ_≤_def] THEN ∨_left_tac);
a(bc_thm_tac ℝ_ℕ_exp_0_less_thm THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(REPEAT strip_tac THEN bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜d ⋏-⋏1 * d⌝);
a(REPEAT strip_tac THEN_LIST [id_tac, ALL_FC_T rewrite_tac[ℝ_recip_clauses]]);
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(bc_thm_tac ℝ_≤_times_mono_thm);
a(asm_rewrite_tac[ℝ_≤_def]);
pop_thm()
));

=TEX
The heart of the ratio test: this is generally formulated
using lim sups or limits (which can be useful), but neither is necessary: we just need to know that
the ratios are eventually all bounded below 1. We formulate this as follows.
%%%%
%%%%
=SML

val ⦏ratio_test_thm1⦎ = save_thm ( "ratio_test_thm1", (
set_goal([], ⌜
	∀s b m⦁
	(∀m⦁¬s m = ℕℝ 0)
∧	ℕℝ 0 < b ∧ b < ℕℝ 1
∧	(∀n⦁m ≤ n ⇒ Abs(s (n+1) / s n) < b)
⇒	∃c ⦁ Series s -> c
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀i⦁ℕℝ 0 < Abs(s i)⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜s i⌝ ℝ_0_≤_abs_thm));
a(DROP_NTH_ASM_T 5 (strip_asm_tac o ∀_elim⌜i⌝));
a(lemma_tac⌜¬Abs(s i ) = ℕℝ 0⌝ THEN1 asm_rewrite_tac[ℝ_abs_eq_0_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a( lemma_tac⌜∀i⦁Abs(s(m + i)) ≤ Abs(s m) * b^ i⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac THEN induction_tac⌜i:ℕ⌝ THEN rewrite_tac[ℝ_ℕ_exp_def]);
a(rewrite_tac[ℝ_≤_def] THEN ∨_left_tac);
a(DROP_NTH_ASM_T 3 (ante_tac o ∀_elim⌜m + i⌝));
a(DROP_NTH_ASM_T 5 (strip_asm_tac o ∀_elim⌜m + i⌝));
a(rewrite_tac[plus_assoc_thm]);
a(ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
a(rewrite_tac[ℝ_abs_times_thm, ℝ_times_assoc_thm]);
a(ALL_FC_T rewrite_tac[ℝ_abs_recip_thm] THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_less_≤_trans_thm THEN ∃_tac⌜Abs(s(m+i))*b⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a(lemma_tac⌜¬Abs(s(m+i) ) = ℕℝ 0⌝ THEN1 asm_rewrite_tac[ℝ_abs_eq_0_thm]);
a(DROP_NTH_ASM_T 5 (strip_asm_tac o ∀_elim⌜m + i⌝));
a(lemma_tac⌜ℕℝ 0 < Abs(s(m+i))⋏-⋏1⌝ THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac
	[∀_elim⌜Abs(s(m+i))⋏-⋏1⌝ ℝ_times_mono_⇔_thm]);
a(once_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀a b c d e:ℝ⦁a * b < c * d * e ⇔ b * a < (c * d) * e⌝]);
a(ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2.1.2" *** *)
a(once_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀a b c d e:ℝ⦁a * b ≤ c * d * e ⇔ b * a ≤ d * c * e⌝]);
a(bc_thm_tac ℝ_≤_times_mono_thm THEN REPEAT strip_tac);
a(asm_rewrite_tac[ℝ_≤_def]);
(* *** Goal "2.2" *** *)
a(once_rewrite_tac[∀_elim⌜m⌝ lim_series_shift_∃_thm]);
a(bc_thm_tac root_test_thm);
a(∃_tac⌜Abs(s m)⌝ THEN ∃_tac⌜0⌝  THEN ∃_tac⌜b⌝ THEN rewrite_tac[] THEN REPEAT strip_tac);
a(once_rewrite_tac [plus_comm_thm] THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The ratio test  in terms of limits is often useful (and this is what we call the ratio test).
%%%%
%%%%
=SML

val ⦏ratio_test_thm⦎ = save_thm ( "ratio_test_thm", (
set_goal([], ⌜
	∀s b⦁
	(∀m⦁¬s m = ℕℝ 0)
∧	ℕℝ 0 ≤ b ∧ b < ℕℝ 1
∧	(λn⦁ Abs(s (n+1) / s n)) -> b
⇒	∃c ⦁ Series s -> c
⌝);
a(REPEAT strip_tac THEN bc_thm_tac ratio_test_thm1 THEN
	POP_ASM_T (strip_asm_tac o rewrite_rule[lim_seq_def]) THEN 
	rename_tac[] THEN asm_rewrite_tac[] );
a(lemma_tac⌜∃c⦁ℕℝ 0 < c ∧ ℕℝ 0 < c + ~b ∧ c < ℕℝ 1⌝ THEN1
	(∃_tac⌜(b + ℕℝ 1) / ℕℝ 2⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LIST_DROP_NTH_ASM_T [3, 6] (MAP_EVERY ante_tac)
	THEN LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(REPEAT strip_tac THEN ∃_tac⌜n⌝ THEN ∃_tac ⌜c⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜n'⌝) THEN asm_rewrite_tac[]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
Uniform convergence of power series:
%%%%
%%%%
=SML

val ⦏power_series_convergence_thm⦎ = save_thm ( "power_series_convergence_thm", (
set_goal([], ⌜
	∀s B C b⦁
	ℕℝ 0 < B ∧ ℕℝ 0 < b ∧ b < B
∧	(λm⦁ PowerSeries (λm⦁Abs(s m)) m B) ->  C
⇒	∃f⦁ (PowerSeries s ---> f) (OpenInterval (~b) b)
⌝);
a(rewrite_tac[power_series_series_thm] THEN REPEAT strip_tac);
a(pure_once_rewrite_tac[prove_rule[]⌜∀m : ℕ; x:ℝ⦁ 
		(λ m⦁ s m * x ^ m) =
		(λ m⦁ (λm x⦁ s m  * x ^ m) m x)⌝]);
a(bc_thm_tac weierstrass_test_thm);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[η_axiom]));
a(∃_tac⌜C⌝ THEN ∃_tac ⌜λ m⦁ Abs (s m) * B ^ m⌝ THEN rewrite_tac[open_interval_def]
	THEN REPEAT strip_tac);
a(rewrite_tac [ℝ_abs_times_thm]);
a(bc_thm_tac ℝ_≤_times_mono_thm THEN rewrite_tac[ℝ_0_≤_abs_thm]);
a(rewrite_tac[ℝ_abs_ℝ_ℕ_exp_thm]);
a(induction_tac⌜m⌝ THEN rewrite_tac[ℝ_ℕ_exp_def]);
a(lemma_tac ⌜Abs x ≤  b⌝ THEN1
	(cases_tac ⌜ℕℝ 0 ≤ x⌝ THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜Abs x * B ^ m⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ℝ_≤_times_mono_thm THEN asm_rewrite_tac[ℝ_0_≤_abs_thm]);
(* *** Goal "2" *** *)
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(bc_thm_tac ℝ_≤_times_mono_thm THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[ℝ_≤_def] THEN ∨_left_tac);
a(bc_thm_tac ℝ_ℕ_exp_0_less_thm THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Formula for the derivatives of partial sums of a power series:
%%%%
%%%%
=SML

val ⦏power_series_deriv_coeffs_thm⦎ = save_thm ( "power_series_deriv_coeffs_thm", (
set_goal([], ⌜
	∀s n x⦁
	(PowerSeries s (n+1) Deriv PowerSeries (λm⦁ℕℝ (m+1)*s(m+1)) n x) x
⌝);
a(rewrite_tac[power_series_series_thm, series_def] THEN REPEAT strip_tac);
a(induction_tac ⌜n⌝ THEN rewrite_tac [series_def]);
(* *** Goal "1" *** *)
a(rewrite_tac[const_deriv_thm]);
(* *** Goal "2" *** *)
a(ho_bc_thm_tac plus_deriv_thm);
a(REPEAT strip_tac);
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜∀a b c:ℝ⦁ (a * b) * c = b * a * c⌝]);
a(rewrite_tac[ℕℝ_plus_homomorphism_thm]);
a(accept_tac (rewrite_rule[const_deriv_thm, ℝ_ℕ_exp_deriv_thm] (
	list_∀_elim[⌜λ x:ℝ⦁ s (n + 1)⌝, ⌜ℕℝ 0⌝, ⌜x⌝, ⌜λx:ℝ⦁x ^ (n + 1)⌝, ⌜(ℕℝ n + ℕℝ 1)* x ^ n⌝] 	
			times_deriv_thm
)));
pop_thm()
));

=TEX
Now lemmas needed in showing the convergence of the sequence of derivatives
of a convergent power series. The first one is the special case where the sequence
is a convergent geometric series:
%%%%
%%%%
=SML

val ⦏power_series_deriv_lemma1⦎ = save_thm ( "power_series_deriv_lemma1", (
set_goal([], ⌜
	∀ b ⦁
	ℕℝ 0 < b ∧ b < ℕℝ 1
⇒	∃c ⦁ Series (λm:ℕ⦁ ℕℝ (m + 1) * b ^ m) -> c
⌝);
a(REPEAT strip_tac THEN bc_thm_tac ratio_test_thm);
a(∃_tac⌜b⌝ THEN asm_rewrite_tac[ℝ_≤_def]);
a(lemma_tac⌜¬ b = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜∀m:ℕ⦁¬ b^m = ℕℝ 0⌝ THEN1
	(strip_tac THEN ALL_FC_T rewrite_tac [ℝ_ℕ_exp_¬_eq_0_thm]));
a(lemma_tac⌜∀m⦁ ¬ ℕℝ (m + 1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(once_rewrite_tac[taut_rule ⌜∀p q⦁p ∧ q ⇔ p ∧ (p ⇒q)⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜¬ b^m = ℕℝ 0⌝ THEN1 asm_rewrite_tac[]);
a(asm_rewrite_tac[ℝ_times_eq_0_thm] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜∀m x⦁ x / (ℕℝ (m + 1) * b ^ m) = x * (ℕℝ (m + 1) * b ^ m) ⋏-⋏1 ⌝
	asm_rewrite_thm_tac THEN1
		(∀_tac THEN bc_thm_tac ℝ_over_times_recip_thm THEN asm_rewrite_tac[]));
a(LEMMA_T⌜∀n⦁ (ℕℝ (n + 1) * b ^ n) ⋏-⋏1  =  ℕℝ (n + 1)⋏-⋏1  *( b ^ n) ⋏-⋏1⌝
	rewrite_thm_tac THEN1
		(REPEAT strip_tac THEN
			(lemma_tac⌜¬ ℕℝ(n+1) = ℕℝ 0 ∧ ¬b ^ n = ℕℝ 0⌝
				THEN1 asm_rewrite_tac[]) THEN
					 all_fc_tac[ ℝ_recip_clauses]));
a(rewrite_tac[ℝ_ℕ_exp_plus_thm, ℝ_times_assoc_thm]);
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b c d e:ℝ⦁a * b * c * d * e = c * a * d * b * e⌝]);
a(LEMMA_T ⌜∀m:ℕ⦁ b^m * (b ^ m) ⋏-⋏1 = ℕℝ 1⌝  rewrite_thm_tac THEN1
	(REPEAT strip_tac 	THEN
		(lemma_tac⌜¬b ^ (m:ℕ) = ℕℝ 0⌝
			THEN1 asm_rewrite_tac[]) THEN
					 all_fc_tac[ ℝ_recip_clauses]));
a(rewrite_tac[ℝ_abs_times_thm]);
a(LEMMA_T⌜Abs b = b⌝ rewrite_thm_tac THEN1
	asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
a(lemma_tac⌜∀m⦁ ℕℝ 0 < ℕℝ(m+1)⋏-⋏1 ⌝  THEN1
	(REPEAT strip_tac THEN
		(lemma_tac⌜ℕℝ 0 < ℕℝ (m+1)⌝
			THEN1 rewrite_tac[ℕℝ_less_thm]) THEN
					 all_fc_tac[ ℝ_0_less_0_less_recip_thm]));
a(asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
a(conv_tac (RIGHT_C(pure_once_rewrite_conv[prove_rule[]⌜b = b * ℕℝ 1⌝])));
a(ho_bc_thm_tac times_lim_seq_thm THEN rewrite_tac[const_lim_seq_thm]);
a(conv_tac (LEFT_C(λ_C(LEFT_C (once_rewrite_conv[ℕℝ_plus_homomorphism_thm])))));
a(rewrite_tac[ℝ_times_plus_distrib_thm]);
a(LEMMA_T⌜∀m⦁ ℕℝ (m + 1) * ℕℝ(m+1) ⋏-⋏1 = ℕℝ 1⌝  rewrite_thm_tac THEN1
	(REPEAT strip_tac THEN
		(lemma_tac⌜¬ℕℝ (m+1) = ℕℝ 0⌝
			THEN1 rewrite_tac[ℕℝ_one_one_thm]) THEN
					 all_fc_tac[ ℝ_recip_clauses]));
a(conv_tac (RIGHT_C(pure_once_rewrite_conv[prove_rule[]⌜ℕℝ 1 = ℕℝ 1 + ℕℝ 0⌝])));
a(ho_bc_thm_tac plus_lim_seq_thm THEN rewrite_tac[
	const_lim_seq_thm,
	rewrite_rule[](∀_elim⌜ℕℝ 0⌝ lim_seq_recip_ℕ_thm)]);
pop_thm()
));

=TEX
Another lemma for the convergence of the derivatives of partial sums of a power series:
this is the special case where the estimate on the radius of convergence is 1, for
which the calculations are rather simpler.

%%%%
%%%%
=SML

val ⦏power_series_deriv_lemma2⦎ = save_thm ( "power_series_deriv_lemma2", (
set_goal([], ⌜
	∀s C b⦁
	ℕℝ 0 < b ∧ b < ℕℝ 1
∧	(λm⦁ PowerSeries (λm⦁Abs(s m)) m (ℕℝ 1)) ->  C
⇒	∃D⦁ (λm⦁ PowerSeries (λm⦁Abs((ℕℝ (m+1))*s (m+1))) m b) -> D
⌝);
a(rewrite_tac[power_series_series_thm] THEN REPEAT strip_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[η_axiom, ℝ_ℕ_exp_0_1_thm]));
a(all_fc_tac[rewrite_rule[](∀_elim⌜ℕℝ 1⌝ lim_series_bounded_thm)]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_abs_abs_thm, ℝ_abs_times_thm]));
a(conv_tac (RAND_C(λ_C (once_rewrite_conv[η_axiom]))));
a(once_rewrite_tac[∀_elim⌜m⌝ lim_series_shift_∃_thm]);
a(all_fc_tac[once_rewrite_rule[∀_elim⌜m⌝ lim_series_shift_∃_thm]power_series_deriv_lemma1]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[] o ∀_elim⌜m⌝));
a(bc_thm_tac comparison_test_thm);
a(∃_tac ⌜x⌝ THEN ∃_tac⌜λ m'⦁ ℕℝ ((m' + m) + 1) * b ^ (m' + m)⌝ );
a(rewrite_tac[]);
a(once_rewrite_tac[ℝ_abs_times_thm] THEN rewrite_tac[ℝ_abs_abs_thm]);
a(rewrite_tac[ℝ_abs_times_thm, ℝ_times_assoc_thm] THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_≤_times_mono_thm THEN rewrite_tac[ℕℝ_≤_thm]);
a(lemma_tac ⌜ℕℝ 0 ≤ b^(m'+m)⌝
		THEN1 (rewrite_tac[ℝ_≤_def] THEN
			ALL_FC_T rewrite_tac[ℝ_ℕ_exp_less_mono_thm]));
a(LEMMA_T ⌜Abs (b^(m'+m)) = b^(m'+m)⌝ rewrite_thm_tac THEN1 asm_rewrite_tac[ℝ_abs_def]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜ℕℝ 1 * b ^ (m' + m)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(pure_once_rewrite_tac[ℝ_times_comm_thm]);
a(bc_thm_tac ℝ_≤_times_mono_thm THEN REPEAT strip_tac);
a(rewrite_tac[ℝ_≤_def] THEN ∨_left_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
The identity for scaling the argument of a power series by a constant factor:
%%%%
%%%%
=SML

val ⦏power_series_scale_arg_thm⦎ = save_thm ( "power_series_scale_arg_thm", (
set_goal([], ⌜∀c s m y⦁
	PowerSeries s m (c * y) = PowerSeries (λ m⦁ s m * c ^ m)  m y
⌝);
a(rewrite_tac[power_series_series_thm, ℝ_ℕ_exp_times_thm, ℝ_times_assoc_thm]);
pop_thm()
));

=TEX
The identity for scaling the coefficients of a power series by a constant factor:
%%%%
%%%%
=SML

val ⦏power_series_scale_coeffs_thm⦎ = save_thm ( "power_series_scale_coeffs_thm", (
set_goal([], ⌜∀c s m y⦁
	PowerSeries (λm⦁c * s m) m y =c * PowerSeries s  m y
⌝);
a(rewrite_tac[power_series_series_thm, ℝ_ℕ_exp_times_thm, ℝ_times_assoc_thm]
	THEN REPEAT strip_tac);
a(pure_rewrite_tac[prove_rule[]⌜ (λ m⦁ c * s m * y ^ m) =  (λ m⦁ c * (λm⦁ s m * y ^ m) m)⌝]);
a(pure_rewrite_tac[const_times_series_thm] THEN rewrite_tac[]);
pop_thm()
));

=TEX
The theorem on the convergence of the derivatives of a power series:

%%%%
%%%%
=SML

val ⦏power_series_deriv_lim_seq_convergence_thm⦎ = save_thm (
	"power_series_deriv_lim_seq_convergence_thm", (
set_goal([], ⌜
	∀s B C b⦁
	ℕℝ 0 < b ∧ b < B
∧	(λm⦁ PowerSeries (λm⦁Abs(s m)) m B) ->  C
⇒	∃D⦁ (λm⦁ PowerSeries (λm⦁Abs((ℕℝ (m+1))*s(m+1))) m b) -> D
⌝);
a(REPEAT strip_tac);
a(swap_nth_asm_concl_tac 1);
a(pure_once_rewrite_tac[prove_rule[]⌜B = B * ℕℝ 1⌝]);
a(pure_rewrite_tac[power_series_scale_arg_thm] THEN rewrite_tac[]);
a(swap_nth_asm_concl_tac 1 THEN REPEAT strip_tac THEN rewrite_tac[]);
a(lemma_tac ⌜ℕℝ 0 < B⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac ⌜∃c⦁ B ⋏-⋏1 * B = ℕℝ 1 ∧ ℕℝ 0 < c ∧ c < ℕℝ 1 ∧ b = B * c⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜B ⋏-⋏1 * b⌝);
a(all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(ALL_FC_T rewrite_tac [ℝ_0_less_0_less_times_thm]);
a(lemma_tac ⌜¬b = ℕℝ 0 ∧ ¬ B ⋏-⋏1 = ℕℝ 0 ∧ ¬B = ℕℝ 0⌝ THEN1
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rewrite_tac[ℝ_times_assoc_thm1] THEN ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[∀_elim⌜B⌝ ℝ_times_mono_⇔_thm]);
a(rewrite_tac[ℝ_times_assoc_thm1] THEN ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(swap_nth_asm_concl_tac 5);
a(lemma_tac ⌜Abs B = B⌝ THEN1 asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
a(lemma_tac ⌜∀m:ℕ⦁Abs(B ^ m) = B ^ m⌝ THEN1
	(strip_tac THEN induction_tac⌜m:ℕ⌝ THEN
		asm_rewrite_tac[ℝ_ℕ_exp_def, ℝ_abs_times_thm]));
a(LEMMA_T ⌜∀m:ℕ⦁Abs(s m) * B ^ m = Abs(s m * B ^ m)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_abs_times_thm]);
a(pure_once_rewrite_tac[prove_rule[]⌜∀m:ℕ⦁ s m * B ^ m = (λm⦁ s m * B ^ m) m⌝]);
a(swap_nth_asm_concl_tac 3 THEN REPEAT strip_tac);
a(all_fc_tac[power_series_deriv_lemma2]);
a(∃_tac⌜B ⋏-⋏1 * D⌝ THEN rewrite_tac[power_series_scale_arg_thm]);
a(swap_nth_asm_concl_tac 1 THEN
	asm_rewrite_tac[ℝ_ℕ_exp_def, ℝ_times_assoc_thm, ℝ_abs_times_thm]);
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c d:ℝ⦁ a * b * c * d = c* a * b * d⌝ ]);
a(pure_once_rewrite_tac[ prove_rule[]⌜∀m⦁
	ℕℝ (m + 1) * Abs(s (m + 1)) * B ^ m = (λm⦁ ℕℝ (m + 1) * Abs(s (m + 1)) * B ^ m) m
⌝]);
a(pure_once_rewrite_tac[power_series_scale_coeffs_thm]);
a(swap_nth_asm_concl_tac 1);
a(LEMMA_T ⌜∀m s⦁PowerSeries s m c = (B ⋏-⋏1 * B) * PowerSeries s m c⌝ once_rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a(rewrite_tac[ℝ_times_assoc_thm, ℝ_abs_times_thm]);
a(ho_bc_thm_tac times_lim_seq_thm THEN asm_rewrite_tac[const_lim_seq_thm]);
pop_thm()
));

=TEX
Uniform convergence of power series:
%%%%
%%%%
=SML

val ⦏power_series_deriv_convergence_thm⦎ = save_thm ( "power_series_deriv_convergence_thm", (
set_goal([], ⌜
	∀s B C b⦁
	ℕℝ 0 < B ∧ ℕℝ 0 < b ∧ b < B
∧	(λm⦁ PowerSeries (λm⦁Abs(s m)) m B) ->  C
⇒	∃df⦁ (PowerSeries (λm⦁(ℕℝ (m+1))*s(m+1)) ---> df) (OpenInterval (~b) b)
⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜∃B1⦁ ℕℝ 0 < B1 ∧ b < B1 ∧ B1 <  B⌝ THEN1
	(∃_tac⌜(1/2)*(B + b) ⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(DROP_NTH_ASM_T 5 discard_tac THEN all_fc_tac[power_series_deriv_lim_seq_convergence_thm]);
a(POP_ASM_T ante_tac);
a(pure_once_rewrite_tac[ prove_rule[]⌜
	(λ m⦁ Abs(ℕℝ (m + 1) * s (m + 1))) =(λ m⦁ Abs((λm⦁ ℕℝ (m + 1) * s (m + 1))m))
⌝] THEN strip_tac);
a(DROP_NTH_ASM_T 5 discard_tac THEN all_fc_tac[power_series_convergence_thm]);
a(∃_tac⌜f⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
The main theorem on power series: if a power series is absolutely convergent for
some positive value $B$ of its argument, then for any positive
$b < B$, it is uniformly convergent to a limit $f$ on any open interval $(-b, b)$
and $f$ is differential on that open interval with derivative given by the (uniformly
convergent) limit of the derivatives of the partial sums of the series:
%%%%
%%%%
=SML

val ⦏power_series_main_thm⦎ = save_thm ( "power_series_main_thm", (
set_goal([], ⌜
	∀s B C b⦁
	ℕℝ 0 < b ∧ b < B
∧	(λm⦁ PowerSeries (λm⦁Abs(s m)) m B) ->  C
⇒	∃f df⦁
	(PowerSeries s ---> f) (OpenInterval (~b) b)
∧	(PowerSeries (λm⦁(ℕℝ (m+1))*s(m+1)) ---> df) (OpenInterval (~b) b)
∧	(∀y⦁ y ∈ OpenInterval (~b) b ⇒ (f Deriv df y) y)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < B⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[power_series_convergence_thm, power_series_deriv_convergence_thm]);
a(∃_tac⌜f⌝ THEN ∃_tac⌜df⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 ∈ OpenInterval (~b) b⌝ THEN1
	(rewrite_tac[open_interval_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜∃g⦁ (PowerSeries s ---> g) (OpenInterval (~b) b) ∧
	(∀y⦁ y ∈ OpenInterval (~b) b ⇒ (g Deriv df y) y)⌝);
(* *** Goal "1" *** *)
a(once_rewrite_tac[∀_elim⌜1⌝ unif_lim_seq_shift_thm]);
a(bc_thm_tac unif_lim_seq_deriv_thm);
a(∃_tac⌜f(ℕℝ 0)⌝ THEN ∃_tac⌜ℕℝ 0⌝ THEN ∃_tac⌜PowerSeries (λ m⦁ ℕℝ (m + 1) * s (m + 1))⌝);
a(REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(rewrite_tac[power_series_deriv_coeffs_thm]);
(* *** Goal "1.2" *** *)
a(bc_thm_tac unif_lim_seq_pointwise_lim_seq_thm);
a(∃_tac⌜OpenInterval (~b) b⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (ante_tac o once_rewrite_rule[∀_elim⌜1⌝ unif_lim_seq_shift_thm]));
a(rewrite_tac[]);
(* *** Goal "2" *** *)
a(bc_thm_tac deriv_local_thm);
a(∃_tac⌜g⌝ THEN ∃_tac⌜b⌝ THEN ∃_tac⌜~b⌝ THEN rewrite_tac[
	prove_rule[open_interval_def] ⌜∀A B Y⦁A < Y ∧ Y <  B ⇔ Y ∈ OpenInterval A  B⌝]);
a(GET_NTH_ASM_T 4 (rewrite_thm_tac o rewrite_rule[open_interval_def]));
a(LIST_GET_NTH_ASM_T [1] (ALL_FC_T rewrite_tac));
a(REPEAT strip_tac THEN bc_thm_tac unif_lim_seq_unique_thm);
a(∃_tac⌜OpenInterval (~b) b⌝ THEN ∃_tac⌜PowerSeries s⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The main theorem has the following useful consequences for power series that
are convergent for all positive values of their argument. Thefirst consequence
gives information about uniform convergence:
%%%%
%%%%
=SML

val ⦏power_series_main_thm1⦎ = save_thm ( "power_series_main_thm1", (
set_goal([], ⌜
	∀s b⦁
	ℕℝ 0 <  b
∧	(∀x⦁ ℕℝ 0 < x ⇒ ∃c⦁ (λm⦁ PowerSeries (λm⦁Abs(s m)) m x) ->  c)
⇒	∃f df⦁
	(PowerSeries s ---> f) (OpenInterval (~b) b)
∧	(PowerSeries (λm⦁(ℕℝ (m+1))*s(m+1)) ---> df) (OpenInterval (~b) b)
∧	(∀y⦁ y ∈ OpenInterval (~b) b ⇒ (f Deriv df y) y)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃B⦁b < B ∧ℕℝ 0 < B⌝ THEN1
	(∃_tac⌜b + b⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜B⌝));
a(all_fc_tac[power_series_main_thm]);
a(∃_tac⌜f⌝ THEN ∃_tac⌜df⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
The second consequence of the main theorem just gives information about pointwise convergence.
It is just what is wanted to justify definitions of functions by differential equation like
that of the exponential function.
%%%%
%%%%
=SML

val ⦏power_series_main_thm2⦎ = save_thm ( "power_series_main_thm2", (
set_goal([], ⌜
	∀s⦁
	(∀x⦁ ℕℝ 0 < x ⇒ ∃c⦁ (λm⦁ PowerSeries (λm⦁Abs(s m)) m x) ->  c)
⇒	∃f df⦁
	(∀x⦁ (λm⦁PowerSeries s m x) ->  f x)
∧	(∀x⦁ (λm⦁PowerSeries (λm⦁(ℕℝ (m+1))*s(m+1)) m x) ->  df x) 
∧	(∀x⦁ (f Deriv df x) x)
∧	f (ℕℝ 0) = s 0
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀z⦁∃b⦁ℕℝ 0 < b ∧ z ∈ OpenInterval (~b) b⌝ THEN1
	(strip_tac THEN ∃_tac⌜Abs z + ℕℝ 1⌝ THEN cases_tac⌜ℕℝ 0 ≤ z⌝ THEN
		asm_rewrite_tac[ℝ_abs_def, open_interval_def] THEN
			PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜(∃f⦁∀y⦁ (λm⦁ PowerSeries s m y) -> f y)
∧	(∃df⦁ ∀y⦁ (λm⦁PowerSeries (λm⦁(ℕℝ (m+1))*s(m+1)) m y) ->  df y) 
⌝ THEN1 (REPEAT strip_tac THEN prove_∃_tac THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a(spec_nth_asm_tac 1 ⌜y'⌝  THEN all_asm_fc_tac[power_series_main_thm1]);
a(∃_tac⌜f y'⌝ );
a(all_fc_tac[ unif_lim_seq_pointwise_lim_seq_thm]);
(* *** Goal "2" *** *)
a(spec_nth_asm_tac 1 ⌜y'⌝  THEN all_asm_fc_tac[power_series_main_thm1]);
a(∃_tac⌜df y'⌝ );
a(all_fc_tac[ unif_lim_seq_pointwise_lim_seq_thm]);
(* *** Goal "3" *** *)
a(∃_tac⌜f⌝ THEN ∃_tac⌜df⌝ THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3.2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3.3" *** *)
a(spec_nth_asm_tac 3  ⌜x⌝  THEN all_asm_fc_tac[power_series_main_thm1]);
a(bc_thm_tac deriv_local_thm);
a(∃_tac⌜f'⌝ THEN ∃_tac⌜b⌝ THEN ∃_tac⌜~b⌝ THEN rewrite_tac[
	prove_rule[open_interval_def] ⌜∀A B Y⦁A < Y ∧ Y <  B ⇔ Y ∈ OpenInterval A  B⌝]);
a(GET_NTH_ASM_T 5 (rewrite_thm_tac o rewrite_rule[open_interval_def]));
a(REPEAT strip_tac);
(* *** Goal "3.3.1" *** *)
a(conv_tac eq_sym_conv THEN bc_thm_tac unif_lim_seq_pointwise_unique_thm);
a(∃_tac⌜OpenInterval(~b) b⌝ THEN ∃_tac⌜PowerSeries s⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3.3.2" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(LEMMA_T ⌜df x = df' x⌝ asm_rewrite_thm_tac);
a(conv_tac eq_sym_conv THEN bc_thm_tac unif_lim_seq_pointwise_unique_thm);
a(∃_tac⌜OpenInterval(~b) b⌝ THEN
	∃_tac⌜PowerSeries  (λ m⦁ ℕℝ (m + 1) * s (m + 1))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3.4" *** *)
a(POP_ASM_T discard_tac THEN POP_ASM_T (strip_asm_tac o ∀_elim⌜ℕℝ 0⌝));
a(strip_asm_tac (∀_elim⌜s⌝ power_series_limit_0_thm));
a(all_fc_tac[lim_seq_unique_thm]);
pop_thm()
));

=TEX
The third consequence of the main theorem gives information about pointwise convergence
and the first and second derivatives as needed for the sine and cosine function:
%%%%
%%%%
=SML

val ⦏power_series_main_thm3⦎ = save_thm ( "power_series_main_thm3", (
set_goal([], ⌜
	∀s⦁
	(∀x⦁ ℕℝ 0 < x ⇒ ∃c⦁ (λm⦁ PowerSeries (λm⦁Abs(s m)) m x) ->  c)
⇒	∃f d1f d2f⦁
	(∀x⦁ (λm⦁PowerSeries s m x) ->  f x)
∧	(∀x⦁ (λm⦁PowerSeries (λm⦁ℕℝ (m+1) *s(m+1)) m x) ->  d1f x) 
∧	(∀x⦁ (λm⦁PowerSeries (λm⦁ℕℝ(m+1) * ℕℝ (m+2)*s(m+2)) m x) ->  d2f x) 
∧	(∀x⦁ (f Deriv d1f x) x)
∧	(∀x⦁ (d1f Deriv d2f x) x)
∧	f (ℕℝ 0) = s 0
∧	d1f (ℕℝ 0) = s 1
⌝);
a(REPEAT strip_tac);
a(lemma_tac (
	subst [(⌜(λm⦁(ℕℝ (m+1))*s(m+1))⌝, ⌜s⌝)]
		 ⌜∀x⦁ ℕℝ 0 < x ⇒ ∃c⦁ (λm⦁ PowerSeries (λm⦁Abs(s m)) m x) ->  c⌝));
(* *** Goal "1" *** *)
a(rewrite_tac[] THEN REPEAT strip_tac);
a(bc_thm_tac power_series_deriv_lim_seq_convergence_thm);
a(lemma_tac⌜ℕℝ 0 < x + ℕℝ 1⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 rewrite_thm_tac THEN all_asm_fc_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜c⌝ THEN ∃_tac⌜x + ℕℝ 1⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(all_fc_tac[power_series_main_thm2]);
a(LIST_DROP_NTH_ASM_T [9, 10] discard_tac);
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[])
	THEN rename_tac[(⌜f⌝, "d1f"), (⌜f'⌝, "f"), (⌜df⌝, "d2f")]);
a(DROP_NTH_ASM_T 7 (strip_asm_tac o rewrite_rule[plus_assoc_thm]));
a(∃_tac⌜f⌝ THEN ∃_tac⌜d1f⌝ THEN ∃_tac⌜d2f⌝ THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜d1f = df' ⌝ asm_rewrite_thm_tac THEN REPEAT strip_tac);
a(spec_nth_asm_tac 5 ⌜x⌝);
a(spec_nth_asm_tac 9 ⌜x⌝);
a(all_fc_tac[lim_seq_unique_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
%%%%
\subsection{Some Special Functions}
=TEX
We begin our investigation of the exponential function by proving a (very) few elementary
properties of the factorial function. 
All we need to know really is that it is always positive and that the ratio $m!/(m+1)!$
is $1/(m+1$.The following lemma gives a weak lower bound on the growth of the
factorial function and shows that is always positive.
%%%%
%%%%
=SML

val ⦏factorial_linear_estimate_thm⦎ = save_thm ( "factorial_linear_estimate_thm", (
set_goal([], ⌜∀m⦁ ℕℝ 1 ≤ ℕℝ (m!) ∧ ℕℝ m ≤ ℕℝ (m!)⌝);
a(REPEAT ∀_tac THEN induction_tac⌜m:ℕ⌝ THEN asm_rewrite_tac[factorial_def]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac ⌜ℕℝ (m!)⌝ THEN REPEAT strip_tac);
a(rewrite_tac[ℕℝ_times_homomorphism_thm]);
a(conv_tac(LEFT_C(pure_once_rewrite_conv [prove_rule[]⌜ℕℝ (m!) = ℕℝ 1 * ℕℝ (m!)⌝])));
a(pure_once_rewrite_tac[ℝ_times_comm_thm]);
a(bc_thm_tac ℝ_≤_times_mono_thm);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rewrite_tac[ℝ_≤_def, ℕℝ_less_thm, ℕℝ_one_one_thm]);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[ℕℝ_times_homomorphism_thm]);
a(conv_tac(LEFT_C(pure_once_rewrite_conv [prove_rule[]⌜∀x⦁ x = x * ℕℝ 1⌝])));
a(bc_thm_tac ℝ_≤_times_mono_thm THEN REPEAT strip_tac);
a(rewrite_tac[ℝ_≤_def, ℕℝ_less_thm, ℕℝ_one_one_thm]);
pop_thm()
));

=TEX

The next lemma says explicitly that factorials are always positive:
%%%%
%%%%
=SML

val ⦏factorial_0_less_thm⦎ = save_thm ( "factorial_0_less_thm", (
set_goal([], ⌜∀m⦁ ℕℝ 0 < ℕℝ (m!) ⌝);
a(REPEAT strip_tac THEN bc_thm_tac ℝ_less_≤_trans_thm
	THEN ∃_tac⌜ℕℝ 1⌝ THEN rewrite_tac [factorial_linear_estimate_thm]
	THEN REPEAT strip_tac);
pop_thm()
));

=TEX
The following lemma is the one that will show that the exponential function
is its own derivative:
%%%%
%%%%
=SML

val ⦏factorial_times_recip_thm⦎ = save_thm ( "factorial_times_recip_thm", (
set_goal([], ⌜∀m⦁ ℕℝ (m + 1) * ℕℝ ((m + 1) !) ⋏-⋏1 = ℕℝ (m!) ⋏-⋏1⌝);
a(REPEAT strip_tac THEN rewrite_tac[factorial_def,
	ℕℝ_times_homomorphism_thm]);
a(strip_asm_tac (∀_elim⌜m⌝ factorial_0_less_thm));
a(lemma_tac⌜¬ ℕℝ (m+1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(ALL_FC_T (MAP_EVERY (strip_asm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)))
	[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁a < b ⇒ ¬a = b⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(rewrite_tac[ℝ_times_assoc_thm1]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML

val ⦏gen_rolle_thm⦎ = save_thm ( "gen_rolle_thm", (
set_goal([], ⌜∀n D a b⦁
	a < b
∧	(∀m x⦁ m ≤ n ∧ a ≤ x ∧ x ≤ b ⇒ D m Cts x)
∧	(∀m x⦁ m ≤ n ∧ a < x ∧ x < b ⇒ (D m Deriv D(m+1) x) x)
∧	(∀m⦁ m ≤ n ⇒ D m a = ℕℝ 0)
∧	D 0 b = ℕℝ 0
⇒	∃x⦁ a < x ∧ x < b ∧ D (n+1) x = ℕℝ 0
⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜∀k⦁k ≤ n ⇒ ∃x⦁ a < x ∧ x < b ∧ D (k+1) x = ℕℝ 0⌝
	bc_thm_tac THEN strip_tac);
a(induction_tac⌜k⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜∃ x⦁ a < x ∧ x < b ∧ (D 0 Deriv ℕℝ 0) x⌝
	THEN1 bc_thm_tac rolle_thm);
(* *** Goal "1.1" *** *)
a(∃_tac⌜D 1⌝ THEN asm_rewrite_tac[]);
a(LIST_GET_NTH_ASM_T [2, 3, 4]
	 (rewrite_tac o map (rewrite_rule[] o ∀_elim⌜0⌝)));
(* *** Goal "1.2" *** *)
a(∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a(LEMMA_T⌜(D 0 Deriv D(0+1) x) x⌝ (strip_asm_tac o rewrite_rule[])
	THEN1 (DROP_NTH_ASM_T 6 bc_thm_tac THEN asm_rewrite_tac[]));
a(all_fc_tac[deriv_unique_thm]);
(* *** Goal "2" *** *)
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜∃ y⦁ a < y ∧ y < x ∧ (D (k+1) Deriv ℕℝ 0) y⌝
	THEN1 bc_thm_tac rolle_thm);
(* *** Goal "3.1" *** *)
a(∃_tac⌜D ((k+1)+1)⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "3.1.1" *** *)
a(DROP_NTH_ASM_T 10 bc_thm_tac
	THEN REPEAT strip_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.1.2" *** *)
a(DROP_NTH_ASM_T 9 bc_thm_tac
	THEN REPEAT strip_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.1.3" *** *)
a(DROP_NTH_ASM_T 6 bc_thm_tac
	THEN REPEAT strip_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.2" *** *)
a(∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜(D (k+1) Deriv D((k+1)+1) y) y⌝
	THEN1 (DROP_NTH_ASM_T 10 bc_thm_tac THEN asm_rewrite_tac[]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[deriv_unique_thm]);
pop_thm()
));

=TEX
%%%%
%%%%

=SML
set_goal([], ⌜∀n D a b⦁
	a < b
∧	(∀m x⦁ m ≤ n ∧ a ≤ x ∧ x ≤ b ⇒ D m Cts x)
∧	(∀m x⦁ m ≤ n ∧ a < x ∧ x < b ⇒ (D m Deriv D(m+1) x) x)
∧	(∀m⦁ m ≤ n ⇒ D m a = ℕℝ 0)
⇒	∃x⦁ a < x ∧ x < b
∧	D 0 b = D (n+1) x * (b - a) ^ (n+1) * ℕℝ ((n+1) !) ⋏-⋏1
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃G⦁∀m x⦁
	G m = λx⦁
	D 0 b * (x + ~a) ^ ((n+1)-m) * ℕℝ (((n+1)-m) !) ⋏-⋏1
	+ ~(D m x) * (b + ~a) ^ (n+1) * ℕℝ ((n+1) !) ⋏-⋏1⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∃ x⦁ a < x ∧ x < b ∧ G (n + 1) x = ℕℝ 0⌝);
(* *** Goal "1" *** *)
a(bc_thm_tac gen_rolle_thm THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(asm_rewrite_tac[]);
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
(* *** Goal "1.2" *** *)
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 (strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(m + i) + 1 = i + (m + 1)⌝]);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜i + (m + 1) = (i+1)+m⌝]);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(i+1)+m = (m+i)+1⌝]);
a(RAT_DERIV_T (ante_tac o ∀_elim⌜D(m+1)x⌝));
a(REPEAT (conv_tac(ONCE_MAP_C ℝ_anf_conv)));
a(asm_rewrite_tac[]);
a(bc_thm_tac(prove_rule[]⌜∀f a b⦁a = b ⇒ (f Deriv a) x ⇒ (f Deriv b) x⌝));
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀a y z:ℝ⦁ a * y + y + z = (a + ℕℝ 1)*y +z⌝,
	ℕℝ_plus_homomorphism_thm1]);
a(rewrite_tac[ℝ_times_assoc_thm1,
	factorial_times_recip_thm]);
(* *** Goal "1.3" *** *)
a(LIST_DROP_NTH_ASM_T [3] (ALL_FC_T asm_rewrite_tac));
a(POP_ASM_T(strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(m + i) + 1 = (i + 1) + m⌝,
	ℝ_ℕ_exp_0_1_thm]);
(* *** Goal "1.4" *** *)
a(asm_rewrite_tac[]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN strip_tac);
(* *** Goal "2" *** *)
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[factorial_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
val ⦏taylor_lemma1⦎ = pop_thm();
=TEX
%%%%
%%%%

=SML

val ⦏taylor_thm⦎ = save_thm ( "taylor_thm", (
set_goal([], ⌜∀n f D a b⦁
	a < b
∧	D 0 = f
∧	(∀ m x⦁ m ≤ n ∧ a ≤ x ∧ x ≤ b ⇒ D m Cts x)
∧	(∀ m x⦁ m ≤ n ∧ a < x ∧ x < b ⇒ (D m Deriv D (m + 1) x) x)
⇒	∃x⦁ a < x ∧ x < b
∧	f b =
	PowerSeries (λm⦁ D m a * ℕℝ(m!)⋏-⋏1) (n+1) (b-a) +
	D (n+1) x * (b-a) ^ (n+1) * ℕℝ((n+1)!)⋏-⋏1
⌝);
a(PC_T1 "predicates" REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(lemma_tac⌜∃G⦁∀m⦁
	G m = λx⦁
	D m x - PowerSeries (λk⦁ D (k+m) a * ℕℝ(k!)⋏-⋏1) ((n+1)-m) (x-a)⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∃ x⦁ a < x ∧ x < b ∧
	G 0 b = G (n+1) x * (b-a) ^ (n+1)* ℕℝ ((n+1) !) ⋏-⋏1⌝);
(* *** Goal "1" *** *)
a(bc_thm_tac taylor_lemma1 THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(LIST_DROP_NTH_ASM_T[6] all_fc_tac);
a(asm_rewrite_tac[]);
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(ho_bc_thm_tac (all_∀_intro(∀_elim⌜PowerSeries f i⌝ comp_cts_thm)));
a(REPEAT strip_tac
	THEN REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(bc_thm_tac poly_cts_thm);
a(rewrite_tac[power_series_def, poly_func_eq_poly_eval_thm]);
a(∃_tac⌜((λ k⦁ D (k + m) a * ℕℝ (k !) ⋏-⋏1) To ((n + 1) - m))⌝
	THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 4 (strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(m + i) + 1 = (i + 1) + m⌝]);
a(DERIV_T (power_series_deriv_coeffs_thm::rat_deriv_thms)
	(ante_tac o ∀_elim⌜D(m+1)x⌝));
a(asm_rewrite_tac[]);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(i + 1) + m = i + (m + 1)⌝]);
a(REPEAT (conv_tac(ONCE_MAP_C ℝ_anf_conv)));
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜∀m'⦁(m' + 1) + m = m' + m + 1⌝,
	pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀x y z:ℝ⦁ x * y * z = (y * x) * z⌝,
	factorial_times_recip_thm]);
(* *** Goal "1.3" *** *)
a(asm_rewrite_tac[]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1"lin_arith" prove_rule[]
	⌜(m + i) + 1 = (i + 1) + m⌝,
	power_series_0_arg_thm,
	factorial_def]);
(* *** Goal "1.4" *** *)
a(∃_tac⌜x⌝ THEN POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a(rewrite_tac[power_series_series_thm, series_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
We can now show using the ratio test and some calculations that the usual series
for the exponential converges for all positive arguments:
%%%%
%%%%
=SML

val ⦏exp_series_convergence_thm⦎ = save_thm ( "exp_series_convergence_thm", (
set_goal([], ⌜∀x⦁
	ℕℝ 0 < x
⇒	∃c⦁ (λm⦁ PowerSeries (λm⦁ Abs(ℕℝ(m!) ⋏-⋏1)) m x) -> c
⌝);
a(rewrite_tac [power_series_series_thm] THEN REPEAT strip_tac);
a(conv_tac(BINDER_C (rewrite_conv[η_axiom])));
a(bc_thm_tac ratio_test_thm);
a(strip_asm_tac factorial_0_less_thm);
a(lemma_tac⌜∀m⦁ℕℝ 0 < ℕℝ(m!) ⋏-⋏1 ⌝ THEN1
	(strip_tac THEN bc_thm_tac ℝ_0_less_0_less_recip_thm
		THEN rewrite_tac[factorial_0_less_thm]));
a(lemma_tac⌜∀m⦁Abs(ℕℝ(m!) ⋏-⋏1) = ℕℝ(m!) ⋏-⋏1 ⌝ THEN1
	(asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]));
a(lemma_tac⌜∀m:ℕ⦁ℕℝ 0 < x ^ m ⌝ THEN1
	(strip_tac THEN bc_thm_tac ℝ_ℕ_exp_0_less_thm THEN REPEAT strip_tac));
a(lemma_tac⌜∀m⦁ℕℝ 0 < Abs(ℕℝ(m!) ⋏-⋏1) * x ^ m ⌝ THEN1
	(strip_tac THEN bc_thm_tac ℝ_0_less_0_less_times_thm THEN asm_rewrite_tac[]));
a(∃_tac⌜ℕℝ 0⌝ THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(POP_ASM_T (ante_tac o ∀_elim⌜m⌝) THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith"  prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a(LEMMA_T⌜∀m y⦁y/ (ℕℝ(m!) ⋏-⋏1 * x ^ m) = y *  (ℕℝ(m!) ⋏-⋏1 * x ^ m)⋏-⋏1⌝  rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜m⌝);
a(lemma_tac ⌜¬ ℕℝ(m !) ⋏-⋏1 * x ^ m = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rename_tac[(⌜x⌝, "xx")] THEN ALL_FC_T rewrite_tac[ℝ_over_times_recip_thm]);
(* *** Goal "2.2" *** *)
a(asm_rewrite_tac[ℝ_abs_times_thm]);
a(LEMMA_T⌜∀m⦁(ℕℝ(m !) ⋏-⋏1 * x ^ m) ⋏-⋏1 = ℕℝ(m !) * (x ^ m) ⋏-⋏1⌝  rewrite_thm_tac);
(* *** Goal "2.2.1" *** *)
a(REPEAT strip_tac);
a(spec_nth_asm_tac 5 ⌜m⌝);
a(spec_nth_asm_tac 5 ⌜m⌝);
a(spec_nth_asm_tac 4 ⌜m⌝);
a(ALL_FC_T (MAP_EVERY (strip_asm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)))
	[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁a < b ⇒ ¬a = b⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2.2.2" *** *)
a(asm_rewrite_tac[ℝ_abs_times_thm, ℝ_abs_ℝ_ℕ_exp_thm]);
a(lemma_tac⌜∀m:ℕ⦁ℕℝ 0 < (x ^ m) ⋏-⋏1⌝  THEN1
	(strip_tac THEN bc_thm_tac ℝ_0_less_0_less_recip_thm THEN asm_rewrite_tac[]));
a(asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def, factorial_0_less_thm]);
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b c d:ℝ⦁(a * b) * c * d = a * c * b * d⌝]);
a(rewrite_tac[ℝ_ℕ_exp_def, factorial_def,
	ℕℝ_times_homomorphism_thm]);
a(LEMMA_T⌜∀m⦁(ℕℝ(m+1) * ℕℝ(m !)) ⋏-⋏1 =ℕℝ (m+1)  ⋏-⋏1 * ℕℝ(m!) ⋏-⋏1⌝  rewrite_thm_tac);
(* *** Goal "2.2.2.1" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜¬ℕℝ(m+1) = ℕℝ 0⌝ THEN1 rewrite_tac[ℕℝ_one_one_thm]);
a(spec_nth_asm_tac 7 ⌜m⌝);
a(ALL_FC_T (MAP_EVERY (strip_asm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)))
	[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁a < b ⇒ ¬a = b⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2.2.2.2" *** *)
a(rewrite_tac[ℝ_times_assoc_thm]);
a(LEMMA_T⌜∀m:ℕ⦁x ^ m * (x ^ m) ⋏-⋏1 = ℕℝ 1⌝  rewrite_thm_tac);
(* *** Goal "2.2.2.2.1" *** *)
a(REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜m⌝);
a(ALL_FC_T (MAP_EVERY (strip_asm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)))
	[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁a < b ⇒ ¬a = b⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2.2.2.2.2" *** *)
a(once_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b c d:ℝ⦁a * b * c * d = a * d * b * c⌝]);
a(LEMMA_T⌜∀m⦁ℕℝ(m !) ⋏-⋏1 * ℕℝ(m !) = ℕℝ 1⌝  rewrite_thm_tac);
(* *** Goal "2.2.2.2.2.1" *** *)
a(REPEAT strip_tac);
a(spec_nth_asm_tac 6 ⌜m⌝);
a(ALL_FC_T (MAP_EVERY (strip_asm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)))
	[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁a < b ⇒ ¬a = b⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2.2.2.2.2.2" *** *)
a(pure_once_rewrite_tac[prove_rule[]⌜ℕℝ 0 = ℕℝ 0 * x⌝]);
a(ho_bc_thm_tac times_lim_seq_thm THEN rewrite_tac[const_lim_seq_thm]);
a(rewrite_tac[rewrite_rule[](∀_elim⌜ℕℝ 0⌝ lim_seq_recip_ℕ_thm)]);
pop_thm()
));

=TEX
The main theorem justifying the consistency of the definition by the differential equation
of the exponential function. We add in the fact that the function whose existence 
is asserted is equal to the limit of the usual power series. This is not relevant
for proving the consistency of the definition but is used later to show that the
exponential function is equal to the power series (the alternative would be to
have packaged this claim in the specification of the exponential function).SS
%%%%
%%%%

=SML

val ⦏exp_consistency_thm⦎ = save_thm ( "exp_consistency_thm", (
set_goal([], ⌜
	∃f⦁
	(∀y⦁ (f Deriv f y) y)
∧	f (ℕℝ 0) = ℕℝ 1
∧	(∀ x⦁ (λ m⦁ PowerSeries (λ m⦁ ℕℝ(m !) ⋏-⋏1) m x) -> f x)
⌝);
a(ante_tac exp_series_convergence_thm);
a(pure_once_rewrite_tac[prove_rule[]⌜∀m⦁ ℕℝ(m !) ⋏-⋏1 = (λm⦁ ℕℝ(m !) ⋏-⋏1) m⌝]);
a(strip_tac THEN all_fc_tac[power_series_main_thm2]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[factorial_def]));
a(DROP_NTH_ASM_T 3 ante_tac);
a(rewrite_tac[factorial_times_recip_thm] THEN REPEAT strip_tac);
a(∃_tac⌜f⌝  THEN asm_rewrite_tac[]);
a(∀_tac THEN LEMMA_T⌜f y = df y⌝ asm_rewrite_thm_tac);
a(bc_thm_tac lim_seq_unique_thm);
a(∃_tac⌜ (λ m⦁ PowerSeries (λ m⦁ ℕℝ(m !) ⋏-⋏1) m y)⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX

Et, voil\'a!
%%%%
%%%%
=TEX
=SML
push_consistency_goal⌜Exp⌝;
a(strip_asm_tac exp_consistency_thm);
a(∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
val _ = save_consistency_thm ⌜Exp⌝ (pop_thm());

val ⦏exp_def⦎ = save_thm("exp_def", get_spec⌜Exp⌝);
=TEX

The following property will be used to show, for example, that the exponential function
is equal to the usual power series expansion.
%%%%
%%%%

=SML

val ⦏exp_unique_thm⦎ = save_thm ( "exp_unique_thm", (
set_goal([], ⌜
	∀f g a b t⦁
	(∀x⦁ x ∈ OpenInterval a b ⇒ ¬f x = ℕℝ 0)
∧	(∀x⦁ x ∈ OpenInterval a b ⇒ (f Deriv f x) x)
∧	(∀x⦁ x ∈ OpenInterval a b ⇒ (g Deriv g x) x)
∧	t ∈ OpenInterval a b
⇒	(∀x⦁ x ∈ OpenInterval a b ⇒ g x = g t * f t ⋏-⋏1 * f x)
⌝);
a(rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
a(lemma_tac⌜∀y⦁ a < y ∧ y < b ⇒ ((λy⦁g y * f y ⋏-⋏1) Deriv ℕℝ 0) y⌝);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [1, 2, 3, 4] discard_tac);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 (strip_asm_tac o ∀_elim⌜y⌝));
a(DROP_NTH_ASM_T 5 (strip_asm_tac o ∀_elim⌜y⌝));
a(all_fc_tac[ recip_comp_deriv_thm]);
a(DROP_NTH_ASM_T 6 (strip_asm_tac o ∀_elim⌜y⌝));
a(LEMMA_T⌜
	((λ y⦁ g y * f y ⋏-⋏1) Deriv
		g y * f y ⋏-⋏1 + g y * ~ (f y ⋏-⋏1 * f y ⋏-⋏1) * f y)  y⌝  ante_tac THEN1
	(ALL_FC_T (MAP_EVERY ante_tac)[times_deriv_thm] THEN rewrite_tac[] THEN taut_tac));
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c d:ℝ⦁a * ~(b * c) * d = ~(a * b * c * d)⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [2, 3] (MAP_EVERY ante_tac));
a(ALL_FC_T (MAP_EVERY (strip_asm_tac o rewrite_rule[])) [deriv_0_thm]);
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(all_var_elim_asm_tac1);
a(asm_rewrite_tac[ℝ_times_assoc_thm1]);
a(rewrite_tac[ℝ_times_assoc_thm]);
a(all_asm_fc_tac[] THEN ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
We now develop some basic properties of the exponential function.

The exponential function is continuous everywhere
%%%%
%%%%

=SML

val ⦏exp_cts_thm⦎ = save_thm ( "exp_cts_thm", (
set_goal([], ⌜ ∀x⦁ Exp Cts x⌝);
a(REPEAT strip_tac THEN bc_thm_tac deriv_cts_thm);
a(∃_tac ⌜Exp x⌝ THEN rewrite_tac[exp_def]);
pop_thm()
));

=TEX

The following lemma is key in showing the main algebraic properties of the exponential function. 
%%%%
%%%%

=SML
set_goal([], ⌜ ∀x y⦁Exp (x + y) * Exp(~x) = Exp y⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀x⦁ ((λx⦁ Exp (x + y) * Exp(~x)) Deriv ℕℝ 0) x⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DERIV_T (∧_right_elim exp_def::rat_deriv_thms) ante_tac
	THEN conv_tac (ONCE_MAP_C ℝ_anf_conv)
	THEN taut_tac);
(* *** Goal "2" *** *)
a(all_fc_tac[deriv_0_thm2]
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac[]);
a(STRIP_T (ante_tac o list_∀_elim[⌜x⌝, ⌜ℕℝ 0⌝]));
a(rewrite_tac[exp_def]);
val ⦏exp_plus_lemma⦎ = pop_thm();
=TEX

The exponential function is never zero. 
%%%%
%%%%

=SML

val ⦏exp_¬_eq_0_thm⦎ = save_thm ( "exp_¬_eq_0_thm", (
set_goal([], ⌜ ∀x⦁¬Exp x = ℕℝ 0⌝);
a(contr_tac);
a(ante_tac(list_∀_elim[⌜x⌝, ⌜ℕℝ 0⌝] exp_plus_lemma) THEN asm_rewrite_tac[exp_def]);
pop_thm()
));

=TEX

The exponential function maps negation to reciprocal:
%%%%
%%%%

=SML

val ⦏exp_minus_thm⦎ = save_thm ( "exp_minus_thm", (
set_goal([], ⌜∀x⦁ Exp (~x) = Exp x ⋏-⋏1⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜¬Exp x = ℕℝ 0⌝ THEN1 rewrite_tac[exp_¬_eq_0_thm]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[
	conv_rule(ONCE_MAP_C(RIGHT_C eq_sym_conv))ℝ_times_cancel_thm]);
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(ante_tac(list_∀_elim[⌜x⌝, ⌜ℕℝ 0⌝] exp_plus_lemma));
a(rewrite_tac[exp_def]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX

The exponential function is always positive:
%%%%
%%%%

=SML

val ⦏exp_0_less_thm⦎ = save_thm ( "exp_0_less_thm", (
set_goal([], ⌜ ∀x⦁ ℕℝ 0 < Exp x⌝);
a(REPEAT strip_tac THEN cases_tac⌜ℕℝ 0 ≤ x⌝);
(* *** Goal "1" *** *)
a(cases_tac⌜x = ℕℝ 0⌝ THEN1 asm_rewrite_tac[exp_def]);
a(contr_tac THEN lemma_tac⌜ℕℝ 0 < x⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN lemma_tac⌜¬Exp x = ℕℝ 0⌝
	THEN1 rewrite_tac[exp_¬_eq_0_thm]
	THEN lemma_tac⌜Exp x < ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ante_tac (list_∀_elim[⌜Exp⌝, ⌜ℕℝ 0⌝, ⌜x⌝]
	intermediate_value_thm));
a(asm_rewrite_tac[exp_def, exp_cts_thm]);
a(REPEAT strip_tac);
a(∃_tac⌜ℕℝ 0⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(all_fc_tac[exp_¬_eq_0_thm]);
(* *** Goal "2" *** *)
a(contr_tac THEN lemma_tac⌜x < ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN lemma_tac⌜¬Exp x = ℕℝ 0⌝
	THEN1 rewrite_tac[exp_¬_eq_0_thm]
	THEN lemma_tac⌜Exp x < ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ante_tac (list_∀_elim[⌜Exp⌝, ⌜x⌝, ⌜ℕℝ 0⌝]
	intermediate_value_thm));
a(asm_rewrite_tac[exp_def, exp_cts_thm]);
a(REPEAT strip_tac);
a(∃_tac⌜ℕℝ 0⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(all_fc_tac[exp_¬_eq_0_thm]);
pop_thm()
));

=TEX

The exponential function maps addition to multiplication. 
%%%%
%%%%

=SML

val ⦏exp_plus_thm⦎ = save_thm ( "exp_plus_thm", (
set_goal([], ⌜ ∀x y⦁Exp (x + y) = Exp x * Exp y⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜¬Exp (~x) = ℕℝ 0⌝ THEN1 rewrite_tac[exp_¬_eq_0_thm]);
a(ALL_FC_T1 fc_⇔_canon once_rewrite_tac[
	conv_rule(ONCE_MAP_C(RIGHT_C eq_sym_conv))ℝ_times_cancel_thm]);
a(rewrite_tac[exp_plus_lemma, exp_minus_thm]);
a(lemma_tac⌜¬Exp x = ℕℝ 0⌝ THEN1 rewrite_tac[exp_¬_eq_0_thm]);
a(rewrite_tac[∀_elim⌜Exp y⌝ ℝ_times_order_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
=TEX

The next theorem just collects facts about the exponential function into a useful
rewrite rule:
%%%%
%%%%

=SML

val ⦏exp_clauses⦎ = save_thm ( "exp_clauses", (
set_goal([], ⌜
	Exp(ℕℝ 0) = ℕℝ 1
∧	(∀x⦁ Exp(~x) = Exp x ⋏-⋏1)
∧	(∀x y⦁ Exp(x + y) = Exp x * Exp y)
∧	(∀x⦁ℕℝ 0 < Exp x)
∧	(∀x⦁ℕℝ 0 ≤ Exp x)
⌝);
a(rewrite_tac[exp_def, exp_minus_thm, exp_plus_thm, ℝ_≤_def, exp_0_less_thm]);
pop_thm()
));

=TEX

The exponential function is monotonic increasing:
%%%%
%%%%

=SML

val ⦏exp_less_mono_thm⦎ = save_thm ( "exp_less_mono_thm", (
set_goal([], ⌜∀x y⦁  x < y ⇔ Exp x < Exp y⌝);
a(lemma_tac⌜∀x y⦁  x < y ⇒ Exp x < Exp y⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(bc_thm_tac deriv_0_less_thm THEN ∃_tac⌜Exp⌝);
a(asm_rewrite_tac[exp_cts_thm, exp_def, exp_0_less_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac THEN1 all_asm_fc_tac[]);
a(cases_tac⌜x = y⌝ THEN1 all_var_elim_asm_tac1);
a(contr_tac THEN lemma_tac⌜y < x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

Now we know that the exponential function is never zero we can show that it
is equal to its power series.
%%%%
%%%%

=SML

val ⦏exp_power_series_thm⦎ = save_thm ( "exp_power_series_thm", (
set_goal([], ⌜∀x⦁
	(λm⦁ PowerSeries (λm⦁ ℕℝ(m !) ⋏-⋏1) m x) ->  Exp x
⌝);
a(strip_asm_tac exp_consistency_thm);
a(LEMMA_T ⌜Exp = f⌝ asm_rewrite_thm_tac THEN REPEAT strip_tac);
a(lemma_tac⌜∃a b⦁ ℕℝ 0 ∈ OpenInterval a b ∧ x ∈ OpenInterval a b⌝ THEN1
	(rewrite_tac [open_interval_def] THEN
	∃_tac⌜~(Abs(x) + ℕℝ 1)⌝ THEN ∃_tac⌜Abs(x) + ℕℝ 1⌝ THEN
	REPEAT strip_tac THEN cases_tac⌜ℕℝ 0 ≤ x⌝ THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(ante_tac (list_∀_elim[⌜Exp⌝, ⌜f⌝, ⌜a⌝, ⌜b⌝, ⌜ℕℝ 0⌝] exp_unique_thm));
a(rename_tac[] THEN asm_rewrite_tac[exp_def, exp_¬_eq_0_thm]);
a(REPEAT strip_tac THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX

We show that the definition of the natural logarithm function is consistent:
%%%%
%%%%

=SML
push_consistency_goal ⌜Log⌝;
a(lemma_tac⌜∃f⦁ ∀x y⦁ Exp y = x ⇒ f x = y⌝ THEN1 prove_∃_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(cases_tac⌜∀y⦁ ¬Exp y = x'⌝ THEN1 asm_rewrite_tac[]);
a(∃_tac⌜y⌝ THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1 THEN contr_tac);
a(contr_tac THEN1 lemma_tac⌜y < y' ∨ y' < y⌝ THEN all_fc_tac[exp_less_mono_thm]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜f⌝ THEN REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
val _ = save_consistency_thm ⌜Log⌝ (pop_thm());

val ⦏log_def⦎ = save_thm("log_def", get_spec⌜Log⌝);
=TEX

The exponential function is one-to-one:
%%%%
%%%%

=SML

val ⦏exp_one_one_thm⦎ = save_thm ( "exp_one_one_thm", (
set_goal([], ⌜OneOne Exp⌝);
a(rewrite_tac[one_one_def] THEN contr_tac);
a(lemma_tac⌜x1 < x2 ∨ x2 < x1⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN all_fc_tac[exp_less_mono_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

The exponential function maps natural number multiples to powers:
%%%%
%%%%

=SML

val ⦏exp_ℝ_ℕ_exp_thm⦎ = save_thm ( "exp_ℝ_ℕ_exp_thm", (
set_goal([], ⌜∀m x⦁ Exp (ℕℝ m *x) = Exp x ^ m⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝ THEN
	asm_rewrite_tac[ℝ_ℕ_exp_def, exp_def, ℕℝ_plus_homomorphism_thm,
		ℝ_times_plus_distrib_thm, exp_plus_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

The exponential function maps the real line onto the positive reals:
%%%%
%%%%

=SML

val ⦏exp_0_less_onto_thm⦎ = save_thm ( "exp_0_less_onto_thm", (
set_goal([], ⌜∀x⦁  ℕℝ 0 < x ⇒ ∃y⦁x = Exp y⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜(∃b⦁ x < Exp b) ∧ (∃a⦁Exp a < x)⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜∃d⦁ ℕℝ 1 < Exp d⌝ THEN1
	(∃_tac⌜ℕℝ 2⌝ THEN rewrite_tac[eq_sym_rule(∧_left_elim exp_def)] THEN
		bc_thm_tac exp_less_mono_thm THEN REPEAT strip_tac));
a(all_fc_tac[ℝ_ℕ_exp_tends_to_infinity_thm]);
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜x⌝));
a(∃_tac⌜ℕℝ m * d⌝ THEN asm_rewrite_tac[exp_ℝ_ℕ_exp_thm]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∃d⦁ ℕℝ 0 < Exp d ∧ Exp d < ℕℝ 1⌝ THEN1
	(∃_tac⌜~(ℕℝ 2)⌝ THEN
		rewrite_tac[eq_sym_rule(∧_left_elim exp_def), exp_0_less_thm] THEN
			bc_thm_tac exp_less_mono_thm THEN REPEAT strip_tac));
a(all_fc_tac[ℝ_ℕ_exp_tends_to_0_thm]);
a(∃_tac⌜ℕℝ m'* d⌝ THEN asm_rewrite_tac[exp_ℝ_ℕ_exp_thm]);
(* *** Goal "3" *** *)
a(lemma_tac⌜a < b⌝ THEN1 contr_tac);
(* *** Goal "3.1" *** *)
a(lemma_tac ⌜Exp a < Exp b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜a = b⌝ THEN1 all_var_elim_asm_tac1);
a(lemma_tac ⌜b < a⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac ⌜Exp b <  Exp a⌝ THEN1 all_fc_tac[exp_less_mono_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.2" *** *)
a(ante_tac (list_∀_elim[⌜Exp⌝, ⌜a⌝, ⌜b⌝] intermediate_value_thm));
a(asm_rewrite_tac[exp_cts_thm]);
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
a(∃_tac⌜x'⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX

The exponential function is a left inverse for the natural logarithm function on the
positive reals:
%%%%
%%%%

=SML

val ⦏exp_log_thm⦎ = save_thm ( "exp_log_thm", (
set_goal([], ⌜∀x⦁  ℕℝ 0 < x ⇒ Exp(Log x) = x⌝);
a(REPEAT strip_tac);
a(all_fc_tac[exp_0_less_onto_thm] THEN all_var_elim_asm_tac1);
a(rewrite_tac[log_def]);
pop_thm()
));

=TEX

The natural logarithm function is strictly monotonic on the positive reals:
%%%%
%%%%

=SML

val ⦏log_less_mono_thm⦎ = save_thm ( "log_less_mono_thm", (
set_goal([], ⌜∀x y⦁  ℕℝ 0 < x ∧ x < y ⇒ Log x < Log y⌝);
a(REPEAT strip_tac);
a(all_fc_tac[ℝ_less_trans_thm]);
a(once_rewrite_tac[exp_less_mono_thm]);
a(ALL_FC_T asm_rewrite_tac[exp_log_thm]);
pop_thm()
));

=TEX

The natural logarithm function is continuous on the positive reals:
%%%%
%%%%

=SML

val ⦏log_cts_thm⦎ = save_thm ( "log_cts_thm", (
set_goal([], ⌜∀x⦁  ℕℝ 0 < x ⇒  Log Cts x⌝);
a(REPEAT strip_tac);
a(bc_thm_tac darboux_cts_mono_thm);
a(lemma_tac ⌜∃U L⦁ℕℝ 0 < L ∧ L < x ∧ x < U ∧ ℕℝ 0 < U⌝ THEN1
	(∃_tac⌜ℕℝ 2*x⌝ THEN ∃_tac⌜(1/2)* x⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜U⌝ THEN ∃_tac⌜L⌝ THEN rewrite_tac[open_interval_def, closed_interval_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac log_less_mono_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜Exp y⌝ THEN rewrite_tac[log_def]);
a(LEMMA_T ⌜L = Exp (Log L) ∧ U = Exp(Log U)⌝ once_rewrite_thm_tac THEN1
	ALL_FC_T rewrite_tac [exp_log_thm]);
a(REPEAT strip_tac THEN bc_thm_tac exp_less_mono_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX

The natural logarithm function is differential for positive arguments with derivative given by the
reciprocal function.
%%%%
%%%%

=SML

val ⦏log_deriv_thm⦎ = save_thm ( "log_deriv_thm", (
set_goal([], ⌜∀x⦁  ℕℝ 0 < x ⇒  (Log Deriv x ⋏-⋏1) x⌝);
a(REPEAT strip_tac THEN bc_thm_tac inverse_deriv_thm);
a(lemma_tac ⌜∃U L⦁ℕℝ 0 < L ∧ L < x ∧ x < U ∧ ℕℝ 0 < U ∧¬x = ℕℝ 0⌝ THEN1
	(∃_tac⌜ℕℝ 2*x⌝ THEN ∃_tac⌜(1/2)* x⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜Exp⌝ THEN ∃_tac⌜U⌝ THEN ∃_tac⌜L⌝ THEN
	rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[ℝ_less_trans_thm] THEN ALL_FC_T rewrite_tac[exp_log_thm]);
(* *** Goal "2" *** *)
a(all_fc_tac[exp_0_less_onto_thm] THEN all_var_elim_asm_tac1 THEN rewrite_tac[exp_def, log_def]);
(* *** Goal "3" *** *)
a(all_fc_tac[log_cts_thm]);
pop_thm()
));

=TEX

The natural logarithm function is a homomorphism from the multiplicative group
of positive real numbers under multiplication to the group of  all reals under addition:
%%%%
%%%%

=SML

val ⦏log_clauses⦎ = save_thm ( "log_clauses", (
set_goal([], ⌜
	Log (ℕℝ 1) = ℕℝ 0
∧	(∀x⦁  ℕℝ 0 < x ⇒  Log(x ⋏-⋏1) = ~(Log x))
∧	(∀x y⦁  ℕℝ 0 < x ∧ ℕℝ 0 < y ⇒  Log(x*y) = Log x + Log y)
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[eq_sym_rule (∧_left_elim exp_def), log_def]);
(* *** Goal "2" *** *)
a(all_fc_tac[exp_0_less_onto_thm] THEN all_var_elim_asm_tac1);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) exp_minus_thm, log_def]);
(* *** Goal "3" *** *)
a(all_fc_tac[exp_0_less_onto_thm] THEN all_var_elim_asm_tac1);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) exp_plus_thm, log_def]);
pop_thm()
));

=TEX
We have come a long way without introducing roots, but the time has come.
It could have been done using the intermediate value theorem much earlier
on, but we can do it with logarithms now. First we give the logarithm method
for calculating powers:
%%%%
%%%%

=SML

val ⦏ℝ_ℕ_exp_exp_log_thm⦎ = save_thm ( "ℝ_ℕ_exp_exp_log_thm", (
set_goal([], ⌜
	∀m x⦁ ℕℝ 0 < x ⇒ x ^ m = Exp (ℕℝ m * Log x)
⌝);
a(∀_tac THEN induction_tac⌜m:ℕ⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[ℝ_ℕ_exp_0_1_thm, exp_def]);
(* *** Goal "3" *** *)
a(rewrite_tac[ℝ_ℕ_exp_def, ℕℝ_plus_homomorphism_thm, ℝ_times_plus_distrib_thm,
	exp_clauses]);
a(ALL_ASM_FC_T rewrite_tac[exp_log_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
And that gives us the existence of roots of positive values for positive integer exponents):
%%%%
%%%%

=SML

val ⦏positive_root_thm⦎ = save_thm ( "positive_root_thm", (
set_goal([], ⌜
	∀m x⦁ ¬m =  0 ∧ ℕℝ 0 < x ⇒ ∃y⦁ℕℝ 0 < y ∧ y ^ m = x
⌝);
a(REPEAT strip_tac);
a(∃_tac⌜Exp(Log x * (ℕℝ m)⋏-⋏1)⌝);
a(lemma_tac ⌜ℕℝ 0 < Exp (Log x * ℕℝ m ⋏-⋏1)⌝ THEN rewrite_tac[exp_0_less_thm]);
a(ALL_FC_T rewrite_tac[ℝ_ℕ_exp_exp_log_thm]);
a(rewrite_tac[log_def]);
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀a b c:ℝ⦁ a * b * c = b * a * c⌝]);
a(lemma_tac⌜¬ℕℝ m = ℕℝ 0⌝ THEN1 asm_rewrite_tac[ℕℝ_one_one_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses, exp_log_thm]);
pop_thm()
));

=TEX
Square roots are particularly useful (and we build in a potentially useful converse into the theorem):
%%%%
%%%%

=SML

val ⦏square_root_thm⦎ = save_thm ( "square_root_thm", (
set_goal([], ⌜
	∀x⦁ ℕℝ 0 < x ⇔ ∃y⦁ℕℝ 0 < y ∧ y ^ 2 = x
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[rewrite_rule[](∀_elim⌜2⌝ positive_root_thm)]);
a(∃_tac⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(bc_thm_tac ℝ_0_less_0_less_times_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
A similar theorem on square roots of non-negative numbers:
%%%%
%%%%

=SML

val ⦏square_root_thm1⦎ = save_thm ( "square_root_thm1", (
set_goal([], ⌜
	∀x⦁ ℕℝ 0 ≤ x ⇔ ∃y⦁ℕℝ 0 ≤ y ∧ y ^ 2 = x
⌝);
a(rewrite_tac[ℝ_≤_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[rewrite_rule[](∀_elim⌜2⌝ positive_root_thm)]);
a(∃_tac⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(∃_tac⌜ℕℝ 0⌝ THEN rewrite_tac[ℝ_ℕ_exp_0_1_thm]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1 THEN contr_tac);
a(lemma_tac⌜ℕℝ 0 < y ^ 2⌝ THEN1
	(rewrite_tac[ℝ_ℕ_exp_square_thm] THEN bc_thm_tac ℝ_0_less_0_less_times_thm
		THEN REPEAT strip_tac));
 (* *** Goal "4" *** *)
a(all_var_elim_asm_tac1 THEN all_asm_ante_tac);
a(rewrite_tac[ℝ_ℕ_exp_square_thm]);
pop_thm()
));

=TEX
Square roots, when they exist are unique up to sign:
%%%%
%%%%

=SML

val ⦏square_root_unique_thm⦎ = save_thm ( "square_root_unique_thm", (
set_goal([], ⌜
	∀x y:ℝ⦁ x ^ 2 = y ^ 2 ⇔ x = y ∨ x = ~y
⌝);
a(rewrite_tac[ℝ_ℕ_exp_square_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜(x + ~y) *(x + y) = ℕℝ 0⌝ ante_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rewrite_tac[ℝ_times_eq_0_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
=TEX
Squaring and taking square roots is monotonic for positive values:
%%%%
%%%%

=SML

val ⦏square_square_root_mono_thm⦎ = save_thm ( "square_square_root_mono_thm", (
set_goal([], ⌜
	∀x y⦁ ℕℝ 0 < x ∧ ℕℝ 0 < y ⇒ (x ^ 2 < y ^ 2 ⇔ x < y)
⌝);
a(rewrite_tac[ℝ_ℕ_exp_square_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(CONTR_T (asm_tac o rewrite_rule[ℝ_¬_less_≤_thm]));
a(lemma_tac⌜ℕℝ 0 ≤ x ∧ ℕℝ 0 ≤ y⌝ THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(LEMMA_T⌜y * y ≤ x * x⌝ (fn th => strip_asm_tac th THEN
	PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜y*x⌝);
a(conv_tac (RAND_C (once_rewrite_conv[ℝ_times_comm_thm])));
a(ALL_FC_T rewrite_tac[ℝ_≤_times_mono_thm]);
(* *** Goal "2" *** *)
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜x*y⌝);
a(conv_tac (RAND_C (once_rewrite_conv[ℝ_times_comm_thm])));
a(strip_asm_tac ℝ_times_mono_thm);
a(rename_tac[] THEN ALL_ASM_FC_T rewrite_tac[]);
pop_thm()
));

=TEX

We now look at the sine and cosine functions. The patter is simuliar to that for the exponential
functions but a little more complicated, because the two functions need to be defined together.

First of all we give the result that shows absolute convergence for the power series for the
sine function:
%%%%
%%%%
=SML

val ⦏sin_series_convergence_thm⦎ = save_thm ( "sin_series_convergence_thm", (
set_goal([], ⌜∀x⦁
	ℕℝ 0 < x
⇒	∃c⦁ (λm⦁ PowerSeries (λm⦁
		Abs(if m Mod 2 = 0 then ℕℝ 0 else ~(ℕℝ 1) ^ (m Div 2) * ℕℝ(m !) ⋏-⋏1)) m x) -> c
⌝);
a(REPEAT strip_tac);
a(ante_tac (∀_elim⌜x⌝ exp_series_convergence_thm));
a(rewrite_tac [power_series_series_thm] THEN REPEAT strip_tac);
a(conv_tac(BINDER_C (rewrite_conv[η_axiom]))
	THEN POP_ASM_T (strip_asm_tac o rewrite_rule[η_axiom]));
a(bc_thm_tac comparison_test_thm);
a(∃_tac⌜c⌝ THEN ∃_tac⌜ (λ m⦁ Abs (ℕℝ(m !) ⋏-⋏1) * x ^ m)⌝ THEN REPEAT strip_tac);
a(rewrite_tac[]);
a(lemma_tac ⌜Abs x = x⌝ THEN1 asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
a(cases_tac⌜m Mod 2 = 0⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜Abs (ℕℝ(m !) ⋏-⋏1) * x ^ m = Abs ((ℕℝ(m !) ⋏-⋏1) * x ^ m)⌝ 
	(fn th => rewrite_tac[th, ℝ_0_≤_abs_thm]));
a(asm_rewrite_tac[ℝ_abs_times_thm, ℝ_abs_ℝ_ℕ_exp_thm]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[ℝ_abs_times_thm, ℝ_abs_ℝ_ℕ_exp_thm, ℝ_ℕ_exp_0_1_thm, ℝ_abs_abs_thm]);
pop_thm()
));

=TEX
Now we develop some algebra needed to deal with the coefficients of the power series:

%%%%
%%%%
=SML

val ⦏even_odd_thm⦎ = save_thm ( "even_odd_thm", (
set_goal([], ⌜∀m⦁ ∃n⦁ m = 2 * n ∨ m = 2 * n + 1⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜0⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜n⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜n+1⌝ THEN all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏mod_2_div_2_thm⦎ = save_thm ( "mod_2_div_2_thm", (
set_goal([], ⌜∀n⦁
	(2 * n) Mod 2 = 0
∧	(2 * n + 1) Mod 2 = 1
∧	(2 * n) Div 2 = n
∧	(2 * n + 1) Div 2 = n⌝);
a(∀_tac);
a(ante_tac (list_∀_elim[⌜2*n⌝, ⌜2⌝, ⌜n⌝, ⌜0⌝] div_mod_unique_thm));
a(ante_tac (list_∀_elim[⌜2*n + 1⌝, ⌜2⌝, ⌜n⌝, ⌜1⌝] div_mod_unique_thm) THEN 
	PC_T1 "lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏mod_2_cases_thm⦎ = save_thm ( "mod_2_cases_thm", (
set_goal([], ⌜∀m⦁ m Mod 2 = 0 ∨ m Mod 2 = 1⌝);
a(strip_tac THEN lemma_tac⌜m Mod 2 < 2⌝ THEN1 
	(bc_thm_tac mod_less_thm THEN REPEAT strip_tac));
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX

As an aside, at this point, we develop some results relating to odd and even power series:
%%%%
%%%%
=SML

val ⦏mod_2_0_ℝ_ℕ_exp_thm⦎ = save_thm ( "mod_2_0_ℝ_ℕ_exp_thm", (
set_goal([], ⌜∀m; x : ℝ⦁ m Mod 2 = 0 ⇒ (~x) ^ m = x ^ m⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜m⌝ even_odd_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(POP_ASM_T discard_tac THEN induction_tac ⌜n⌝ THEN1 rewrite_tac[ℝ_ℕ_exp_def]);
a(pure_once_rewrite_tac[pc_rule1 "lin_arith" prove_rule[]⌜2*(n+1) = (2*n+1)+1⌝]);
a(pure_rewrite_tac[ℝ_ℕ_exp_def] THEN asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[mod_2_div_2_thm]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏mod_2_1_ℝ_ℕ_exp_thm⦎ = save_thm ( "mod_2_1_ℝ_ℕ_exp_thm", (
set_goal([], ⌜∀m; x : ℝ⦁ m Mod 2 = 1 ⇒ (~x) ^ m = ~(x ^ m)⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜m⌝ even_odd_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac[mod_2_div_2_thm]);
(* *** Goal "2" *** *)
a(POP_ASM_T discard_tac THEN induction_tac ⌜n⌝ THEN1 rewrite_tac[ℝ_ℕ_exp_def]);
a(pure_once_rewrite_tac[pc_rule1 "lin_arith" prove_rule[]⌜2*(n+1) = (1+2*n)+1⌝]);
a(pure_rewrite_tac[ℝ_ℕ_exp_def]);
a(asm_rewrite_tac[prove_rule[]⌜1+2*n = 2*n+1⌝]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏power_series_even_thm⦎ = save_thm ( "power_series_even_thm", (
set_goal([], ⌜∀s n x⦁ (∀m⦁ m Mod 2 = 1 ⇒ s m = ℕℝ 0)
	⇒ PowerSeries s n (~x) = PowerSeries s n x⌝);
a(rewrite_tac[power_series_series_thm] THEN REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN asm_rewrite_tac[series_def]);
a(strip_asm_tac(∀_elim⌜n⌝ mod_2_cases_thm));
 (* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[mod_2_0_ℝ_ℕ_exp_thm]);
 (* *** Goal "2" *** *)
a(LEMMA_T ⌜s n = ℕℝ 0⌝ rewrite_thm_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX

%%%%
%%%%
=SML

val ⦏power_series_odd_thm⦎ = save_thm ( "power_series_odd_thm", (
set_goal([], ⌜∀s n x⦁ (∀m⦁ m Mod 2 = 0 ⇒ s m = ℕℝ 0)
	⇒ PowerSeries s n (~x) = ~(PowerSeries s n x)⌝);
a(rewrite_tac[power_series_series_thm] THEN REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN asm_rewrite_tac[series_def]);
a(strip_asm_tac(∀_elim⌜n⌝ mod_2_cases_thm));
 (* *** Goal "1" *** *)
a(LEMMA_T ⌜s n = ℕℝ 0⌝ rewrite_thm_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN asm_rewrite_tac[]);
 (* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[mod_2_1_ℝ_ℕ_exp_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX

Returning to the consistency of the definitions, we now do the algebra that shows that the coefficients in
the power series for the second derivative of the sine function are what one would
expect (viz., the negatives of the coefficients of the sine power series). We do a little lemma first:

%%%%
%%%%
=SML
set_goal([], ⌜∀m ⦁ ~(ℕℝ 1) ^ ((m +2) Div 2) =  ~(~(ℕℝ 1) ^ (m Div 2))⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜m⌝ even_odd_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜2*n + 2 = 2*(n+1)⌝ rewrite_thm_tac THEN1 PC_T1 "lin_arith" prove_tac[]);
a(rewrite_tac[mod_2_div_2_thm, ℝ_ℕ_exp_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜(2*n +1)  + 2 = 2*(n+1) + 1⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" prove_tac[]);
a(rewrite_tac[mod_2_div_2_thm, ℝ_ℕ_exp_def]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
val ⦏sin_deriv_coeffs_lemma⦎ = pop_thm();
=TEX
Now the required fact about the coefficients for the second derivative:
%%%%
%%%%
=SML

val ⦏sin_deriv_coeffs_thm⦎ = save_thm ( "sin_deriv_coeffs_thm", (
set_goal([], ⌜∀m⦁
	ℕℝ (m + 1) * ℕℝ (m+2) * (
		if (m + 2) Mod 2 = 0 then ℕℝ 0 else ~(ℕℝ 1) ^ ((m +2) Div 2) * ℕℝ((m + 2) !) ⋏-⋏1)
	=	~(if m Mod 2 = 0 then ℕℝ 0 else ~(ℕℝ 1) ^ (m Div 2) * ℕℝ(m !) ⋏-⋏1)⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜m⌝ even_odd_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(LEMMA_T⌜2*n+2 = 2*(n+1)⌝ rewrite_thm_tac THEN1 PC_T1 "lin_arith" prove_tac[]);
a(rewrite_tac[mod_2_div_2_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[sin_deriv_coeffs_lemma]);
a(rewrite_tac[plus_assoc_thm] THEN induction_tac⌜n⌝ THEN1 rewrite_tac[]);
(* *** Goal "2.1" *** *)
a(pure_once_rewrite_tac[prove_rule[]⌜1 = 0 + 1 ∧ 3 = ((0 + 1) + 1) + 1⌝]);
a(pure_rewrite_tac[factorial_def]
	THEN rewrite_tac[ℕℝ_times_homomorphism_thm]);
(* *** Goal "2.2" *** *)
a(LEMMA_T⌜∀n⦁2*n+3 = 2*(n+1)+1⌝ rewrite_thm_tac THEN1 PC_T1 "lin_arith" prove_tac[]);
a(rewrite_tac[mod_2_div_2_thm, plus_assoc_thm]);
a(once_rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b c d:ℝ⦁a*b*c*d = c*a*b*d⌝]);
a(rewrite_tac[factorial_times_recip_thm]);
a(LEMMA_T⌜2*(n+1) + 2 = (2*(n+1) + 1) + 1 ∧ 2*(n+2) = (2*(n+1) + 1) + 1⌝
	rewrite_thm_tac THEN1 PC_T1 "lin_arith" prove_tac[]);
a(rewrite_tac[factorial_times_recip_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
The main theorem justifying the consistency of the definition by the differential equation
of the sine and cosine functions.
For future use, we add in the facts that the witness are given by the expected power series
(the form of the coefficients for cosine is just what drops out of the proof and can be
simplified later).
%%%%
%%%%
=SML

val ⦏sin_cos_consistency_thm⦎ = save_thm ( "sin_cos_consistency_thm", (
set_goal([], ⌜
	∃s c⦁
	(∀y⦁ (s Deriv c y) y)
∧	(∀y⦁ (c Deriv  ~(s y)) y)
∧	s (ℕℝ 0) = ℕℝ 0
∧	c (ℕℝ 0) = ℕℝ 1
∧	(∀ x⦁ (λ n⦁ PowerSeries(λ m⦁
		if m Mod 2 = 0
		then ℕℝ 0
		else ~ (ℕℝ 1) ^ (m Div 2) * ℕℝ(m !) ⋏-⋏1)  n x) -> s x)
∧	(∀ x⦁ (λ n⦁ PowerSeries(λ m⦁
		ℕℝ (m+1) *
		if (m+1) Mod 2 = 0
		then ℕℝ 0
		else ~ (ℕℝ 1) ^ ((m+1) Div 2) * ℕℝ((m+1)!) ⋏-⋏1)  n x) -> c x)
⌝);
a(ante_tac sin_series_convergence_thm);
a(pure_once_rewrite_tac[prove_rule[]⌜∀m⦁
		(if m Mod 2 = 0 then ℕℝ 0 else ~ (ℕℝ 1) ^ (m Div 2) * ℕℝ(m !) ⋏-⋏1)
	=	 (λm⦁ (if m Mod 2 = 0 then ℕℝ 0 else ~ (ℕℝ 1) ^ (m Div 2) * ℕℝ(m !) ⋏-⋏1)) m⌝]);
a(strip_tac THEN all_fc_tac[power_series_main_thm3]);
a(DROP_NTH_ASM_T 2(strip_asm_tac o rewrite_rule[factorial_def]));
a(DROP_NTH_ASM_T 2 ante_tac);
a(rewrite_tac[] THEN pure_once_rewrite_tac[prove_rule[]⌜1 = 0 + 1⌝ ]
	THEN pure_rewrite_tac[factorial_def] THEN rewrite_tac[]);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[sin_deriv_coeffs_thm]));
a(∃_tac⌜f⌝  THEN ∃_tac⌜d1f⌝ THEN asm_rewrite_tac[]);
a(GET_NTH_ASM_T 6 (rewrite_thm_tac o rewrite_rule[]));
a(LEMMA_T ⌜∀y⦁~(f y) = d2f y⌝ asm_rewrite_thm_tac THEN REPEAT strip_tac);
a(SPEC_NTH_ASM_T 7 ⌜y⌝ ante_tac);
a(SPEC_NTH_ASM_T 1 ⌜y⌝ ante_tac);
a(DROP_ASMS_T discard_tac THEN rewrite_tac[power_series_series_thm]);
a(rewrite_tac[
	rewrite_rule[pc_rule1 "ℝ_lin_arith" prove_rule[]
			⌜∀a b⦁ ~(ℕℝ 1) * a = ~a ∧ ~(a *b) = ~a * b⌝]
		(list_∀_elim[
			⌜λm⦁ (
				if m Mod 2 = 0
				then ℕℝ 0
				else ~ (ℕℝ 1) ^ (m Div 2) * ℕℝ (m !) ⋏-⋏1) * y ^ m⌝,
			⌜~(ℕℝ 1)⌝]
			const_times_series_thm)
]);
a(strip_tac THEN STRIP_T (ante_tac o once_rewrite_rule [minus_lim_seq_thm]));
a(rewrite_tac[] THEN strip_tac);
a(all_fc_tac[lim_seq_unique_thm]);
pop_thm()
));

=TEX
Et, voil\'a:
%%%%
%%%%
=TEX
=SML
push_consistency_goal⌜Sin⌝;
a(strip_asm_tac sin_cos_consistency_thm);
a(∃_tac ⌜(s, c)⌝ THEN asm_rewrite_tac[]);
val _ = save_consistency_thm ⌜Sin⌝ (pop_thm());
val ⦏sin_def⦎ = get_spec⌜Sin⌝;
val ⦏cos_def⦎ = get_spec⌜Cos⌝;

val _ = list_save_thm(["sin_def", "cos_def"], sin_def);
=TEX
=TEX
From the definitions it follows that the sine and cosine functions
have derivatives everywhere and so are everywhere continuous:
%%%%
%%%%

=SML

val ⦏sin_cos_cts_thm⦎ = save_thm ( "sin_cos_cts_thm", (
set_goal([], ⌜ ∀x⦁ Sin Cts x ∧ Cos Cts x⌝);
a(REPEAT strip_tac THEN bc_thm_tac deriv_cts_thm);
(* *** Goal "1" *** *)
a(∃_tac ⌜Cos x⌝ THEN rewrite_tac[sin_def]);
(* *** Goal "2" *** *)
a(∃_tac ⌜~(Sin x)⌝ THEN rewrite_tac[sin_def]);
pop_thm()
));

=TEX

=TEX
Now we have a useful connection of facts about the derivatives of our basic
set of transcendental functions
=SML
val ⦏trans_deriv_thms⦎ = [
	∧_right_elim exp_def,
	∧_right_elim(∧_right_elim sin_def),
	log_deriv_thm
] @ rat_deriv_thms;
val ⦏trans_deriv_rule⦎ = deriv_rule trans_deriv_thms;
val ⦏TRANS_DERIV_T⦎ = DERIV_T trans_deriv_thms;  
=TEX
With the aid of these it is very easy to follow the ``axiomatic'' development of
the basic properties of the sine and cosine functions. The idea is to use the
defining properties to derive some basic algebraic properties and then use
the mean value theorem to show that sine and cosine are periodic with a
period that can be taken as the definition of $2\pi$.
See, for example, Mitchell's Calculus Without Analytic Geometry.

%%%%
%%%%
=SML

val ⦏cos_squared_plus_sin_squared_thm⦎ = save_thm ( "cos_squared_plus_sin_squared_thm", (
set_goal([], ⌜∀x⦁ Cos x ^ 2 + Sin x ^ 2 = ℕℝ 1⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜ (λx⦁ Cos x ^ 2 + Sin x ^ 2)  x =  (λx⦁ Cos x ^ 2 + Sin x ^ 2) (ℕℝ 0)⌝ ante_tac
	THEN1 (bc_thm_tac deriv_0_thm2 THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a(TRANS_DERIV_T (rewrite_thm_tac o conv_rule(ONCE_MAP_C ℝ_anf_conv)));
(* *** Goal "2" *** *)
a(rewrite_tac[sin_def]);
pop_thm()
));

=TEX
We depart a little from Mitchell here by calculating the right hand sides of the following
equation explicitly now, rather than after the next theorem.
%%%%
%%%%
=SML

val ⦏sin_cos_unique_lemma1⦎ = save_thm ( "sin_cos_unique_lemma1", (
set_goal([], ⌜∀f g x⦁ 
	(∀x⦁(f Deriv g x) x)
∧	(∀x⦁ (g Deriv ~(f x)) x)
⇒	Cos x * g x + Sin x * f x = g(ℕℝ 0)
∧	Cos x * f x - Sin x * g x = f(ℕℝ 0)
⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "predicates" lemma_tac⌜∃h⦁h = λx⦁ Cos x * g x + Sin x * f x⌝ THEN1 prove_∃_tac);
a(LEMMA_T⌜h x = h (ℕℝ 0)⌝ ante_tac THEN_LIST
	[bc_thm_tac deriv_0_thm2 THEN strip_tac, asm_rewrite_tac[sin_def]]);
a(POP_ASM_T (rewrite_thm_tac));
a(TRANS_DERIV_T ante_tac);
a(STRIP_T (ante_tac o list_∀_elim[⌜~(f x)⌝, ⌜g x⌝]) THEN asm_rewrite_tac[]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(PC_T1 "predicates" lemma_tac⌜∃h⦁h = λx⦁ Cos x * f x + ~(Sin x * g x)⌝ THEN1 prove_∃_tac);
a(LEMMA_T⌜h x = h (ℕℝ 0)⌝ ante_tac THEN_LIST
	[bc_thm_tac deriv_0_thm2 THEN strip_tac, asm_rewrite_tac[sin_def]]);
a(POP_ASM_T (rewrite_thm_tac));
a(TRANS_DERIV_T ante_tac);
a(STRIP_T (ante_tac o list_∀_elim[⌜g x⌝, ⌜~(f x)⌝]) THEN asm_rewrite_tac[]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN REPEAT strip_tac);
pop_thm()
));

=TEX
Pleasingly, the algebra in the next step is easy given the explicit formula on
the right-hand sides of the equations in the previous theorem.
%%%%
%%%%
=SML

val ⦏sin_cos_unique_lemma2⦎ = save_thm ( "sin_cos_unique_lemma2", (
set_goal([], ⌜∀f g x⦁ 
	(∀x⦁(f Deriv g x) x)
∧	(∀x⦁ (g Deriv ~(f x)) x)
⇒	f x = f(ℕℝ 0) * Cos x + g(ℕℝ 0) * Sin x
∧	g x = g(ℕℝ 0) * Cos x - f(ℕℝ 0) * Sin x
⌝);
a(rewrite_tac[] THEN REPEAT ∀_tac THEN ⇒_tac);
a(ALL_FC_T (rewrite_tac o map (conv_rule(ONCE_MAP_C eq_sym_conv)))
	[sin_cos_unique_lemma1]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(rewrite_tac[conv_rule (ONCE_MAP_C eq_sym_conv) ℝ_times_plus_distrib_thm,
	cos_squared_plus_sin_squared_thm]);
pop_thm()
));

=TEX
This gives us the uniqueness theorem \ldots
%%%%
%%%%
=SML

val ⦏sin_cos_unique_thm⦎ = save_thm ( "sin_cos_unique_thm", (
set_goal([], ⌜∀f g x⦁ 
	f(ℕℝ 0) = ℕℝ 0
∧	g(ℕℝ 0) = ℕℝ 1
∧	(∀x⦁(f Deriv g x) x)
∧	(∀x⦁ (g Deriv ~(f x)) x)
⇒	f x = Sin x
∧	g x = Cos x
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(ALL_FC_T once_rewrite_tac[sin_cos_unique_lemma2]);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX

\ldots from which we can show that sine and cosine have the expected power series expansions:
%%%%
%%%%

=SML

val ⦏sin_cos_power_series_thm⦎ = save_thm ( "sin_cos_power_series_thm", (
set_goal([], ⌜∀x⦁
	(λ n⦁ PowerSeries (λ m⦁
		if m Mod 2 = 0
		then ℕℝ 0
		else ~ (ℕℝ 1) ^ (m Div 2) * ℕℝ(m !) ⋏-⋏1) n x) -> Sin  x
∧	(λ n⦁ PowerSeries (λ m⦁
		ℕℝ (m + 1) *
		(if (m + 1) Mod 2 = 0
		then ℕℝ 0
		else ~ (ℕℝ 1) ^ ((m + 1) Div 2) * ℕℝ((m + 1)!) ⋏-⋏1)) n x) -> Cos x	⌝);
a(strip_asm_tac sin_cos_consistency_thm);
a(LEMMA_T ⌜Sin = s ∧ Cos = c⌝ asm_rewrite_thm_tac THEN rewrite_tac[]);
a(LEMMA_T⌜∀ x⦁ Sin x = s x ∧ Cos x = c x⌝ rewrite_thm_tac THEN ∀_tac);
a(ante_tac (list_∀_elim[⌜s⌝, ⌜c⌝, ⌜x⌝] sin_cos_unique_thm));
a(asm_rewrite_tac[]);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
\ldots and the rules for sums:
%%%%
%%%%
=SML

val ⦏sin_cos_plus_thm⦎ = save_thm ( "sin_cos_plus_thm", (
set_goal([], ⌜∀x y⦁ 
	Sin (x + y) = Sin x * Cos y + Cos x * Sin y
∧	Cos(x + y) = Cos x * Cos y - Sin x * Sin y
⌝);
a(REPEAT ∀_tac);
a(PC_T1 "predicates" lemma_tac⌜∃f g⦁ f = (λx⦁Sin(x + y)) ∧ g = λx⦁(Cos(x + y))⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜(∀x⦁(f Deriv g x) x) ∧ (∀x⦁ (g Deriv ~(f x)) x)⌝ THEN1
	(REPEAT strip_tac THEN asm_rewrite_tac[] THEN TRANS_DERIV_T ante_tac
	THEN rewrite_tac[]));
a(ALL_FC_T (MAP_EVERY ante_tac)[sin_cos_unique_lemma2]);
a(LIST_DROP_NTH_ASM_T [3, 4] rewrite_tac);
a(REPEAT strip_tac THEN asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
\ldots and the facts that sine and cosine are odd and even respectively:
%%%%
%%%%
=SML

val ⦏sin_cos_minus_thm⦎ = save_thm ( "sin_cos_minus_thm", (
set_goal([], ⌜∀x⦁ 
	Sin(~x) = ~(Sin x)
∧	Cos(~x) = Cos x
⌝);
a(lemma_tac⌜∀x⦁ ((λx⦁ ~(Sin(~x))) Deriv (λx⦁ Cos (~x)) x) x⌝
	THEN1 (strip_tac THEN rewrite_tac[] THEN TRANS_DERIV_T ante_tac
		THEN conv_tac (ONCE_MAP_C ℝ_anf_conv)
			THEN REPEAT strip_tac));
a(lemma_tac⌜∀x⦁ ((λx⦁ Cos(~x)) Deriv ~((λx⦁ ~(Sin (~x))) x)) x⌝
	THEN1 (strip_tac THEN rewrite_tac[] THEN TRANS_DERIV_T ante_tac
		THEN conv_tac (ONCE_MAP_C ℝ_anf_conv)
			THEN REPEAT strip_tac));
a(ante_tac (list_∀_elim[⌜(λx⦁ ~(Sin(~x)))⌝, ⌜(λx⦁ Cos (~x))⌝] sin_cos_unique_lemma2));
a(asm_rewrite_tac[sin_def] THEN ⇒_tac THEN ∀_tac);
a(pure_once_rewrite_tac[prove_rule[]⌜Sin (~ x) = ~(~(Sin (~x)))⌝]);
a(pure_asm_rewrite_tac[] THEN rewrite_tac[]);
pop_thm()
));

=TEX
The previous results give rise to several useful subgroups of the additive group 
of reals. The zeroes of the sine function comprise the group we use to define
$\pi$. The next theorem states that it is indeed a subgroup:
%%%%
%%%%
=SML

val ⦏sin_0_group_thm⦎ = save_thm ( "sin_0_group_thm", (
set_goal([], ⌜
	ℕℝ 0  ∈ {x | Sin x = ℕℝ 0} 
∧	(∀x y⦁ x ∈ {x | Sin x = ℕℝ 0} ∧ y ∈ {x | Sin x = ℕℝ 0} ⇒ x + y ∈ {x | Sin x = ℕℝ 0})
∧	(∀x⦁ x ∈ {x | Sin x = ℕℝ 0} ⇒ ~x ∈ {x | Sin x = ℕℝ 0})
⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[sin_def, sin_cos_plus_thm, sin_cos_minus_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_0_ℕℝ_times_thm⦎ = save_thm ( "sin_0_ℕℝ_times_thm", (
set_goal([], ⌜∀x m⦁ Sin x = ℕℝ 0 ⇒ Sin (ℕℝ m * x) = ℕℝ 0⌝);
a(REPEAT ∀_tac THEN induction_tac⌜m:ℕ⌝ THEN REPEAT strip_tac
	THEN asm_rewrite_tac[sin_def,
		sin_cos_plus_thm,
		ℕℝ_plus_homomorphism_thm,
		ℝ_times_plus_distrib_thm]);
pop_thm()
));

=TEX
We now show that if the sine and cosine functions are equal at $x$ then $\Sin{2x} = 1$
and $\Cos{2x} = 0$.
%%%%
%%%%
=SML

val ⦏sin_eq_cos_sin_cos_twice_thm⦎ = save_thm ( "sin_eq_cos_sin_cos_twice_thm", (
set_goal([], ⌜∀x⦁
	Sin x = Cos x
⇒	Sin (ℕℝ 2 * x) = ℕℝ 1
 ∧	Cos(ℕℝ 2 * x) = ℕℝ 0
⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(pure_once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜ℕℝ 2 * x = x + x⌝]);
a(ante_tac(∀_elim⌜x⌝ cos_squared_plus_sin_squared_thm));
a(asm_rewrite_tac[ℝ_ℕ_exp_square_thm, sin_cos_plus_thm]);
pop_thm()
));

=TEX
We need a special case ($z = 1$)
of the following algebraic inequality, which is just as easy to state and prove for arbitrary $z$:
%%%%
%%%%
=SML

val ⦏sum_squares_abs_bound_thm⦎ = save_thm ( "sum_squares_abs_bound_thm", (
set_goal([], ⌜∀x y z:ℝ⦁ x ^ 2 + y ^ 2 = z ^ 2 ⇒ Abs x ≤ Abs z⌝);
a(contr_tac THEN POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(LEMMA_T⌜Abs x ^ 2 + Abs y ^ 2 = Abs z ^ 2⌝ ante_tac
	THEN1 asm_rewrite_tac[ℝ_abs_squared_thm] THEN contr_tac);
a(lemma_tac ⌜ℕℝ 0 ≤ Abs z⌝ THEN1 rewrite_tac[ℝ_0_≤_abs_thm]);
a(lemma_tac ⌜ℕℝ 0 ≤ Abs y ^ 2⌝ THEN1 
	(rewrite_tac[ℝ_ℕ_exp_square_thm] THEN
		bc_thm_tac ℝ_0_≤_0_≤_times_thm THEN REPEAT strip_tac
			THEN rewrite_tac[ℝ_0_≤_abs_thm]));
a(lemma_tac⌜Abs z ^ 2 < Abs x ^ 2⌝ THEN_LIST
	[id_tac, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(lemma_tac⌜ℕℝ 0 < Abs x ∧ ℕℝ 0 ≤ Abs x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜Abs z * Abs x⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac ℝ_≤_times_mono_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(bc_thm_tac ℝ_times_mono_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
We need a special case ($z = 1$)
of the following algebraic inequality, which is just as easy to state and prove for arbitrary $z$:
%%%%
%%%%
=SML

val ⦏sum_squares_abs_bound_thm1⦎ = save_thm ( "sum_squares_abs_bound_thm1", (
set_goal([], ⌜∀x y:ℝ⦁ x ^ 2 + y ^ 2 = ℕℝ 1 ⇒ Abs x ≤ ℕℝ 1⌝);
a(REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜x⌝, ⌜y⌝, ⌜ℕℝ 1⌝] sum_squares_abs_bound_thm) THEN rewrite_tac[]);
a(POP_ASM_T ante_tac THEN taut_tac);
pop_thm()
));

=TEX
Whence sine and cosine are of absolute value at most one:
%%%%
%%%%
=SML

val ⦏abs_sin_abs_cos_≤_1_thm⦎ = save_thm ( "abs_sin_abs_cos_≤_1_thm", (
set_goal([], ⌜
	∀x:ℝ⦁ Abs(Sin x) ≤ ℕℝ 1 ∧ Abs(Cos x) ≤ ℕℝ 1
⌝);
a(strip_tac);
a(strip_asm_tac (∀_elim⌜x⌝ cos_squared_plus_sin_squared_thm));
a(TOP_ASM_T (strip_asm_tac o once_rewrite_rule[ℝ_plus_comm_thm]));
a(all_fc_tac[sum_squares_abs_bound_thm1] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
We plan to make our estimates of the value of $\pi/2$ a little bit more accurate than
the ones given by Mitchell.
From the estimate given by {\em deriv\_linear\_estimate\_thm}, $\Cos{x}$ is positive for $x$ in the open interval $(0, 1)$:
%%%%
%%%%
=SML

val ⦏cos_positive_estimate_thm⦎ = save_thm ( "cos_positive_estimate_thm", (
set_goal([], ⌜
	∀x⦁ x ∈ OpenInterval (ℕℝ 0) (ℕℝ 1) ⇒ ℕℝ 0 < Cos x
⌝);
a(rewrite_tac[open_interval_def] THEN contr_tac);
a(POP_ASM_T  (strip_asm_tac o rewrite_rule[ℝ_¬_less_≤_thm]));
a(ante_tac (list_∀_elim[⌜Cos⌝, ⌜λt⦁~(Sin t)⌝, ⌜ℕℝ 0⌝, ⌜x⌝]deriv_linear_estimate_thm));
a(asm_rewrite_tac[cos_def, ℝ_abs_minus_thm, abs_sin_abs_cos_≤_1_thm] THEN REPEAT strip_tac);
a(lemma_tac⌜¬ℕℝ 0 ≤ Cos x + ~(ℕℝ 1)⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_abs_def, ℝ_¬_≤_less_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Whence $\Sin{x}$ too is positive for $x$ in the open interval $(0, 1)$, and so, 
by the sum formula for $x$ in $[1, 2)$ as well.
%%%%
%%%%
=SML

val ⦏sin_positive_estimate_thm⦎ = save_thm ( "sin_positive_estimate_thm", (
set_goal([], ⌜
	∀x⦁ x ∈ OpenInterval (ℕℝ 0) (ℕℝ 2) ⇒ ℕℝ 0 < Sin x
⌝);
a(LEMMA_T⌜∀x⦁ x ∈ OpenInterval (ℕℝ 0) (ℕℝ 1) ⇒ ℕℝ 0 < Sin x⌝ ante_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
a(ante_tac (list_∀_elim[⌜Sin⌝, ⌜Cos⌝, ⌜ℕℝ 0⌝, ⌜x⌝]deriv_0_less_thm));
a(asm_rewrite_tac[cos_def, sin_cos_cts_thm] THEN REPEAT strip_tac);
a(lemma_tac⌜x' < ℕℝ 1⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[rewrite_rule[open_interval_def] cos_positive_estimate_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/2)*x ∧ (1/2)*x < ℕℝ 1⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3, 4, 5] all_fc_tac);
a(all_fc_tac [rewrite_rule[open_interval_def] cos_positive_estimate_thm]);
a(pure_once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜ x = (1/2)*x + (1/2)*x⌝]);
a(rewrite_tac[sin_cos_plus_thm]);
a(LEMMA_T ⌜ℕℝ 0 < Sin((1/2)*x) * Cos((1/2)*x) ∧ ℕℝ 0 <  Cos((1/2)*x) * Sin((1/2)*x)⌝
	(fn th => ante_tac th THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(REPEAT strip_tac THEN all_fc_tac[ℝ_0_less_0_less_times_thm]);
pop_thm()
));

=TEX
Now, following Mitchell but getting the best estimate we can from the proof we have the following
theorem that shows that if the cosine function is  greater than $1/\sqrt{2}$ in some interval
$[0, t)$, then $t$ is at most $\sqrt{2}$.
%%%%
%%%%
=SML

val ⦏cos_greater_root_2_thm⦎ = save_thm ( "cos_greater_root_2_thm", (
set_goal([], ⌜∀t⦁
	ℕℝ 0 < t
∧	(∀x⦁ℕℝ 0 < x ∧ x < t ⇒ 1/2 < Cos x ^ 2)
⇒	t ^ 2 ≤ ℕℝ 2
⌝);
a(rewrite_tac[ℝ_ℕ_exp_square_thm] THEN REPEAT strip_tac);
a(ante_tac (list_∀_elim[⌜Sin⌝, ⌜Cos⌝, ⌜ℕℝ 0⌝, ⌜t⌝]mean_value_thm1));
a(asm_rewrite_tac[sin_def] THEN REPEAT strip_tac);
a(CONTR_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(lemma_tac⌜ℕℝ 1 < Sin t * Sin t⌝ THEN1 asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(pure_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[] ⌜
	ℕℝ 1 = ℕℝ 2 * (1/2)
∧	(t * Cos x) * t * Cos x = (t * t) * (Cos x * Cos x)⌝]);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜ℕℝ 2 * (Cos x * Cos x)⌝ THEN
	REPEAT strip_tac THEN1
		(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac));
a(lemma_tac ⌜ℕℝ 0 < Cos x * Cos x⌝  THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(once_rewrite_tac[ℝ_times_comm_thm] THEN bc_thm_tac ℝ_times_mono_thm
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(lemma_tac ⌜ℕℝ 0 ≤ Sin t * Sin t⌝  THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ℕℝ 1 < Abs(Sin t * Sin t)⌝ ante_tac THEN1 
	(DROP_NTH_ASM_T 5 discard_tac THEN asm_rewrite_tac[ℝ_abs_def]));
a(rewrite_tac[ℝ_abs_times_thm] THEN REPEAT strip_tac);
a(rewrite_tac[ℝ_¬_less_≤_thm]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜Abs(Sin t) * ℕℝ 1⌝);
a(REPEAT strip_tac THEN1
	(bc_thm_tac ℝ_≤_times_mono_thm )THEN
		rewrite_tac[abs_sin_abs_cos_≤_1_thm, ℝ_0_≤_abs_thm]);
pop_thm()
));

=TEX
By the intermediate value theorem and the last result,there is an $x$
with $0 < x$,  $x^2 < 2 + e$ and $\Cos{x} = 1/\sqrt{2}$. for any positive $e$
%%%%
%%%%
=SML

val ⦏cos_squared_eq_half_thm⦎ = save_thm ( "cos_squared_eq_half_thm", (
set_goal([], ⌜
	∀e⦁ ℕℝ 0 < e ⇒ ∃x⦁ ℕℝ 0 < x ∧ x ^ 2 < ℕℝ 2 + e ∧ ℕℝ 0 < Cos x ∧ Cos x ^ 2 = 1/2
⌝);
a(REPEAT strip_tac THEN lemma_tac ⌜ℕℝ 0 < ℕℝ 2 + e ⌝ THEN1
	PC_T1"ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜∃rt2⦁ℕℝ 0 < rt2 ∧ rt2 ^ 2 = 1/2⌝ THEN1
	(bc_thm_tac square_root_thm THEN rewrite_tac[]));
a(ante_tac(list_∀_elim[⌜rt2⌝, ⌜ℕℝ 1⌝] square_square_root_mono_thm));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(cases_tac⌜¬∀x⦁ ℕℝ 0 < x ∧ x ^ 2 < ℕℝ 2 + e ⇒ ℕℝ 0 ≤  (λx⦁ Cos x + ~rt2) x⌝
	THEN REPEAT  strip_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[ℝ_¬_≤_less_thm]));
a(lemma_tac ⌜ ∀x⦁ (λx⦁ Cos x + ~rt2)  Cts x⌝);
(* *** Goal "1.1" *** *)
a(DROP_ASMS_T discard_tac THEN
	REPEAT strip_tac THEN bc_thm_tac deriv_cts_thm THEN REPEAT strip_tac);
a(contr_tac THEN asm_tac (rewrite_rule[] (deriv_rule trans_deriv_thms ⌜ (λx⦁ Cos x + ~rt2) ⌝ ⌜x⌝)));
a(all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a(ante_tac (list_∀_elim[⌜(λx⦁ Cos x + ~rt2)⌝, ⌜ℕℝ 0⌝, ⌜x⌝] intermediate_value_thm));
a(pure_asm_rewrite_tac[] THEN asm_rewrite_tac[cos_def]);
a(lemma_tac⌜ℕℝ 0 < ℕℝ 1 + ~rt2⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(STRIP_T (ante_tac o ∀_elim⌜ℕℝ 0⌝) THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(ante_tac(list_∀_elim[⌜x'⌝, ⌜x⌝] square_square_root_mono_thm));
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.3" *** *)
a(lemma_tac⌜Cos x' = rt2⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[]) THEN contr_tac);
a(lemma_tac⌜ℕℝ 0 < ℕℝ 2  + (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜∃t⦁ℕℝ 0 < t  ∧ t^ 2 = ℕℝ 2  + (1/2)*e⌝ THEN1
	(bc_thm_tac square_root_thm THEN REPEAT strip_tac));
a(lemma_tac ⌜t ^ 2 ≤ ℕℝ 2⌝ THEN_LIST
	[bc_thm_tac cos_greater_root_2_thm, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(REPEAT strip_tac);
a(lemma_tac ⌜x ^ 2 < t ^ 2⌝ );
(* *** Goal "2.1" *** *)
a(ante_tac(list_∀_elim[⌜x⌝, ⌜t⌝] square_square_root_mono_thm));
a(asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜x ^ 2 < ℕℝ 2 + e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(GET_NTH_ASM_T 11 (rewrite_thm_tac o eq_sym_rule));
a(LIST_GET_NTH_ASM_T [9] all_fc_tac);
a(lemma_tac⌜ℕℝ 0 < Cos x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ante_tac(list_∀_elim[⌜rt2⌝, ⌜Cos x⌝] square_square_root_mono_thm));
a(asm_rewrite_tac[]);
a(STRIP_T rewrite_thm_tac);
a(lemma_tac⌜rt2 ≤ Cos x⌝  THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[ℝ_≤_def]);
a(DROP_NTH_ASM_T 11 (ante_tac o ∀_elim⌜x⌝) THEN asm_rewrite_tac[]);
a(contr_tac THEN all_var_elim_asm_tac1);
pop_thm()
));

=TEX
Pulling the above pieces together, there is an $x$ in the open interval $(0, 2)$ such
that $\Sin{x} = \Cos{x}$.

%%%%
%%%%
=SML

val ⦏sin_eq_cos_exists_thm⦎ = save_thm ( "sin_eq_cos_exists_thm", (
set_goal([], ⌜
	∃x⦁ x ∈ OpenInterval (ℕℝ 0) (ℕℝ 2) ∧ Sin x = Cos x
⌝);
a(ante_tac (∀_elim⌜1/4⌝ cos_squared_eq_half_thm) THEN rewrite_tac[] THEN strip_tac);
a(strip_asm_tac (∀_elim⌜x⌝ cos_squared_plus_sin_squared_thm));
a(lemma_tac⌜Sin x ^ 2 = 1/2⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ante_tac(list_∀_elim[⌜x⌝, ⌜3/2⌝] square_square_root_mono_thm));
a(asm_rewrite_tac[] THEN strip_tac);
a(lemma_tac⌜x < ℕℝ 2⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[rewrite_rule[open_interval_def] sin_positive_estimate_thm]);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
a(LEMMA_T ⌜Sin x ^ 2 = Cos x ^ 2⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(rewrite_tac[square_root_unique_thm]);
a(REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
That gives us a positive zero for the sine function:
%%%%
%%%%
=SML

val ⦏sin_positive_zero_thm⦎ = save_thm ( "sin_positive_zero_thm", (
set_goal([], ⌜
	∃x⦁ ℕℝ 0 < x ∧ Sin x = ℕℝ 0
⌝);
a(strip_asm_tac (rewrite_rule[open_interval_def] sin_eq_cos_exists_thm));
a(all_fc_tac[sin_eq_cos_sin_cos_twice_thm]);
a(∃_tac⌜ℕℝ 2*x + ℕℝ 2*x⌝ THEN asm_rewrite_tac[sin_cos_plus_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
Now we prove the general result that non-trivial discrete subgroups of the additive group
of reals are cyclic. (This follows on from some of the work done in constructing the
multiplicative structure of the reals, and we follow the same naming conventions for
variables as were used there).

%%%%
%%%%
=SML

val ⦏ℝ_discrete_subgroup_thm⦎ = save_thm ( "ℝ_discrete_subgroup_thm", (
set_goal([], ⌜ ∀G h a⦁
	ℕℝ 0 ∈ G
∧	(∀ g h⦁ g ∈ G ∧ h ∈ G ⇒ g + h ∈ G)
∧	(∀ g⦁ g ∈ G ⇒ ~ g ∈ G)
∧	ℕℝ 0 < h
∧	h ∈ G
∧	ℕℝ 0 < a
∧	(∀h⦁ℕℝ 0 < h ∧ h ∈ G ⇒ a < h)
⇒	∃g⦁ℕℝ 0 < g ∧  g ∈ G ∧ ∀h⦁ℕℝ 0 < h ∧ h ∈ G ⇒ ∃m⦁h = ℕℝ m * g
⌝);
a(contr_tac);
a(lemma_tac⌜∀m x⦁x ∈ G ⇒ ℕℝ m * x ∈ G⌝ THEN1 
	(∀_tac THEN induction_tac⌜m:ℕ⌝ THEN asm_rewrite_tac[ℕℝ_plus_homomorphism_thm]));
(* *** Goal "1" *** *)
a(rewrite_tac[ℝ_times_plus_distrib_thm] THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 9 bc_thm_tac THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(lemma_tac⌜∀h⦁h ∈ G ∧ ℕℝ 0 < h ⇒ ∃k⦁k ∈ G ∧ ℕℝ 0 < k ∧ k < h⌝);
(* *** Goal "2.1" *** *)
a(LIST_DROP_NTH_ASM_T [ 5, 6] discard_tac THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜h⌝));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 ≤ h'⌝ THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(strip_asm_tac (list_∀_elim[⌜h⌝, ⌜h'⌝] ℝ_archimedean_division_thm));
a(all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜q⌝));
a(cases_tac⌜r = ℕℝ 0⌝ THEN1 asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[ℝ_≤_def]);
a(POP_ASM_T (rewrite_thm_tac o conv_rule(RAND_C eq_sym_conv)));
a(REPEAT strip_tac THEN ∃_tac⌜r⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜r = (ℕℝ q * h + r) + ~(ℕℝ q * h)⌝ once_rewrite_thm_tac THEN1
	(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀x⦁ (x + r) + ~x = r⌝]));
a(LIST_GET_NTH_ASM_T [8, 11, 12] bc_tac THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∃f⦁∀x⦁x ∈ G ∧ ℕℝ 0 < x ⇒ f x ∈ G ∧ ℕℝ 0 < f x ∧ f x < x⌝
	THEN1 prove_∃_tac THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(cases_tac⌜¬(x' ∈ G ∧ ℕℝ 0 < x')⌝ THEN asm_rewrite_tac[]);
a(GET_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜∃s⦁s 0 = h ∧ ∀m⦁s(m+1) = f(s m)⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜∀ m⦁ s m ∈ G ∧ ℕℝ 0 < s m ∧ s (m + 1) < s m⌝ THEN1
	(strip_tac THEN induction_tac⌜m:ℕ⌝ THEN asm_rewrite_tac[]));
(* *** Goal "2.2.2.1" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(LIST_GET_NTH_ASM_T [6] all_fc_tac THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [12] all_fc_tac);
(* *** Goal "2.2.2.3" *** *)
a(ante_tac(list_∀_elim[⌜s⌝, ⌜ℕℝ 0⌝] lim_seq_mono_dec_thm)
	THEN asm_rewrite_tac[ℝ_≤_def]);
a(contr_tac);
a(POP_ASM_T discard_tac THEN all_fc_tac[lim_seq_diffs_tend_to_0_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[lim_seq_def] THEN REPEAT strip_tac);
a(∃_tac⌜a⌝ THEN REPEAT strip_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜n⌝);
a(LEMMA_T⌜¬ℕℝ 0 ≤ s(n+1) + ~(s n)⌝ (fn th => rewrite_tac[th, ℝ_abs_def])
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(spec_nth_asm_tac 5 ⌜n+1⌝);
a(lemma_tac⌜~ (s (n + 1)) + s n ∈ G⌝ THEN1
	(LIST_GET_NTH_ASM_T [19, 20] bc_tac THEN REPEAT strip_tac));
a(lemma_tac⌜ℕℝ 0 < ~ (s (n + 1)) + s n⌝
	THEN1 (GET_NTH_ASM_T 5 ante_tac THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(LIST_GET_NTH_ASM_T [17] all_fc_tac);
a(DROP_ASM_T  ⌜a < ~ (s (n + 1)) + s n⌝ ante_tac THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
and that gives us $\pi$:
%%%%
%%%%
=SML

val ⦏pi_consistency_thm⦎ = save_thm ( "pi_consistency_thm", (
set_goal([], ⌜∃pi⦁
	ℕℝ 0 < pi
∧	Sin pi = ℕℝ 0
∧	(∀x⦁ℕℝ 0 < x ∧ Sin x = ℕℝ 0 ⇒ ∃m⦁x = ℕℝ m * pi)
⌝);
a(strip_asm_tac sin_positive_zero_thm);
a(strip_asm_tac (rewrite_rule[open_interval_def] sin_positive_estimate_thm));
a(lemma_tac ⌜∀x⦁ℕℝ 0 < x ∧ Sin x = ℕℝ 0 ⇒ ℕℝ 1 < x⌝ THEN1 contr_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜x' < ℕℝ 2⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_ASM_FC_T (MAP_EVERY ante_tac)[]);
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(ante_tac (list_∀_elim[⌜{x | Sin x = ℕℝ 0}⌝, ⌜x⌝, ⌜ℕℝ 1⌝] ℝ_discrete_subgroup_thm));
a(rename_tac[] THEN asm_rewrite_tac[sin_0_group_thm] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
Et, voil\'a:
%%%%
%%%%
=TEX
=SML
push_consistency_goal⌜π⌝;
a(strip_asm_tac pi_consistency_thm);
a(∃_tac ⌜pi⌝ THEN asm_rewrite_tac[]);
a(REPEAT_UNTIL is_∨ strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 4 discard_tac);
a(strip_asm_tac(list_∀_elim[⌜ℕℝ 0⌝, ⌜x⌝] ℝ_less_cases_thm));
(* *** Goal "1.1" *** *)
a(all_asm_fc_tac[]);
a(∨_left_tac THEN ∃_tac⌜m⌝  THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(∨_left_tac THEN ∃_tac⌜0⌝  THEN asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a(lemma_tac⌜ℕℝ 0 < ~x ∧  Sin (~x) = ℕℝ 0⌝ THEN1
	(asm_rewrite_tac[sin_cos_minus_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_asm_fc_tac[]);
a(∨_right_tac THEN ∃_tac⌜m⌝  THEN POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1 THEN ALL_FC_T rewrite_tac[sin_0_ℕℝ_times_thm]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[sin_cos_minus_thm]
	THEN ALL_FC_T rewrite_tac[sin_0_ℕℝ_times_thm]);
val _ = save_consistency_thm ⌜π⌝ (pop_thm());

val ⦏π_def⦎ = save_thm("π_def", get_spec⌜π⌝);
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀c m⦁
	(ℕℝ 0 < c ⇒ c ≤ ℕℝ(m + 1) * c)
⌝);
a(REPEAT  strip_tac);
a(induction_tac ⌜m⌝ THEN1 asm_rewrite_tac[]);
a(once_rewrite_tac[ℕℝ_plus_homomorphism_thm]);
a(rewrite_tac[ℝ_times_plus_distrib_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏ℕℝ_plus_1_times_bound_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏ℕℝ_plus_1_times_bound_thm⦎ = save_thm ( "ℕℝ_plus_1_times_bound_thm", (
set_goal([], ⌜
	(∀c m⦁ℕℝ 0 < c ⇒ c ≤ ℕℝ(m + 1) * c)
∧	(∀c m⦁c < ℕℝ 0 ⇒ ℕℝ(m + 1) * c ≤ c)
⌝);
a(rewrite_tac[ℕℝ_plus_1_times_bound_lemma] THEN REPEAT strip_tac);
a(LEMMA_T⌜~c ≤ ℕℝ(m+1) *  ~c⌝ ante_tac THEN1 
	(bc_thm_tac ℕℝ_plus_1_times_bound_lemma THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜
	(∀a ⦁ a * ~c = ~(a * c))
∧	(∀b⦁ ~ c ≤ ~b ⇔ b ≤ c)
⌝]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℕℝ_0_less_¬_ℕℝ_times_π_thm⦎ = save_thm ( "ℕℝ_0_less_¬_ℕℝ_times_π_thm", (
set_goal([], ⌜∀x m⦁
	ℕℝ 0 < x
⇒	¬x = ~(ℕℝ m * π)
⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜m⌝ ℕ_cases_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_asm_ante_tac THEN
	rewrite_tac[pc_rule1"ℝ_lin_arith" prove_rule[]⌜∀a b:ℝ⦁ ~(a * b) = a * ~b⌝]
	THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ(i + 1) * ~ π ≤ ~ π⌝ THEN1
	(bc_thm_tac (∧_right_elim ℕℝ_plus_1_times_bound_thm) THEN ante_tac π_def
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(strip_asm_tac π_def);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_¬_eq_0_thm⦎ = save_thm ( "sin_¬_eq_0_thm", (
set_goal([], ⌜∀x⦁
	ℕℝ 0 < x ∧ x < π ⇒ ¬Sin x = ℕℝ 0	
⌝);
a(rewrite_tac[π_def] THEN contr_tac THEN all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(strip_asm_tac(∀_elim⌜m⌝ ℕ_cases_thm) THEN all_var_elim_asm_tac1
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜ℕℝ 0 < π⌝ THEN1 rewrite_tac[π_def]);
a(lemma_tac⌜π ≤ ℕℝ(i + 1) * π⌝
	THEN1 ALL_FC_T rewrite_tac [ℕℝ_plus_1_times_bound_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(EXTEND_PC_T1 "'mmp1" all_fc_tac[ℕℝ_0_less_¬_ℕℝ_times_π_thm] THEN
	EXTEND_PC_T1 "'mmp1" all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_0_π_0_less_thm⦎ = save_thm ( "sin_0_π_0_less_thm", (
set_goal([], ⌜∀x⦁
	x ∈ OpenInterval (ℕℝ 0) π ⇒ ℕℝ 0 < Sin x
⌝);
a(rewrite_tac[open_interval_def] THEN contr_tac THEN all_fc_tac[sin_¬_eq_0_thm]);
a(lemma_tac⌜ℕℝ 1 < x⌝  THEN1 contr_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜x ∈ OpenInterval (ℕℝ 0) (ℕℝ 2)⌝ THEN1
	(rewrite_tac[open_interval_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[sin_positive_estimate_thm]);
(* *** Goal "2" *** *)
a(ante_tac (list_∀_elim[⌜Sin⌝, ⌜ℕℝ 1⌝, ⌜x⌝] intermediate_value_thm));
a(asm_rewrite_tac[sin_cos_cts_thm, sin_def]);
a(strip_asm_tac (rewrite_rule[open_interval_def](∀_elim⌜ℕℝ 1⌝sin_positive_estimate_thm)));
a(lemma_tac⌜Sin x < ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac);
a(∃_tac⌜ℕℝ 0⌝ THEN asm_rewrite_tac[]);
a(contr_tac);
a(lemma_tac⌜ℕℝ 0 < x' ∧ x' < π⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[sin_¬_eq_0_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜
	Sin π = ℕℝ 0	
⌝);
a(rewrite_tac[π_def]
		THEN ∨_left_tac THEN ∃_tac⌜1⌝ THEN rewrite_tac[]);
val ⦏sin_π_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_π_over_2_thm⦎ = save_thm ( "sin_cos_π_over_2_thm", (
set_goal([], ⌜
	Sin ((1/2) * π) = ℕℝ 1 ∧ Cos ((1/2) * π) = ℕℝ 0
⌝);
a(ante_tac(
	rewrite_rule[sin_π_lemma, ℝ_times_eq_0_thm]
		(conv_rule(ONCE_MAP_C ℝ_anf_conv THEN_C eq_sym_conv)
			(∧_left_elim
				(list_∀_elim[⌜(1/2) * π⌝, ⌜(1/2) * π⌝] sin_cos_plus_thm)))));
a(lemma_tac⌜ℕℝ 0 < π⌝ THEN1 rewrite_tac[π_def]);
a(lemma_tac⌜ℕℝ 0 < 1/2 * π ∧ 1/2 * π < π⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[sin_¬_eq_0_thm]);
a(REPEAT strip_tac);
a(ante_tac(∀_elim⌜1/2 * π⌝ cos_squared_plus_sin_squared_thm));
a(asm_rewrite_tac[
	rewrite_rule[](list_∀_elim[⌜Sin(1/2 * π)⌝, ⌜ℕℝ 1⌝]square_root_unique_thm)]);
a(contr_tac);
a(lemma_tac⌜Sin(1/2 * π) < ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[rewrite_rule[open_interval_def] sin_0_π_0_less_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_plus_π_over_2_thm⦎ = save_thm ( "sin_cos_plus_π_over_2_thm", (
set_goal([], ⌜∀x⦁
	Sin (x + (1/2) * π) = Cos x
∧	Cos(x + (1/2) * π) = ~(Sin x)
⌝);
a(rewrite_tac[sin_cos_plus_thm, sin_cos_π_over_2_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cos_¬_eq_0_thm⦎ = save_thm ( "cos_¬_eq_0_thm", (
set_goal([], ⌜∀x⦁
	~(1/2) * π < x ∧ x < (1/2) * π ⇒ ¬Cos x = ℕℝ 0⌝);
a(contr_tac);
a(lemma_tac⌜Sin (x + (1/2) * π) = ℕℝ 0⌝
	THEN1 asm_rewrite_tac[sin_cos_plus_π_over_2_thm]);
a(lemma_tac⌜¬Sin (x + (1/2) * π) = ℕℝ 0⌝
	THEN1 (bc_thm_tac sin_¬_eq_0_thm
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cos_eq_0_thm⦎ = save_thm ( "cos_eq_0_thm", (
set_goal([], ⌜∀x⦁Cos x = ℕℝ 0 ⇔ 
		(∃m⦁ x = (1/2) * π + ℕℝ m * π)
	∨ (∃m⦁ x = (1/2) * π - ℕℝ m * π)⌝);
a(∀_tac THEN rewrite_tac[
	rewrite_rule[ℝ_plus_assoc_thm]
		(∀_elim⌜x + ~(1/2 * π)⌝
			sin_cos_plus_π_over_2_thm),
	pc_rule1 "ℝ_lin_arith" prove_rule[]
		⌜∀a⦁ ~ a = ℕℝ 0 ⇔ a = ℕℝ 0⌝,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
		⌜∀a b c:ℝ⦁ a + ~b = c ⇔ a = b + c⌝,
	π_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_plus_π_thm⦎ = save_thm ( "sin_cos_plus_π_thm", (
set_goal([], ⌜∀x⦁
	Sin (x + π) = ~(Sin x)
∧	Cos(x + π) = ~(Cos x)
⌝);
a(pure_once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜π = 1/2 * π + 1/2 * π⌝]);
a(rewrite_tac[sin_cos_plus_π_over_2_thm, ℝ_plus_assoc_thm1]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_π_thm⦎ = save_thm ( "sin_cos_π_thm", (
set_goal([], ⌜
	Sin π = ℕℝ 0 
∧	Cos π = ~(ℕℝ 1)
⌝);
a(accept_tac(rewrite_rule[sin_def] (∀_elim⌜ℕℝ 0⌝ sin_cos_plus_π_thm)));
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_plus_2_π_thm⦎ = save_thm ( "sin_cos_plus_2_π_thm", (
set_goal([], ⌜∀x⦁
	Sin (x + ℕℝ 2 * π) = Sin x
∧	Cos(x + ℕℝ 2 * π) = Cos x
⌝);
a(pure_once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜ℕℝ 2 * π = π + π⌝]);
a(rewrite_tac[sin_cos_plus_π_thm, ℝ_plus_assoc_thm1]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_2_π_thm⦎ = save_thm ( "sin_cos_2_π_thm", (
set_goal([], ⌜
	Sin (ℕℝ 2 * π) = ℕℝ 0 
∧	Cos (ℕℝ 2 * π) = ℕℝ 1
⌝);
a(accept_tac(rewrite_rule[sin_def] (∀_elim⌜ℕℝ 0⌝ sin_cos_plus_2_π_thm)));
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_plus_even_times_π_thm⦎ = save_thm ( "sin_cos_plus_even_times_π_thm", (
set_goal([], ⌜∀x m⦁
	Sin (x + ℕℝ (2*m) * π) = Sin x
∧	Cos(x + ℕℝ (2*m) * π) = Cos x
⌝);
a(rewrite_tac[ℕℝ_times_homomorphism_thm]);
a(REPEAT ∀_tac THEN induction_tac⌜m:ℕ⌝ THEN1 rewrite_tac[]);
a(rewrite_tac[ℕℝ_plus_homomorphism_thm, ℝ_times_plus_distrib_thm]);
a(asm_rewrite_tac[ℝ_plus_assoc_thm1, sin_cos_plus_2_π_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_even_times_π_thm⦎ = save_thm ( "sin_cos_even_times_π_thm", (
set_goal([], ⌜∀m⦁
	Sin (ℕℝ (2*m) * π) = ℕℝ 0
∧	Cos(ℕℝ (2*m) * π) = ℕℝ 1
⌝);
a(rewrite_tac[rewrite_rule[sin_def] (∀_elim⌜ℕℝ 0⌝ sin_cos_plus_even_times_π_thm)]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀x y⦁
	x <  y
∧	Sin x = Sin y
∧	Cos x = Cos y
⇒	∃m⦁ y = x + ℕℝ (2 * m) * π
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜Sin(y + ~x) = ℕℝ 0 ∧ Cos(y + ~x) = ℕℝ 1⌝ THEN1
	(asm_rewrite_tac[sin_cos_plus_thm, sin_cos_minus_thm]THEN
		conv_tac (ONCE_MAP_C ℝ_anf_conv)
		THEN rewrite_tac[cos_squared_plus_sin_squared_thm]));
a(fc_tac[π_def]);
(* *** Goal "1" *** *)
a(strip_asm_tac(∀_elim⌜m⌝ even_odd_thm) THEN all_var_elim_asm_tac1);
(* *** Goal "1.1" *** *)
a(∃_tac⌜n⌝);
a(all_fc_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]⌜∀z⦁y + ~x = z ⇒ y = x + z⌝]);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜Cos(y + ~x) = ~(ℕℝ 1)⌝ THEN_LIST [id_tac, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(POP_ASM_T rewrite_thm_tac THEN DROP_ASMS_T discard_tac);
a(rewrite_tac[ℕℝ_plus_homomorphism_thm, ℝ_times_plus_distrib_thm,
	sin_cos_plus_π_thm, sin_cos_even_times_π_thm]);
(* *** Goal "2" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 1);
a(bc_thm_tac ℕℝ_0_less_¬_ℕℝ_times_π_thm);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏sin_cos_period_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_period_thm⦎ = save_thm ( "sin_cos_period_thm", (
set_goal([], ⌜∀x y⦁
	x <  y
⇒	(Sin x = Sin y ∧ Cos x = Cos y ⇔ ∃m⦁ y = x + ℕℝ (2 * m) * π)
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[sin_cos_period_lemma]);
a(∃_tac⌜m⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(rewrite_tac[sin_cos_plus_even_times_π_thm]);
(* *** Goal "3" *** *)
a(all_var_elim_asm_tac1);
a(rewrite_tac[sin_cos_plus_even_times_π_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀x⦁
	Abs x ≤ ℕℝ 1
⇒	∃z⦁ z ∈ ClosedInterval (ℕℝ 0) π ∧ Cos z = x
⌝);
a(rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
a(lemma_tac⌜~(ℕℝ 1) ≤ x ∧ x ≤ ℕℝ 1⌝ THEN1
	(POP_ASM_T ante_tac THEN cases_tac ⌜ℕℝ 0 ≤ x⌝ THEN
		asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(ante_tac (list_∀_elim[⌜Cos⌝, ⌜ℕℝ 0⌝, ⌜π⌝] intermediate_value_thm));
a(asm_rewrite_tac[sin_cos_cts_thm, cos_def, sin_cos_π_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜x = ℕℝ 1⌝ THEN1
	(∃_tac⌜ℕℝ 0⌝ THEN asm_rewrite_tac[cos_def] THEN
		strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(cases_tac⌜x = ~(ℕℝ 1)⌝ THEN1
	(∃_tac⌜ π⌝ THEN asm_rewrite_tac[sin_cos_π_thm] THEN
		strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜~(ℕℝ 1) < x ∧ x < ℕℝ 1⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏sin_cos_onto_unit_circle_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_onto_unit_circle_thm⦎ = save_thm ( "sin_cos_onto_unit_circle_thm", (
set_goal([], ⌜∀x y⦁
	x ^ 2 + y ^ 2 = ℕℝ 1
⇒	∃z⦁ ℕℝ 0 ≤ z ∧ z < ℕℝ 2 * π ∧ x = Cos z ∧ y = Sin z
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[sum_squares_abs_bound_thm1]);
a(all_fc_tac[rewrite_rule[closed_interval_def] sin_cos_onto_unit_circle_lemma]);
a(all_var_elim_asm_tac1);
a(strip_asm_tac (∀_elim⌜z⌝ cos_squared_plus_sin_squared_thm));
a(lemma_tac⌜y ^ 2 = Sin z ^ 2⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(fc_tac[square_root_unique_thm]);
(* *** Goal "1" *** *)
a(∃_tac⌜z⌝ THEN asm_rewrite_tac[] THEN 
	strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜z = ℕℝ 0⌝ THEN1
	(all_var_elim_asm_tac1 THEN all_asm_ante_tac THEN rewrite_tac[sin_def]
		THEN REPEAT strip_tac));
(* *** Goal "2.1" *** *)
a(∃_tac⌜ℕℝ 0⌝ THEN
	asm_rewrite_tac[sin_def]
		 THEN strip_asm_tac π_def  THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜~z + ℕℝ 2 * π⌝ THEN
	asm_rewrite_tac[sin_cos_plus_2_π_thm, sin_cos_minus_thm, closed_interval_def]
		 THEN strip_asm_tac π_def  THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sin_cos_onto_unit_circle_thm1⦎ = save_thm ( "sin_cos_onto_unit_circle_thm1", (
set_goal([], ⌜∀x y⦁
	x ^ 2 + y ^ 2 = ℕℝ 1
⇒	∃⋎1z⦁ ℕℝ 0 ≤ z ∧ z < ℕℝ 2 * π ∧ x = Cos z ∧ y = Sin z
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[sin_cos_onto_unit_circle_thm]);
a(∃⋎1_tac⌜z⌝ THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(strip_asm_tac (list_∀_elim[⌜z'⌝, ⌜z⌝] ℝ_less_cases_thm));
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [2, 3] (MAP_EVERY (strip_asm_tac o eq_sym_rule)));
a(all_fc_tac[sin_cos_period_thm]);
a(all_var_elim_asm_tac1);
a(strip_asm_tac(∀_elim⌜m⌝ℕ_cases_thm) THEN all_var_elim_asm_tac1 THEN1 rewrite_tac[]);
a(lemma_tac⌜ℕℝ 2 * π ≤ ℕℝ (2 * (i + 1)) * π⌝ THEN1
	(once_rewrite_tac[times_comm_thm] THEN
	rewrite_tac[ℕℝ_times_homomorphism_thm, ℝ_times_assoc_thm] THEN
	bc_thm_tac (∧_left_elim ℕℝ_plus_1_times_bound_thm) THEN
	strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[pc_rule1 "ℝ_lin_arith"  prove_rule[]⌜
	∀a b c d⦁ℕℝ 0 ≤  a ∧ a < b ∧ b ≤ d ⇒ ¬a + d < b⌝]);
(* *** Goal "2" *** *)
a(all_fc_tac[sin_cos_period_thm]);
a(all_var_elim_asm_tac1);
a(strip_asm_tac(∀_elim⌜m⌝ℕ_cases_thm) THEN all_var_elim_asm_tac1 THEN1 rewrite_tac[]);
a(lemma_tac⌜ℕℝ 2 * π ≤ ℕℝ (2 * (i + 1)) * π⌝ THEN1
	(once_rewrite_tac[times_comm_thm] THEN
	rewrite_tac[ℕℝ_times_homomorphism_thm, ℝ_times_assoc_thm] THEN
	bc_thm_tac (∧_left_elim ℕℝ_plus_1_times_bound_thm) THEN
	strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[pc_rule1 "ℝ_lin_arith"  prove_rule[]⌜
	∀a b c d⦁ℕℝ 0 ≤  a ∧ a < b ∧ b ≤ d ⇒ ¬a + d < b⌝]);
pop_thm()
));

=TEX
\subsection{L'H\^{o}pital's Rule}
%%%%
%%%% RIGHT-HAND LIMITS
%%%%
=SML

val ⦏lim_right_lim_seq_thm⦎ = save_thm ( "lim_right_lim_seq_thm", (
set_goal([], ⌜∀f c x⦁
	(f +#-> c) x
⇔	∀s⦁ s -> x ∧ (∀m⦁x < s m) ⇒ (λm⦁f(s m)) -> c
⌝);
a(rewrite_tac[lim_right_def, lim_seq_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(lemma_tac⌜ℕℝ 0 < b + ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 6 ⌜b + ~x⌝);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(POP_ASM_T ante_tac);
a(lemma_tac⌜x < s m⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜ℕℝ 0 ≤ s m + ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(conv_tac (LEFT_C (rewrite_conv[ℝ_abs_def])) THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 2 THEN strip_tac);
a(lemma_tac⌜∃s⦁
	∀ m⦁ x < s m ∧ s m < x + ℕℝ (m+1) ⋏-⋏1∧ ¬Abs(f(s m) + ~c) < e⌝);
(* *** Goal "2.1" *** *)
a(prove_∃_tac THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < ℕℝ(m' + 1)⌝ THEN1
	rewrite_tac[ℕℝ_less_thm]);
a(all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(spec_nth_asm_tac 4 ⌜x + ℕℝ (m' + 1) ⋏-⋏1⌝);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(∃_tac⌜s⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 4 discard_tac 
	THEN all_fc_tac[ℝ_archimedean_recip_thm]);
a(∃_tac⌜m+1⌝ THEN REPEAT strip_tac);
a(spec_nth_asm_tac 4 ⌜m'⌝);
a(lemma_tac⌜ℕℝ 0 < ℕℝ (m+1) ∧ ℕℝ 0 < ℕℝ (m'+1)⌝ THEN1 rewrite_tac[ℕℝ_0_less_thm]);
a(lemma_tac⌜ℕℝ (m+1) < ℕℝ (m'+1)⌝ THEN1 
	(asm_rewrite_tac[ℕℝ_less_thm] THEN PC_T1 "lin_arith" asm_prove_tac[]));
a(all_fc_tac[ℝ_less_recip_less_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ s m' + ~x⌝ THEN1  PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_abs_def]);
a(all_fc_tac[
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀t u⦁ x < s m' ∧ s m' < x + t ∧ t < u ∧ u < e' ⇒ s m' + ~x < e'⌝]);
(* *** Goal "2.2.2" *** *)
a(∃_tac⌜e⌝ THEN REPEAT strip_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_lim_right_thm⦎ = save_thm ( "lim_fun_lim_right_thm", (
set_goal([], ⌜∀f c x⦁
	(f --> c) x
⇔	(f +#-> c) x ∧ ((λy⦁f(~y)) +#-> c) (~x)
⌝);
a(rewrite_tac[lim_right_def, lim_fun_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜x + d⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(lemma_tac⌜ℕℝ 0 ≤ x' + ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]); 
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜~x + d⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(lemma_tac⌜¬ℕℝ 0 ≤ ~x' + ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]); 
(* *** Goal "3" *** *)
a(LIST_DROP_NTH_ASM_T [2, 3] all_fc_tac);
a(lemma_tac⌜ℕℝ 0 < b' + ~x ∧ ℕℝ 0 < b + x⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]); 
a(strip_asm_tac(list_∀_elim[⌜b' + ~x⌝, ⌜b + x⌝]ℝ_bound_below_2_thm));
a(∃_tac⌜d⌝ THEN REPEAT strip_tac);
a(swap_nth_asm_concl_tac 2 THEN cases_tac⌜ℕℝ 0 ≤ y + ~x⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN swap_nth_asm_concl_tac 2);
(* *** Goal "3.1" *** *)
a(DROP_NTH_ASM_T 9 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.2" *** *)
a(pure_once_rewrite_tac[prove_rule[]⌜y = ~(~y)⌝]);
a(DROP_NTH_ASM_T 11 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏const_lim_right_thm⦎ = save_thm ( "const_lim_right_thm", (
set_goal([], ⌜∀c x⦁ ((λx⦁c) +#-> c) x ⌝);
a(rewrite_tac[lim_right_lim_seq_thm] THEN REPEAT strip_tac);
a(rewrite_tac[const_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏id_lim_right_thm⦎ = save_thm ( "id_lim_right_thm", (
set_goal([], ⌜∀x⦁ ((λx⦁x) +#-> x) x ⌝);
a(rewrite_tac[lim_right_def] THEN REPEAT strip_tac);
a(∃_tac⌜x + e⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 ≤ x' + ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_abs_def] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_lim_right_thm⦎ = save_thm ( "plus_lim_right_thm", (
set_goal([], ⌜∀f1 c1 f2 c2 x⦁
	(f1 +#-> c1) x ∧ (f2 +#-> c2) x
⇒	((λx⦁f1 x + f2 x) +#-> c1 + c2) x
⌝);
a(rewrite_tac[lim_right_lim_seq_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3, 4] all_fc_tac);
a(ALL_FC_T (rewrite_tac o mapfilter (rewrite_rule[])) [plus_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_lim_right_thm⦎ = save_thm ( "times_lim_right_thm", (
set_goal([], ⌜∀f1 c1 f2 c2 x⦁
	(f1 +#-> c1) x ∧ (f2 +#-> c2) x
⇒	((λx⦁f1 x * f2 x) +#-> c1 * c2) x
⌝);
a(rewrite_tac[lim_right_lim_seq_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3, 4] all_fc_tac);
a(ALL_FC_T (rewrite_tac o mapfilter (rewrite_rule[])) [times_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏poly_lim_right_thm⦎ = save_thm ( "poly_lim_right_thm", (
set_goal([], ⌜∀f g c x⦁
	f ∈ PolyFunc
∧	(g +#-> c) x
⇒	((λx⦁f(g x)) +#-> f c) x
⌝);
a(rewrite_tac[lim_right_lim_seq_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(ALL_FC_T (rewrite_tac o mapfilter (rewrite_rule[])) [poly_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏recip_lim_right_thm⦎ = save_thm ( "recip_lim_right_thm", (
set_goal([], ⌜∀f c x⦁
	(f +#-> c)x
∧	¬c = ℕℝ 0
⇒	((λx⦁f x ⋏-⋏1) +#-> c ⋏-⋏1) x
⌝);
a(rewrite_tac[lim_right_lim_seq_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(ALL_FC_T (rewrite_tac o mapfilter (rewrite_rule[])) [recip_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_right_unique_thm⦎ = save_thm ( "lim_right_unique_thm", (
set_goal([], ⌜∀f c d x⦁
	(f +#-> c) x ∧ (f +#-> d) x
⇒	c = d
⌝);
a(rewrite_tac[lim_right_lim_seq_thm] THEN REPEAT strip_tac);
a(DROP_ASMS_T (MAP_EVERY(ante_tac o ∀_elim⌜(λ m⦁ x + ℕℝ (m + 1) ⋏-⋏1)⌝)));
a(rewrite_tac[lim_seq_recip_ℕ_thm, ℕℝ_0_less_recip_thm]
	THEN REPEAT strip_tac);
a(EXTEND_PC_T1 "'mmp1" (ALL_FC_T rewrite_tac) [lim_seq_unique_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cts_lim_right_thm⦎ = save_thm ( "cts_lim_right_thm", (
set_goal([], ⌜∀f c x⦁
	f Cts x
∧	(f +#-> c)x
⇒	f x = c
⌝);
a(rewrite_tac[lim_right_lim_seq_thm, cts_lim_seq_thm] THEN REPEAT strip_tac);
a(strip_asm_tac(∀_elim⌜x⌝lim_seq_recip_ℕ_thm));
a(lemma_tac⌜∀ m⦁ x < (λ m⦁ x + ℕℝ (m + 1) ⋏-⋏1) m⌝
	THEN1 rewrite_tac[ℕℝ_0_less_recip_thm]);
a(all_asm_fc_tac[]);
a(all_asm_fc_tac[lim_seq_unique_thm]);
pop_thm()
));

=TEX
%%%%
%%%% LIMITS AT INFINITY
%%%%
=SML

val ⦏lim_infinity_lim_seq_thm⦎ = save_thm ( "lim_infinity_lim_seq_thm", (
set_goal([], ⌜∀f c⦁
	f -+#> c
⇔	∀s⦁ (∀m:ℕ⦁ℕℝ m ≤ s m) ⇒ (λm⦁f(s m)) -> c
⌝);
a(rewrite_tac[lim_infinity_def, lim_seq_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(strip_asm_tac (∀_elim⌜b⌝ ℝ_archimedean_thm));
a(∃_tac⌜m⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ m ≤ ℕℝ m' ∧ ℕℝ m' ≤ s m'⌝ THEN1 asm_rewrite_tac[ℕℝ_≤_thm]);
a(GET_NTH_ASM_T 5 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 2 THEN strip_tac);
a(lemma_tac⌜∃s⦁
	∀ m⦁ ℕℝ m ≤ s m ∧ ¬Abs(f(s m) + ~c) < e⌝);
(* *** Goal "2.1" *** *)
a(prove_∃_tac THEN REPEAT strip_tac);
a(TOP_ASM_T (strip_asm_tac o ∀_elim⌜ℕℝ m'⌝));
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[ℝ_≤_def]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜s⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜e⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜n⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_infinity_lim_right_thm⦎ = save_thm ( "lim_infinity_lim_right_thm", (
set_goal([], ⌜∀f c⦁ (f -+#> c) ⇔ ((λx⦁f(x ⋏-⋏1)) +#-> c) (ℕℝ 0) ⌝);
a(rewrite_tac[lim_right_def, lim_infinity_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(strip_asm_tac (list_∀_elim[⌜ℕℝ 0⌝, ⌜b⌝] ℝ_max_2_thm));
a(lemma_tac⌜ℕℝ 0 < z ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(∃_tac⌜z ⋏-⋏1⌝ THEN REPEAT strip_tac);
a(all_fc_tac [ℝ_less_recip_less_thm]);
a(POP_ASM_T ante_tac
	THEN lemma_tac⌜¬z = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses] THEN REPEAT strip_tac);
a(lemma_tac⌜b < x ⋏-⋏1⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(lemma_tac⌜ℕℝ 0 < b ⋏-⋏1⌝ THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(∃_tac⌜b ⋏-⋏1⌝ THEN REPEAT strip_tac);
a(all_fc_tac [ℝ_less_recip_less_thm]);
a(POP_ASM_T ante_tac
	THEN lemma_tac⌜¬b = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses] THEN REPEAT strip_tac);
a(all_fc_tac[ℝ_less_trans_thm]);
a(lemma_tac⌜ℕℝ 0 < x ⋏-⋏1⌝ THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(POP_ASM_T ante_tac
	THEN lemma_tac⌜¬x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_right_lim_infinity_thm⦎ = save_thm ( "lim_right_lim_infinity_thm", (
set_goal([], ⌜∀f c⦁
	((λx⦁f (x ⋏-⋏1)) +#-> c) (ℕℝ 0)
⇔	f -+#> c⌝);
a(rewrite_tac[lim_infinity_lim_right_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏const_lim_infinity_thm⦎ = save_thm ( "const_lim_infinity_thm", (
set_goal([], ⌜∀c⦁	(λx⦁c) -+#> c⌝);
a(rewrite_tac[lim_infinity_lim_seq_thm]
	THEN REPEAT strip_tac);
a(rewrite_tac[const_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏id_lim_infinity_thm⦎ = save_thm ( "id_lim_infinity_thm", (
set_goal([], ⌜∀c⦁	¬(λx⦁x) -+#> c⌝);
a(rewrite_tac[lim_infinity_def] THEN REPEAT strip_tac);
a(∃_tac⌜ℕℝ 1⌝ THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜b⌝, ⌜c + ℕℝ 1⌝] ℝ_max_2_thm));
a(∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 ≤ z + ~c ⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[ℝ_abs_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_lim_infinity_thm⦎ = save_thm ( "plus_lim_infinity_thm", (
set_goal([], ⌜∀f1 c1 f2 c2⦁
	f1 -+#> c1 ∧ f2 -+#> c2
⇒	(λx⦁f1 x + f2 x) -+#> c1 + c2
⌝);
a(rewrite_tac[lim_infinity_lim_seq_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2, 3] all_fc_tac);
a(ALL_FC_T (rewrite_tac o map (rewrite_rule[])) [plus_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_lim_infinity_thm⦎ = save_thm ( "times_lim_infinity_thm", (
set_goal([], ⌜∀f1 c1 f2 c2⦁
	f1 -+#> c1 ∧ f2 -+#> c2
⇒	(λx⦁f1 x * f2 x) -+#> c1 * c2
⌝);
a(rewrite_tac[lim_infinity_lim_seq_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2, 3] all_fc_tac);
a(ALL_FC_T (rewrite_tac o map (rewrite_rule[])) [times_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏poly_lim_infinity_thm⦎ = save_thm ( "poly_lim_infinity_thm", (
set_goal([], ⌜∀f g c⦁
	f ∈ PolyFunc
∧	g -+#> c
⇒	(λx⦁f(g x)) -+#> f c
⌝);
a(rewrite_tac[lim_infinity_lim_seq_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(ALL_FC_T (rewrite_tac o map (rewrite_rule[])) [poly_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏recip_lim_infinity_thm⦎ = save_thm ( "recip_lim_infinity_thm", (
set_goal([], ⌜∀f c⦁
	f -+#> c
∧	¬c = ℕℝ 0
⇒	(λx⦁f x ⋏-⋏1) -+#> c ⋏-⋏1
⌝);
a(rewrite_tac[lim_infinity_lim_seq_thm] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(ALL_FC_T (rewrite_tac o map (rewrite_rule[])) [recip_lim_seq_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏recip_lim_infinity_0_thm⦎ = save_thm ( "recip_lim_infinity_0_thm", (
set_goal([], ⌜(λ x⦁ x ⋏-⋏1) -+#> ℕℝ 0⌝);
a(rewrite_tac[lim_infinity_lim_right_thm]);
a(rewrite_tac[lim_right_def] THEN REPEAT strip_tac);
a(∃_tac⌜e⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜¬x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_infinity_unique_thm⦎ = save_thm ( "lim_infinity_unique_thm", (
set_goal([], ⌜∀f c d⦁
	f -+#> c ∧ f -+#> d
⇒	c = d
⌝);
a(rewrite_tac[lim_infinity_lim_seq_thm] THEN REPEAT strip_tac);
a(DROP_ASMS_T (MAP_EVERY(ante_tac o ∀_elim⌜ℕℝ⌝)));
a(rewrite_tac[] THEN REPEAT strip_tac);
a(EXTEND_PC_T1 "'mmp1" (ALL_FC_T rewrite_tac)[lim_seq_unique_thm]);
pop_thm()
));

=TEX
%%%%
%%%% DIVERGENCE TO INFINITY AT INFINITY
%%%%
=SML

val ⦏div_infinity_pos_thm⦎ = save_thm ( "div_infinity_pos_thm", (
set_goal([], ⌜∀f⦁
	f -+#>+#
⇒	∃b⦁ℕℝ 0 < b ∧ ∀x⦁b < x ⇒ ℕℝ 0 < f x
⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜ℕℝ 0⌝);
a(strip_asm_tac(list_∀_elim[⌜b⌝, ⌜ℕℝ 0⌝]ℝ_max_2_thm));
a(∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏const_plus_div_infinity_thm⦎ = save_thm ( "const_plus_div_infinity_thm", (
set_goal([], ⌜∀f c⦁
	f -+#>+# 
⇒	(λx⦁c + f x) -+#>+#
⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 1 ⌜x + ~c⌝);
a(∃_tac⌜b⌝ THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏id_div_infinity_thm⦎ = save_thm ( "id_div_infinity_thm", (
set_goal([], ⌜(λx⦁x) -+#>+#⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏plus_div_infinity_thm⦎ = save_thm ( "plus_div_infinity_thm", (
set_goal([], ⌜∀f g⦁
	f -+#>+# ∧ g -+#>+#
⇒	(λx⦁f x + g x) -+#>+#
⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜ℕℝ 0⌝]ℝ_max_2_thm));
a(LIST_DROP_NTH_ASM_T [3, 4] (MAP_EVERY (strip_asm_tac o ∀_elim⌜z⌝)));
a(strip_asm_tac(list_∀_elim[⌜b⌝, ⌜b'⌝]ℝ_max_2_thm));
a(∃_tac⌜z'⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4, 5] (MAP_EVERY (strip_asm_tac o ∀_elim⌜y⌝))
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏const_times_div_infinity_thm⦎ = save_thm ( "const_times_div_infinity_thm", (
set_goal([], ⌜∀f c⦁
	f -+#>+# ∧ ℕℝ 0 < c 
⇒	(λx⦁c * f x) -+#>+#
⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜ℕℝ 0⌝, ⌜x⌝]ℝ_max_2_thm));
a(spec_nth_asm_tac 4 ⌜z * c ⋏-⋏1⌝);
a(∃_tac⌜b⌝ THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
a(lemma_tac⌜ℕℝ 0 < c ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(LEMMA_T⌜(c ⋏-⋏1 * x) < c ⋏-⋏1 * z⌝ ante_tac
	THEN1 all_fc_tac[ℝ_times_mono_thm]);
a(STRIP_T (strip_asm_tac o once_rewrite_rule[ℝ_times_comm_thm]));
a(lemma_tac⌜(x * c ⋏-⋏1) < f y⌝
	THEN1 all_fc_tac[ℝ_less_trans_thm]);
a(LEMMA_T⌜c * (x * c ⋏-⋏1) < c * f y⌝ ante_tac
	THEN1 all_fc_tac[ℝ_times_mono_thm]);
a(rewrite_tac[∀_elim⌜x⌝ℝ_times_order_thm]);
a(lemma_tac⌜¬c = ℕℝ 0⌝
	THEN1  (GET_ASM_T ⌜ℕℝ 0 < c⌝ ante_tac
		THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏times_div_infinity_thm⦎ = save_thm ( "times_div_infinity_thm", (
set_goal([], ⌜∀f g⦁
	f -+#>+# ∧ g -+#>+#
⇒	(λx⦁f x * g x) -+#>+#
⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜ℕℝ 1⌝]ℝ_max_2_thm));
a(LIST_DROP_NTH_ASM_T [3, 4] (MAP_EVERY (strip_asm_tac o ∀_elim⌜z⌝)));
a(strip_asm_tac(list_∀_elim[⌜b⌝, ⌜b'⌝]ℝ_max_2_thm));
a(∃_tac⌜z'⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [4, 5] (MAP_EVERY (strip_asm_tac o ∀_elim⌜y⌝))
	THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_less_trans_thm THEN ∃_tac⌜f y * ℕℝ 1⌝);
a(strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_times_mono_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏power_div_infinity_thm⦎ = save_thm ( "power_div_infinity_thm", (
set_goal([], ⌜∀m⦁
	(λx⦁ x ^ (m + 1)) -+#>+#
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜m⌝ THEN all_asm_ante_tac
	THEN rewrite_tac[ℝ_ℕ_exp_def, id_div_infinity_thm]);
a(ante_tac(list_∀_elim[⌜λx:ℝ⦁x⌝, ⌜λ x:ℝ⦁ x * x ^ m⌝]
times_div_infinity_thm));
a(rewrite_tac[id_div_infinity_thm] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏less_div_infinity_thm⦎ = save_thm ( "less_div_infinity_thm", (
set_goal([], ⌜∀f g a⦁
	f -+#>+# ∧ (∀x⦁a < x ⇒ f x < g x)
⇒	g -+#>+#
⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜x⌝);
a(strip_asm_tac(list_∀_elim[⌜a⌝, ⌜b⌝]ℝ_max_2_thm));
a(∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(all_fc_tac[ℝ_less_trans_thm]
	THEN all_asm_fc_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏bounded_deriv_div_infinity_thm⦎ = save_thm ( "bounded_deriv_div_infinity_thm", (
set_goal([], ⌜∀f df a c⦁
	ℕℝ 0 < c
∧	(∀x⦁a ≤ x ⇒ (f Deriv df x) x)
∧	(∀x⦁a ≤ x ⇒ c < df x)
⇒	f -+#>+#
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀x⦁a < x ⇒ f a + c * (x + ~a) < f x⌝);
(* *** Goal "1" *** *)
a(contr_tac);
a(strip_asm_tac(rewrite_rule[](list_∀_elim[⌜f⌝, ⌜df⌝, ⌜a⌝, ⌜x⌝] mean_value_thm1)));
(* *** Goal "1.1" *** *)
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
(* *** Goal "1.2" *** *)
a(lemma_tac⌜a ≤ x'⌝ THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(LEMMA_T⌜f x + ~(f a) ≤ c * (x + ~a)⌝ ante_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(pure_once_rewrite_tac[ℝ_times_comm_thm]);
a(asm_rewrite_tac[ℝ_¬_≤_less_thm]);
a(bc_thm_tac ℝ_times_mono_thm);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
(* *** Goal "2" *** *)
a(ante_tac(pure_once_rewrite_rule[ℝ_plus_comm_thm]
	(list_∀_elim[⌜λx:ℝ⦁x⌝, ⌜~a⌝]const_plus_div_infinity_thm)));
a(rewrite_tac[id_div_infinity_thm] THEN REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜λ x⦁ x + ~ a⌝, ⌜c⌝]const_times_div_infinity_thm));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(ante_tac(list_∀_elim[⌜λ x⦁ c * (x + ~ a)⌝, ⌜f a⌝]const_plus_div_infinity_thm));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(bc_thm_tac less_div_infinity_thm);
a(∃_tac⌜a⌝ THEN ∃_tac⌜λ x⦁ f a + c * (x + ~ a)⌝
	THEN REPEAT strip_tac);
a(rewrite_tac[] THEN LIST_DROP_NTH_ASM_T [5] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏exp_div_infinity_thm⦎ = save_thm ( "exp_div_infinity_thm", (
set_goal([], ⌜Exp -+#>+#⌝);
a(bc_thm_tac bounded_deriv_div_infinity_thm);
a(∃_tac⌜Exp⌝ THEN ∃_tac⌜ℕℝ 0⌝ THEN ∃_tac⌜1/2⌝);
a(rewrite_tac[exp_def]);
a(REPEAT strip_tac THEN bc_thm_tac ℝ_less_≤_trans_thm);
a(∃_tac⌜Exp (ℕℝ 0)⌝ THEN REPEAT strip_tac
	THEN1 rewrite_tac[exp_def]);
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_≤_def]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
a(all_fc_tac[exp_less_mono_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏log_div_infinity_thm⦎ = save_thm ( "log_div_infinity_thm", (
set_goal([], ⌜Log -+#>+#⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜ℕℝ 0⌝, ⌜x⌝] ℝ_max_2_thm));
a(∃_tac⌜Exp z⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜Log(Exp z) < Log y⌝ ante_tac
	THEN1 (bc_thm_tac log_less_mono_thm
		THEN asm_rewrite_tac[exp_0_less_thm]));
a(rewrite_tac[log_def]);
a(REPEAT strip_tac THEN all_fc_tac[ℝ_less_trans_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏div_infinity_times_recip_thm⦎ = save_thm ( "div_infinity_times_recip_thm", (
set_goal([], ⌜∀f a e⦁
	f -+#>+# ∧ ℕℝ 0 < a ∧ ℕℝ 0 < e
⇒	∃b⦁ ∀x⦁ b < x ⇒ a * (f x) ⋏-⋏1 < e
⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 3 ⌜a * e ⋏-⋏1⌝);
a(∃_tac⌜b⌝ THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
a(lemma_tac⌜ℕℝ 0 < e ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜ℕℝ 0 < a * e ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_times_thm]);
a(lemma_tac⌜ℕℝ 0 < f x⌝
	THEN1 all_fc_tac[ℝ_less_trans_thm]);
a(lemma_tac⌜ℕℝ 0 < f x ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(LEMMA_T⌜f x ⋏-⋏1 * e * (a * e ⋏-⋏1) < f x ⋏-⋏1 * e * f x⌝ ante_tac
	THEN1 REPEAT (bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac));
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀f1 e1⦁f1 * e * a * e1 = a * f1 * e * e1
	∧ f1 * e * f x = e * f x * f1⌝]);
a(lemma_tac⌜¬e = ℕℝ 0 ∧ ¬ f x = ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏div_infinity_lim_right_thm⦎ = save_thm ( "div_infinity_lim_right_thm", (
set_goal([], ⌜∀f⦁
	f -+#>+#
⇔	((λx⦁(f (x ⋏-⋏1))⋏-⋏1) +#-> ℕℝ 0) (ℕℝ 0)
∧	∃b⦁∀x⦁ b < x ⇒ ℕℝ 0 < f x⌝);
a(REPEAT strip_tac);
a(POP_ASM_T ante_tac
	THEN rewrite_tac[div_infinity_def, lim_right_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜ℕℝ 0 < e ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(spec_nth_asm_tac 3 ⌜e ⋏-⋏1⌝);
a(strip_asm_tac (list_∀_elim[⌜ℕℝ 0⌝, ⌜b⌝] ℝ_max_2_thm));
a(lemma_tac⌜ℕℝ 0 < z ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(∃_tac⌜z ⋏-⋏1⌝ THEN REPEAT strip_tac);
a(all_fc_tac [ℝ_less_recip_less_thm]);
a(POP_ASM_T ante_tac
	THEN lemma_tac⌜¬z = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses] THEN REPEAT strip_tac);
a(lemma_tac⌜b < x ⋏-⋏1⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(spec_nth_asm_tac 9 ⌜x ⋏-⋏1⌝);
a(lemma_tac⌜ℕℝ 0 < f (x ⋏-⋏1)⌝ THEN all_fc_tac[ℝ_less_trans_thm]);
a(lemma_tac⌜ℕℝ 0 < f (x ⋏-⋏1) ⋏-⋏1⌝ THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
a(LEMMA_T ⌜f (x ⋏-⋏1) ⋏-⋏1 < e ⋏-⋏1 ⋏-⋏1⌝ ante_tac
	THEN1 all_fc_tac[ℝ_less_recip_less_thm]);
a(lemma_tac⌜¬e = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
(* *** Goal "2" *** *)
a(all_fc_tac[div_infinity_pos_thm]);
a(∃_tac⌜b⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a(all_asm_ante_tac
	THEN rewrite_tac[div_infinity_def, lim_right_def]
	THEN REPEAT strip_tac);
a(cases_tac⌜¬ℕℝ 0 < x⌝
	THEN1 (∃_tac⌜b⌝ THEN REPEAT strip_tac
		THEN all_asm_fc_tac[]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(DROP_NTH_ASM_T 4 (strip_asm_tac o ∀_elim⌜x ⋏-⋏1⌝));
a(strip_asm_tac(list_∀_elim[⌜b' ⋏-⋏1⌝, ⌜b⌝]ℝ_max_2_thm));
a(∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < b' ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜ℕℝ 0 < y ∧ ¬y = ℕℝ 0 ∧ ¬b' = ℕℝ 0 ∧ ¬x = ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜ℕℝ 0 < y ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜b' ⋏-⋏1 < y⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜y ⋏-⋏1 < b' ⋏-⋏1 ⋏-⋏1⌝ ante_tac
	THEN1 all_fc_tac[ℝ_less_recip_less_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 12 (ante_tac o ∀_elim⌜y ⋏-⋏1⌝));
a(ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
a(lemma_tac⌜ℕℝ 0 < f y⌝ THEN1
	(DROP_NTH_ASM_T 15 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ 0 < f y ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜¬f y = ℕℝ 0 ∧ ¬f y ⋏-⋏1 = ℕℝ 0⌝
	THEN1 all_fc_tac[
		pc_rule1 "ℝ_lin_arith" prove_rule[]
		⌜∀x⦁ℕℝ 0 < x ⇒ ¬x = ℕℝ 0⌝]
	THEN1 REPEAT strip_tac);
a(asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
a(REPEAT strip_tac
	THEN LEMMA_T⌜x ⋏-⋏1 ⋏-⋏1 < f y ⋏-⋏1 ⋏-⋏1⌝ ante_tac
	THEN1 bc_thm_tac ℝ_less_recip_less_thm
	THEN1 REPEAT strip_tac);
a(ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏div_infinity_lim_infinity_thm⦎ = save_thm ( "div_infinity_lim_infinity_thm", (
set_goal([], ⌜∀f⦁
	f -+#>+#
⇔	(λx⦁f x ⋏-⋏1) -+#> ℕℝ 0
∧	∃b⦁∀x⦁ b < x ⇒ ℕℝ 0 < f x⌝);
a(∀_tac THEN rewrite_tac[div_infinity_lim_right_thm]);
a(pure_rewrite_tac[prove_rule[]
	⌜∀x⦁(λ x⦁ f (x ⋏-⋏1) ⋏-⋏1) = (λx⦁(λ z⦁ f z ⋏-⋏1)(x ⋏-⋏1))⌝]);
a(pure_rewrite_tac[lim_right_lim_infinity_thm]
	THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏comp_div_infinity_thm⦎ = save_thm ( "comp_div_infinity_thm", (
set_goal([], ⌜∀f g⦁
	f -+#>+# ∧ g -+#>+#
⇒	(λx⦁f (g x)) -+#>+#⌝);
a(rewrite_tac[div_infinity_def] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o ∀_elim⌜x⌝));
a(DROP_NTH_ASM_T 2 (strip_asm_tac o ∀_elim⌜b⌝));
a(∃_tac⌜b'⌝ THEN REPEAT strip_tac);
a(REPEAT (all_asm_fc_tac[]));
pop_thm()
));

=TEX
%%%%
%%%%  L'HOSPITAL'S RULE
%%%%
=SML

val ⦏rolle_thm1⦎ = save_thm ( "rolle_thm1", (
set_goal([], ⌜∀f df a b⦁
	a < b
∧	(∀x⦁a ≤ x ∧ x < b ⇒ f Cts x)
∧	(∀x⦁a < x ∧ x < b ⇒ (f Deriv df x) x)
∧	(∀x⦁a < x ∧ x < b ⇒ ¬df x = ℕℝ 0)
⇒	(∀x⦁a < x ∧ x < b ⇒ ¬f x = f a)
⌝);
a(contr_tac);
a(ante_tac(list_∀_elim[⌜f⌝, ⌜df⌝, ⌜a⌝, ⌜x⌝]rolle_thm));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 8 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 7 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(contr_tac);
a(lemma_tac⌜¬df x' = ℕℝ 0⌝
	THEN1 (DROP_NTH_ASM_T 7 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜(f Deriv df x') x'⌝
	THEN1 (DROP_NTH_ASM_T 9 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[deriv_unique_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏l'hopital_lim_right_thm⦎ = save_thm ( "l'hopital_lim_right_thm", (
set_goal([], ⌜∀f df g dg a b c⦁
	a < b
∧	f a = ℕℝ 0
∧	g a = ℕℝ 0
∧	(∀x⦁a ≤ x ∧ x < b ⇒ f Cts x)
∧	(∀x⦁a < x ∧ x < b ⇒ (f Deriv df x) x)
∧	(∀x⦁a ≤ x ∧ x < b ⇒ g Cts x)
∧	(∀x⦁a < x ∧ x < b ⇒ (g Deriv dg x) x)
∧	(∀x⦁a < x ∧ x < b ⇒ ¬dg x = ℕℝ 0)
∧	((λx⦁ df x * dg x ⋏-⋏1) +#-> c) a
⇒	((λx⦁ f x * g x ⋏-⋏1) +#-> c) a
⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(LEMMA_T⌜∀x⦁a < x ∧ x < b ⇒ ¬g x = g a⌝ ante_tac
	THEN1 (bc_thm_tac rolle_thm1 THEN asm_rewrite_tac[]
THEN ∃_tac⌜dg⌝ THEN asm_rewrite_tac[]));
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[lim_right_def]
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(rename_tac[(⌜b'⌝, "y")]
	THEN lemma_tac⌜∃t⦁a < t ∧ t < b ∧ t < y⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜if y < b then a + (1/2)*(y + ~a) else a + (1/2)*(b + ~a)⌝
	THEN cases_tac⌜y < b⌝
	THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜t⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜
	(∀x'⦁a ≤ x' ∧ x' ≤ x ⇒ f Cts x')
∧	(∀x'⦁a < x' ∧ x' < x ⇒ (f Deriv df x') x')
∧	(∀x'⦁a ≤ x' ∧ x' ≤ x ⇒ g Cts x')
∧	(∀x'⦁a < x' ∧ x' < x ⇒ (g Deriv dg x') x')⌝);
(* *** Goal "2.1" *** *)
a(lemma_tac⌜∀x'⦁x' ≤ x ∨ x' < x ⇒ x' < b⌝
	THEN1 PC_T1 "ℝ_lin_arith"asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [1, 12, 13, 14, 15]
	(fn ths => REPEAT strip_tac
		THEN all_asm_fc_tac ths
		THEN all_asm_fc_tac ths));
(* *** Goal "2.2" *** *)
a(ante_tac(list_∀_elim[⌜f⌝, ⌜df⌝, ⌜g⌝, ⌜dg⌝, ⌜a⌝, ⌜x⌝]cauchy_mean_value_thm)
	THEN LIST_DROP_NTH_ASM_T [1, 2, 3, 4] asm_rewrite_tac);
a(REPEAT strip_tac);
a(lemma_tac⌜x' < y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 10 (strip_asm_tac o rewrite_rule[] o ∀_elim⌜x'⌝));
a(LEMMA_T ⌜f x * g x ⋏-⋏1 = df x' * dg x' ⋏-⋏1⌝ asm_rewrite_thm_tac);
a(lemma_tac⌜¬dg x' = ℕℝ 0⌝
	THEN1 (DROP_NTH_ASM_T 14 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜¬g x = ℕℝ 0⌝
	THEN1 (DROP_NTH_ASM_T 14 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(LEMMA_T ⌜
	dg x' ⋏-⋏1 * (dg x' * f x) * g x ⋏-⋏1
 =	dg x' ⋏-⋏1 * (df x' * g x) * g x ⋏-⋏1⌝ ante_tac
	THEN1 asm_rewrite_tac[]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b c⦁a * (b * f x) * c= (a * b) * f x * c
	∧ a * (b * g x) * c = (g x * c) * b * a⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f x⦁
	(λx⦁f(~x)) Cts x ⇔ f Cts (~x)
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜f = (λx⦁(λy⦁ f (~y))(~x))⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac comp_cts_thm THEN asm_rewrite_tac[minus_cts_thm]);
(* *** Goal "2" *** *)
a(bc_thm_tac comp_cts_thm THEN asm_rewrite_tac[minus_cts_thm]);
val ⦏cts_comp_minus_thm⦎ = 
save_pop_thm"cts_comp_minus_thm";
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f df x⦁
	((λx⦁f(~x)) Deriv ~(df(~x))) x ⇔
	(f Deriv df (~x)) (~x)
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜f = (λx⦁(λy⦁ f (~y))(~x))⌝ once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(LEMMA_T⌜df (~x) = (~(df (~x))) * ~(ℕℝ 1)⌝ pure_once_rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac comp_deriv_thm THEN asm_rewrite_tac[minus_deriv_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜~(df(~x)) = df(~x) * ~(ℕℝ 1)⌝ pure_once_rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac comp_deriv_thm THEN asm_rewrite_tac[minus_deriv_thm]);
val ⦏deriv_comp_minus_thm⦎ = 
save_pop_thm"deriv_comp_minus_thm";
=TEX
%%%%
%%%%
=SML

val ⦏l'hopital_lim_fun_thm⦎ = save_thm ( "l'hopital_lim_fun_thm", (
set_goal([], ⌜∀f df g dg a b c x⦁
	a < x ∧ x < b
∧	f x = ℕℝ 0
∧	g x = ℕℝ 0
∧	(∀y⦁a < y ∧ y < b ⇒ f Cts y)
∧	(∀y⦁a < y ∧ y < b ∧ ¬y = x ⇒ (f Deriv df y) y)
∧	(∀y⦁a < y ∧ y < b ⇒ g Cts y)
∧	(∀y⦁a < y ∧ y < b ∧ ¬y = x ⇒ (g Deriv dg y) y)
∧	(∀y⦁a < y ∧ y < b ⇒ ¬dg y = ℕℝ 0)
∧	((λy⦁ df y * dg y ⋏-⋏1) --> c) x
⇒	((λy⦁ f y * g y ⋏-⋏1) --> c) x
⌝);
a(rewrite_tac[lim_fun_lim_right_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac l'hopital_lim_right_thm);
a(∃_tac⌜dg⌝ THEN ∃_tac⌜df⌝ THEN ∃_tac⌜b⌝
	THEN REPEAT strip_tac
	THEN GET_ASMS_T (fn ths => FIRST (mapfilter bc_thm_tac ths))
	THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(pure_once_rewrite_tac[prove_rule[] ⌜∀h:ℝ → ℝ⦁h(~y) = (λx⦁h(~x))y⌝]);
a(bc_thm_tac l'hopital_lim_right_thm);
a(∃_tac⌜λx⦁~(dg(~ x))⌝ THEN ∃_tac⌜λx⦁~(df(~ x))⌝ THEN ∃_tac⌜~a⌝);
a(asm_rewrite_tac[cts_comp_minus_thm, deriv_comp_minus_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜(~x < ~a ⇔ a < x)
	∧ (∀s⦁~s = ℕℝ 0 ⇔ s = ℕℝ 0)⌝]);
a(REPEAT strip_tac
	THEN_TRY (GET_ASMS_T (fn ths => FIRST (mapfilter bc_thm_tac ths))
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(POP_ASM_T ante_tac THEN rewrite_tac[lim_right_def]
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(lemma_tac⌜∃t⦁~x < t ∧ t ≤ b' ∧ t ≤ ~a⌝
	THEN1 (∃_tac⌜if b' < ~a then b' else ~a⌝
		THEN cases_tac⌜b'< ~a⌝
		THEN asm_rewrite_tac[]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜t⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜x' < b'⌝ THEN1 all_fc_tac[ℝ_less_≤_trans_thm]);
a(LIST_DROP_NTH_ASM_T [7] all_fc_tac);
a(POP_ASM_T ante_tac);
a(LEMMA_T ⌜
	df (~ x') * dg (~ x') ⋏-⋏1 =
	~ (df (~ x')) * ~ (dg (~ x')) ⋏-⋏1⌝
	rewrite_thm_tac);
a(LEMMA_T ⌜
	~ (dg (~ x')) = ~(ℕℝ 1) * dg(~ x')⌝
	rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(LEMMA_T ⌜
	(∀x y z:ℝ⦁~x * ~y * z = x * y * z)
	∧ (~(ℕℝ 1) * dg(~ x'))⋏-⋏1 =
		~(ℕℝ 1)⋏-⋏1 * dg(~ x')⋏-⋏1⌝
	rewrite_thm_tac);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac (nth 2 (strip_∧_rule (ℝ_recip_clauses))));
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 10 bc_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀fb fa dfx gb ga dgx⦁
	¬gb = ℕℝ 0 ∧ ¬dgx = ℕℝ 0
∧	dgx * (fb + ~fa) = dfx * (gb + ~ga)
⇒	fb * gb ⋏-⋏1 =
	dfx * dgx ⋏-⋏1 +
	(fa + ~(dfx * dgx ⋏-⋏1) * ga) * gb ⋏-⋏1⌝);
a(REPEAT strip_tac);
a(conv_tac eq_sym_conv);
a(LEMMA_T⌜
	dgx ⋏-⋏1 * (dfx * (gb + ~ga)) * gb ⋏-⋏1 =
	dgx ⋏-⋏1 * (dgx * (fb + ~fa)) * gb ⋏-⋏1⌝
	ante_tac
	THEN1 asm_rewrite_tac[]);
a(once_rewrite_tac[ℝ_eq_thm]);
a(conv_tac(ONCE_MAP_C (ℝ_anf_conv)));
a( (* 2.7.8 or later: *)
  rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a x y⦁ ~a * (a ⋏-⋏1) * x  * y  = ~(a * a ⋏-⋏1) * x * y
	∧ a * (a ⋏-⋏1) * x  * y  = (a * a ⋏-⋏1) * x * y⌝]
	ORELSE (* 2.7.7 or earlier: *)
  rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a x y⦁ ~a * x  * y * (a ⋏-⋏1)  = ~(a * a ⋏-⋏1) * x * y
	∧ a * x  * y * (a ⋏-⋏1)  = (a * a ⋏-⋏1) * x * y⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(conv_tac(ONCE_MAP_C (ℝ_anf_conv)));
a(taut_tac);
val ⦏l'hopital_lemma1⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀fa dfx_by_dgx ga c e⦁
	ℕℝ 0 < e
∧	Abs (dfx_by_dgx + ~c) < (1/2) * e 
⇒	Abs(fa + ~dfx_by_dgx * ga) < Abs fa + (Abs c + e) * Abs ga + ℕℝ 1⌝);
a(REPEAT strip_tac);
a(bc_thm_tac ℝ_≤_less_trans_thm
	THEN ∃_tac⌜Abs fa + (Abs c + e) * Abs ga⌝
	THEN_TRY rewrite_tac[]);
a(bc_thm_tac ℝ_≤_trans_thm
	THEN ∃_tac⌜Abs fa + Abs(~dfx_by_dgx * ga)⌝
	THEN rewrite_tac[ℝ_abs_plus_thm]);
a(rewrite_tac[ℝ_abs_times_thm, ℝ_abs_minus_thm]);
a(once_rewrite_tac[ℝ_times_comm_thm]
	THEN bc_thm_tac ℝ_≤_times_mono_thm);
a(rewrite_tac[ℝ_0_≤_abs_thm]);
a(POP_ASM_T ante_tac
	THEN cases_tac⌜ℕℝ 0 ≤ dfx_by_dgx⌝
	THEN cases_tac⌜ℕℝ 0 ≤ c⌝
	THEN cases_tac⌜ℕℝ 0 ≤ dfx_by_dgx + ~c⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏l'hopital_lemma2⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
fun ⦏stronger_estimate_tac⦎ (v_b : TERM, v_a : TERM) : TACTIC = (
let	fun do_asm asm = (
		let	val t = concl asm;
			val (v_a', v_x') = dest_ℝ_less(fst(dest_⇒(snd(dest_∀ t))));
		in	if	v_a' =$ v_a
			then	lemma_tac(subst[(v_b, v_a)] t)
				THEN1 (∀_tac THEN ⇒_tac
					THEN bc_thm_tac asm
					THEN bc_thm_tac ℝ_less_trans_thm
					THEN ∃_tac v_b
					THEN REPEAT strip_tac)
				THEN DROP_ASM_T t discard_tac
		else	fail_tac
		end	handle Fail _ => fail_tac
	);
in	GET_ASMS_T (MAP_EVERY (TRY o do_asm))
	THEN_TRY DROP_ASM_T (mk_ℝ_less(v_a, v_b)) discard_tac
	THEN rename_tac [(v_b, fst(dest_var v_a))]
end);
=TEX
%%%%
%%%%
=SML
fun ⦏moreover_tac⦎ (tm : TERM) : TACTIC = (
let	val (v_a, v_b) = dest_ℝ_less(fst(dest_∧(snd(dest_∃ tm))));
in	lemma_tac tm THEN_LIST
	[id_tac, stronger_estimate_tac (v_b, v_a)]
end);
=TEX
%%%%
%%%%
=SML

val ⦏l'hopital_lim_infinity_thm⦎ = save_thm ( "l'hopital_lim_infinity_thm", (
set_goal([], ⌜∀f df g dg a c⦁
	g -+#>+#
∧	(∀x⦁a < x ⇒ (f Deriv df x) x)
∧	(∀x⦁a < x ⇒ (g Deriv dg x) x)
∧	(∀x⦁a < x ⇒ ¬dg x = ℕℝ 0)
∧	(λx⦁ df x * dg x ⋏-⋏1) -+#> c
⇒	(λx⦁ f x * g x ⋏-⋏1) -+#> c
⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(rewrite_tac[lim_infinity_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < (1/2)*e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜(1/2)*e⌝));
a(strip_asm_tac(list_∀_elim[⌜a⌝, ⌜b⌝]ℝ_max_2_thm));
a(stronger_estimate_tac(⌜z⌝, ⌜b⌝));
a(stronger_estimate_tac(⌜b⌝, ⌜a⌝));
a(moreover_tac⌜∃b⦁a < b ∧ ∀ x⦁ b < x ⇒ ℕℝ 0 < g x⌝);
(* *** Goal "1" *** *)
a(all_fc_tac[div_infinity_pos_thm]);
a(strip_asm_tac(list_∀_elim[⌜a⌝, ⌜b⌝] ℝ_max_2_thm));
a(∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(all_fc_tac[ℝ_less_trans_thm] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜
	(∀x⦁a < x ⇒ f Cts x)
∧	(∀x⦁a < x ⇒ g Cts x)⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]
		THEN all_fc_tac[deriv_cts_thm]));
a(lemma_tac⌜∃s u⦁ a < s ∧ ∀t⦁s < t ⇒
	∃x v⦁a < x ∧ Abs v < u ∧
	f t * g t ⋏-⋏1 = df x * dg x ⋏-⋏1 + v * g t ⋏-⋏1⌝);
(* *** Goal "2.1" *** *)
a(lemma_tac⌜∃s⦁ a < s⌝ THEN1
	(∃_tac⌜a + 1/2⌝ THEN REPEAT strip_tac));
a(∃_tac⌜s⌝ THEN ∃_tac⌜Abs (f s) + (Abs c + e) * Abs (g s) + ℕℝ 1⌝ THEN REPEAT strip_tac);
a(LEMMA_T⌜∃ x⦁ s < x ∧ x < t
	∧ dg x * (f t - f s) = df x * (g t - g s)⌝
	(strip_asm_tac o rewrite_rule[])
	THEN1 (bc_thm_tac cauchy_mean_value_thm
		THEN REPEAT strip_tac
		THEN GET_ASMS_T (fn ths => FIRST (mapfilter bc_thm_tac ths))
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜x⌝ THEN ∃_tac⌜f s + ~(df x) * dg x ⋏-⋏1 * g s⌝);
a(lemma_tac⌜¬dg x = ℕℝ 0⌝
	THEN1(GET_NTH_ASM_T 9 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜ℕℝ 0 < g t⌝
	THEN1(GET_NTH_ASM_T 13 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜¬g t = ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[l'hopital_lemma1]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y z:ℝ⦁~x * y * z = ~(x * y) * z⌝]);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac l'hopital_lemma2 THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 11 bc_thm_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜ℕℝ 0 < u⌝
	THEN1 (POP_ASM_T (strip_asm_tac o ∀_elim⌜s + ℕℝ 1⌝)
		THEN strip_asm_tac (∀_elim⌜v:ℝ⌝ ℝ_0_≤_abs_thm)
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(strip_asm_tac(list_∀_elim[⌜g⌝, ⌜u⌝, ⌜(1/2)*e⌝] div_infinity_times_recip_thm));
a(strip_asm_tac(list_∀_elim[⌜s⌝, ⌜b⌝] ℝ_max_2_thm));
a(∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜s < x ∧ b < x⌝
	THEN1 (all_fc_tac[ℝ_less_trans_thm]
		THEN REPEAT strip_tac));
a(DROP_NTH_ASM_T 8 (strip_asm_tac o ∀_elim⌜x⌝));
a(POP_ASM_T rewrite_thm_tac);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b⦁(a + b) + ~c = (a + ~c) + b⌝]);
a(bc_thm_tac ℝ_≤_less_trans_thm 
	THEN ∃_tac
	⌜Abs(df x' * dg x' ⋏-⋏1 + ~ c) + Abs(v * g x ⋏-⋏1)⌝
	THEN rewrite_tac[ℝ_abs_plus_thm]);
a(DROP_NTH_ASM_T 13 (strip_asm_tac o ∀_elim⌜x'⌝));
a(POP_ASM_T ante_tac THEN
	LEMMA_T⌜Abs (v * g x ⋏-⋏1) < (1/2)*e⌝ ante_tac
	THEN_LIST [id_tac, PC_T1 "ℝ_lin_arith" prove_tac[]]);
a(rewrite_tac[ℝ_abs_times_thm]);
a(lemma_tac⌜ℕℝ 0 < g x⌝
	THEN1 (DROP_NTH_ASM_T 16 bc_thm_tac THEN all_fc_tac[ℝ_less_trans_thm]));
a(lemma_tac⌜ℕℝ 0 < g x ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(LEMMA_T ⌜Abs (g x ⋏-⋏1) = g x ⋏-⋏1⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
a(DROP_NTH_ASM_T 10 (strip_asm_tac o ∀_elim⌜x⌝));
a(bc_thm_tac ℝ_less_trans_thm
	THEN ∃_tac⌜u * g x ⋏-⋏1⌝
	THEN REPEAT strip_tac);
a(once_rewrite_tac[ℝ_times_comm_thm]
	THEN bc_thm_tac ℝ_times_mono_thm
	THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%% APPLICATIONS OF L'HOPITAL'S RULE
%%%%
=SML

val ⦏cts_deriv_deriv_thm⦎ = save_thm ("cts_deriv_deriv_thm", (
set_goal([], ⌜∀f df a b t⦁
	(∀x⦁x ∈ OpenInterval a b \ {t} ⇒ (f Deriv df x) x)
∧	(∀x⦁x ∈ OpenInterval a b ⇒ df Cts x)
∧	(f Cts t)
∧	t ∈ OpenInterval a b
⇒	(∀x⦁x ∈ OpenInterval a b ⇒ (f Deriv df x) x)
⌝);
a(rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 7 (strip_asm_tac o ∀_elim⌜x⌝));
a(all_var_elim_asm_tac THEN rewrite_tac[deriv_lim_fun_thm1]);
a(ho_bc_thm_tac l'hopital_lim_fun_thm);
a(MAP_EVERY ∃_tac [⌜λx:ℝ⦁ ℕℝ 1⌝, ⌜df⌝, ⌜b⌝, ⌜a⌝]
	THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(cases_tac⌜y = t⌝ THEN1 all_var_elim_asm_tac1);
a(bc_thm_tac deriv_cts_thm);
a(∃_tac⌜df y⌝ THEN DROP_NTH_ASM_T 8 bc_thm_tac);
a(REPEAT strip_tac);
(* *** Goal "2" *** *)
a(RAT_DERIV_T ante_tac THEN rewrite_tac[]);
a(STRIP_T (ante_tac o ∀_elim ⌜df y⌝));
a(LEMMA_T ⌜(f Deriv df y) y⌝ rewrite_thm_tac);
a(DROP_NTH_ASM_T 8 bc_thm_tac);
a(REPEAT strip_tac);
(* *** Goal "3" *** *)
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
(* *** Goal "4" *** *)
a(RAT_DERIV_T ante_tac THEN rewrite_tac[]);
(* *** Goal "5" *** *)
a(rewrite_tac[η_axiom]);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(all_fc_tac[cts_lim_fun_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_id_over_sin_thm⦎ = save_thm ( "lim_fun_id_over_sin_thm", (
set_goal([], ⌜((λx⦁x * Sin x ⋏-⋏1) --> ℕℝ 1) (ℕℝ 0)⌝);
a(ho_bc_thm_tac l'hopital_lim_fun_thm);
a(MAP_EVERY ∃_tac [⌜Cos⌝, ⌜λx:ℝ⦁ ℕℝ 1⌝, ⌜(1/2) * π⌝, ⌜~(1/2) * π⌝]);
a(conv_tac simple_β_η_norm_conv THEN
	rewrite_tac[sin_def, id_cts_thm, id_deriv_thm, sin_cos_cts_thm]);
a(REPEAT strip_tac
	THEN1 (ante_tac π_def THEN PC_T1 "ℝ_lin_arith" prove_tac[])
	THEN1 (ante_tac π_def THEN PC_T1 "ℝ_lin_arith" prove_tac[])
	THEN1 all_fc_tac[cos_¬_eq_0_thm]);
a(lemma_tac⌜(λx⦁ Cos x ⋏-⋏1) Cts (ℕℝ 0)⌝);
(* *** Goal "1" *** *)
a (simple_cts_tac THEN rewrite_tac[cos_def, η_axiom, sin_cos_cts_thm]);
(* *** Goal "2" *** *)
a(all_fc_tac[cts_lim_fun_thm] THEN POP_ASM_T ante_tac);
a(rewrite_tac[cos_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_infinity_recip_exp_thm⦎ = save_thm ( "lim_infinity_recip_exp_thm", (
set_goal([], ⌜(λx⦁Exp x ⋏-⋏1) -+#> ℕℝ 0⌝);
a(rewrite_tac[
	rewrite_rule[div_infinity_lim_infinity_thm] exp_div_infinity_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_infinity_id_over_exp_thm⦎ = save_thm ( "lim_infinity_id_over_exp_thm", (
set_goal([], ⌜(λx⦁x * Exp x ⋏-⋏1) -+#> ℕℝ 0⌝);
a(ho_bc_thm_tac l'hopital_lim_infinity_thm);
a(MAP_EVERY ∃_tac [⌜Exp⌝, ⌜λx:ℝ⦁ ℕℝ 1⌝, ⌜ℕℝ 0⌝]);
a(conv_tac simple_β_η_norm_conv THEN rewrite_tac[
	exp_def, id_deriv_thm,
	exp_div_infinity_thm, exp_¬_eq_0_thm,
	lim_infinity_recip_exp_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_power_over_exp_thm⦎ = save_thm ( "lim_fun_power_over_exp_thm", (
set_goal([], ⌜∀m:ℕ⦁(λx⦁x ^ m * Exp x ⋏-⋏1) -+#> ℕℝ 0⌝);
a(∀_tac THEN strip_asm_tac(∀_elim⌜m:ℕ⌝ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN1 rewrite_tac[lim_infinity_recip_exp_thm]);
a(induction_tac⌜i:ℕ⌝
	THEN1 rewrite_tac[lim_infinity_id_over_exp_thm]);
a(ho_bc_thm_tac l'hopital_lim_infinity_thm THEN conv_tac simple_β_η_norm_conv);
a(MAP_EVERY ∃_tac [⌜Exp⌝, ⌜λx:ℝ⦁ (ℕℝ (i + 1) + ℕℝ 1) * x^(i + 1)⌝, ⌜ℕℝ 0⌝]);
a(rewrite_tac[exp_def, exp_div_infinity_thm, exp_¬_eq_0_thm]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(RAT_DERIV_T strip_asm_tac);
(* *** Goal "2" *** *)
a(ante_tac (list_∀_elim
	[⌜λx:ℝ⦁ ℕℝ (i + 1) + ℕℝ 1⌝, ⌜ℕℝ (i + 1) + ℕℝ 1⌝,
	⌜λ x⦁ x ^ (i + 1) * Exp x ⋏-⋏1⌝, ⌜ℕℝ 0⌝]
	times_lim_infinity_thm));
a(asm_rewrite_tac[const_lim_infinity_thm,
	ℝ_times_assoc_thm] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_infinity_log_over_id_thm⦎ = save_thm ( "lim_infinity_log_over_id_thm", (
set_goal([], ⌜(λx⦁Log x * x ⋏-⋏1) -+#> ℕℝ 0⌝);
a(ho_bc_thm_tac l'hopital_lim_infinity_thm THEN conv_tac simple_β_η_norm_conv);
a(MAP_EVERY ∃_tac [⌜λx:ℝ⦁ℕℝ 1⌝, ⌜$ ⋏-⋏1⌝, ⌜ℕℝ 1⌝]);
a(rewrite_tac[id_deriv_thm, id_div_infinity_thm,
	recip_lim_infinity_0_thm, log_div_infinity_thm]);
a(REPEAT strip_tac);
a(bc_thm_tac log_deriv_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_log_over_id_minus_1_thm⦎ = save_thm ( "lim_fun_log_over_id_minus_1_thm", (
set_goal([], ⌜((λx⦁Log x * (x - ℕℝ 1) ⋏-⋏1) --> ℕℝ 1) (ℕℝ 1)⌝);
a(ho_bc_thm_tac l'hopital_lim_fun_thm THEN conv_tac simple_β_η_norm_conv);
a(MAP_EVERY ∃_tac [⌜λx:ℝ⦁ℕℝ 1⌝, ⌜$ ⋏-⋏1⌝, ⌜ℕℝ 2⌝, ⌜1/2⌝]);
a(rewrite_tac[log_clauses]);
a(REPEAT strip_tac
	THEN1 (bc_thm_tac log_cts_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[])
	THEN1 (bc_thm_tac log_deriv_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[])
	THEN1 REPEAT (simple_cts_tac THEN REPEAT strip_tac)
	THEN1 RAT_DERIV_T (strip_asm_tac o rewrite_rule[]));
a(ante_tac(list_∀_elim[⌜(λ y⦁ y ⋏-⋏1)⌝, ⌜ℕℝ 1⌝] cts_lim_fun_thm));
a(rewrite_tac[] THEN REPEAT strip_tac);
a(swap_nth_asm_concl_tac 1);
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_log_1_plus_over_id_thm⦎ = save_thm ( "lim_fun_log_1_plus_over_id_thm", (
set_goal([], ⌜((λx⦁Log (ℕℝ 1 + x) * x ⋏-⋏1) --> ℕℝ 1) (ℕℝ 0)⌝);
a(once_rewrite_tac[ℝ_plus_comm_thm]);
a(LEMMA_T
	⌜((λx⦁(λy⦁Log y * (y - ℕℝ 1) ⋏-⋏1)((λz⦁z + ℕℝ 1) x))
	--> (ℕℝ 1))(ℕℝ 0)⌝
	(accept_tac o rewrite_rule[ℝ_plus_assoc_thm]));
a(bc_thm_tac comp_lim_fun_thm1);
a(rewrite_tac[rewrite_rule[]lim_fun_log_over_id_minus_1_thm]);
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
pop_thm()
));

=TEX
=TEX
%%%%
%%%%
=SML

val ⦏lim_fun_e_thm⦎ = save_thm ( "lim_fun_e_thm", (
set_goal([], ⌜((λx⦁Exp(x ⋏-⋏1 * Log (ℕℝ 1 + x))) --> Exp(ℕℝ 1))(ℕℝ 0)⌝);
a((ho_bc_thm_tac o all_∀_intro o
	inst_term_rule[(⌜Exp⌝, ⌜g:ℝ → ℝ⌝)]o all_∀_elim) comp_lim_fun_thm);
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(rewrite_tac[lim_fun_log_1_plus_over_id_thm, exp_cts_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏lim_seq_e_thm⦎ = save_thm ( "lim_seq_e_thm", (
set_goal([], ⌜(λm⦁(ℕℝ 1 + ℕℝ m ⋏-⋏1)^m) -> Exp(ℕℝ 1)⌝);
a(once_rewrite_tac[∀_elim⌜1⌝ lim_seq_shift_thm]
	THEN rewrite_tac[]);
a(ante_tac(rewrite_rule[
	rewrite_rule[] (∀_elim⌜ℕℝ 0⌝ lim_seq_recip_ℕ_thm),
	ℕℝ_recip_thm,
	exp_ℝ_ℕ_exp_thm,
	ℕℝ_recip_not_eq_0_thm]
	(∀_elim⌜λm⦁ℕℝ (m + 1) ⋏-⋏1⌝
		(rewrite_rule[lim_fun_lim_seq_thm] lim_fun_e_thm))));
a(LEMMA_T⌜∀m⦁ Exp (Log (ℕℝ 1 + ℕℝ (m + 1) ⋏-⋏1)) = ℕℝ 1 + ℕℝ (m + 1) ⋏-⋏1⌝ rewrite_thm_tac);
a(REPEAT strip_tac THEN bc_thm_tac exp_log_thm);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x⦁ℕℝ 0 < x ⇒ ℕℝ 0 < ℕℝ 1 + x⌝));
a(rewrite_tac[ℕℝ_0_less_recip_thm]);
pop_thm()
));

=TEX
\subsection{Further Functions}
%%%%
%%%% INVERSE FUNCTIONS
%%%%
=SML

val ⦏ℝ_less_mono_⇔_thm⦎ = save_thm ( "ℝ_less_mono_⇔_thm", (
set_goal([],⌜∀f:ℝ → ℝ⦁
	(∀x y⦁ x < y ⇒ f x < f y)
⇔	(∀x y⦁ f x < f y ⇔ x < y)⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜y⌝] ℝ_less_cases_thm)
	THEN1 all_var_elim_asm_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
=SML

val ⦏ℝ_less_mono_⇔_≤_thm⦎ = save_thm ( "ℝ_less_mono_⇔_≤_thm", (
set_goal([],⌜∀f:ℝ → ℝ⦁
	(∀x y⦁ x < y ⇒ f x < f y)
⇔	(∀x y⦁ f x ≤ f y ⇔ x ≤ y)⌝);
a(rewrite_tac[ℝ_less_mono_⇔_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y : ℝ ⦁x ≤ y ⇔ ¬y < x⌝,
	prove_rule[]
	⌜∀p q⦁(¬p ⇔ ¬q) ⇔ (p ⇔ q)⌝]);
a(prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
%%%%
=SML

val ⦏ℝ_less_mono_one_one_thm⦎ = save_thm ( "ℝ_less_mono_one_one_thm", (
set_goal([],⌜∀f:ℝ → ℝ⦁
	(∀x y⦁ x < y ⇒ f x < f y)
⇒	(∀x y⦁ f x = f y ⇔ x = y)⌝);
a(rewrite_tac[ℝ_less_mono_⇔_thm]);
a(REPEAT strip_tac THEN_LIST [id_tac, asm_rewrite_tac[]]);
a(LEMMA_T⌜x = y ⇔ ¬x < y ∧ ¬y < x⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(DROP_NTH_ASM_T 2 (once_rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏total_inverse_cts_thm⦎ = save_thm ( "total_inverse_cts_thm", (
set_goal([],⌜∀f g x⦁
	(∀x y⦁ x < y ⇒ f x < f y)
∧	(∀x⦁g(f x) = x)
∧	(∀y⦁f(g y) = y)
⇒	g Cts (f x)⌝);
a(rewrite_tac[ℝ_less_mono_⇔_thm]
	THEN REPEAT strip_tac);
a(bc_thm_tac darboux_cts_mono_thm);
a(PC_T1 "sets_ext" rewrite_tac[open_interval_def, closed_interval_def] THEN REPEAT strip_tac);
a(∃_tac⌜f x + ℕℝ 1⌝ THEN ∃_tac⌜f x + ~(ℕℝ 1)⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 8 (once_rewrite_thm_tac o conv_rule(ONCE_MAP_C eq_sym_conv)));
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜f y⌝ THEN asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 5 (fn th =>
	LIST_GET_NTH_ASM_T [1, 2]
		(MAP_EVERY (ante_tac o once_rewrite_rule[conv_rule(ONCE_MAP_C eq_sym_conv)th]))));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏total_inverse_thm⦎ = save_thm ( "total_inverse_thm", (
set_goal([],⌜∀f⦁
	(∀x y⦁ x < y ⇒ f x < f y)
∧	(∀y⦁∃x⦁ f x = y)
⇒	∃g⦁	(∀x⦁g(f x) = x)
	∧	(∀y⦁f(g y) = y)
	∧	(∀y⦁g Cts y)
	∧	(∀x y⦁ x < y ⇒ g x < g y)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃g⦁(∀x⦁f(g x) = x)⌝ THEN1 prove_∃_tac);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
a(lemma_tac⌜∀ x⦁ g (f x) = x⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(fc_tac[ℝ_less_mono_one_one_thm]);
a(POP_ASM_T bc_thm_tac);
a(POP_ASM_T rewrite_thm_tac);
(* *** Goal "2" *** *)
a(POP_ASM_T rewrite_thm_tac);
(* *** Goal "3" *** *)
a(all_fc_tac[total_inverse_cts_thm]);
a(spec_nth_asm_tac 4 ⌜y⌝ THEN all_var_elim_asm_tac1);
a(asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a(DROP_NTH_ASM_T 5 (bc_thm_tac o	 rewrite_rule[ℝ_less_mono_⇔_thm]));
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏closed_half_infinite_inverse_thm1⦎ = save_thm ( "closed_half_infinite_inverse_thm1", (
set_goal([], ⌜∀f a⦁
	(∀x⦁ a ≤ x ⇒ f Cts x)
∧	(∀x y⦁ a ≤ x ∧ x < y ⇒ f x < f y)
∧	(∀y⦁ f a ≤ y ⇒ ∃x⦁a ≤ x ∧ f x = y)
⇒	∃g⦁	(∀x⦁ a ≤ x ⇒ g(f x) = x)
	∧	(∀y⦁ f a ≤ y ⇒ f(g y) = y)
	∧	(∀y⦁ g Cts y)
	∧	(∀x y⦁ x < y ⇒ g x < g y)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃h⦁
	(∀x y⦁ x < y ⇒ h x < h y)
∧	(∀y⦁ ∃ x⦁ h x = y)
∧	(∀x⦁ a ≤ x ⇒ f x = h x)⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜λz⦁ if a ≤ z then f z else f a + ~a + z⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(cases_tac⌜a ≤ x⌝ THEN asm_rewrite_tac[]
	THEN1 (lemma_tac⌜a ≤ y⌝
		THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
		THEN ALL_ASM_FC_T asm_rewrite_tac[]));
a(cases_tac⌜¬a ≤ y⌝ THEN asm_rewrite_tac[]);
a(bc_thm_tac ℝ_less_≤_trans_thm
	THEN ∃_tac⌜f a⌝ THEN REPEAT strip_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜a = y⌝ THEN1 asm_rewrite_tac[]);
a(rewrite_tac[ℝ_≤_def] THEN ∨_left_tac);
a(DROP_NTH_ASM_T 6 bc_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(cases_tac⌜¬f a ≤ y⌝);
(* *** Goal "1.2.1" *** *)
a(∃_tac⌜y + ~(f a) + a⌝);
a(LEMMA_T⌜¬a ≤ y + ~(f a) + a⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(all_var_elim_asm_tac1);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(all_fc_tac[total_inverse_thm]);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LIST_DROP_NTH_ASM_T [6] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "2.2" *** *)
a(POP_ASM_T ante_tac);
a(LEMMA_T⌜f a = h a⌝ asm_rewrite_thm_tac
	THEN1 DROP_NTH_ASM_T 5 bc_thm_tac
	THEN REPEAT strip_tac);
a(LEMMA_T⌜f(g y) = h(g y)⌝ asm_rewrite_thm_tac);
a(GET_NTH_ASM_T 6 bc_thm_tac);
a(swap_nth_asm_concl_tac 1);
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_¬_≤_less_thm]
	THEN strip_tac);
a(LIST_GET_NTH_ASM_T [8] all_fc_tac);
a(POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏closed_half_infinite_inverse_thm⦎ = save_thm ( "closed_half_infinite_inverse_thm", (
set_goal([], ⌜∀f df a⦁
	(∀x⦁ a ≤ x ⇒ f Cts x)
∧	(∀x⦁ a < x ⇒ (f Deriv df x) x)
∧	(∀x⦁ a < x ⇒ ℕℝ 0 < df x)
∧	(∀y⦁ f a ≤ y ⇒ ∃x⦁a ≤ x ∧ f x = y)
⇒	∃g⦁	(∀x⦁ a ≤ x ⇒ g(f x) = x)
	∧	(∀y⦁ f a ≤ y ⇒ f(g y) = y)
	∧	(∀y⦁ g Cts y)
	∧	(∀ x y⦁ x < y ⇒ g x < g y)⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀x y⦁ a ≤ x ∧ x < y ⇒ f x < f y⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN bc_thm_tac deriv_0_less_thm);
a(∃_tac⌜df⌝ THEN REPEAT strip_tac
	THEN GET_ASMS_T (fn ths =>
		FIRST (mapfilter bc_thm_tac ths)
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	));
(* *** Goal "2" *** *)
a(all_fc_tac[closed_half_infinite_inverse_thm1]);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cond_cts_thm⦎ = save_thm ( "cond_cts_thm", (
set_goal([], ⌜∀f g y⦁
	f Cts y
∧	g Cts y
∧	f y = g y
⇒	(λz⦁if z ≤ y then f z else g z) Cts y⌝);
a(rewrite_tac[cts_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3, 4] all_fc_tac);
a(lemma_tac⌜∃c⦁ℕℝ 0 < c ∧ c ≤ d ∧ c ≤ d'⌝
	THEN1 (∃_tac⌜if d ≤ d' then d else d'⌝
		THEN cases_tac⌜d ≤ d'⌝
		THEN asm_rewrite_tac[]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(∃_tac⌜c⌝ THEN REPEAT strip_tac);
a(cases_tac⌜y' ≤ y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 11 (rewrite_thm_tac o eq_sym_rule));
a(DROP_NTH_ASM_T 6 bc_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 8 bc_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cond_cts_thm1⦎ = save_thm ( "cond_cts_thm1", (
set_goal([], ⌜∀f g a b y x⦁
	(∀x⦁x ∈ ClosedInterval a y ⇒ f Cts x)
∧	(∀x⦁x ∈ ClosedInterval y b ⇒ g Cts x)
∧	f y = g y
∧	x ∈ ClosedInterval a b
⇒	(λz⦁if z ≤ y then f z else g z) Cts x⌝);
a(rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝, ⌜y⌝] ℝ_less_cases_thm));
(* *** Goal "1" *** *)
a(bc_thm_tac cts_local_thm);
a(MAP_EVERY ∃_tac[⌜f⌝, ⌜y⌝, ⌜a + ~(ℕℝ 1)⌝]);
a(lemma_tac⌜x ≤ y⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [6, 7] all_fc_tac);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜y' ≤ y⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac);
a(bc_thm_tac cond_cts_thm);
a(LEMMA_T⌜y ≤ y⌝ asm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5, 6] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "3" *** *)
a(bc_thm_tac cts_local_thm);
a(MAP_EVERY ∃_tac[⌜g⌝, ⌜b + ℕℝ 1⌝, ⌜y⌝]);
a(lemma_tac⌜y ≤ x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [6, 7] all_fc_tac);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜¬y' ≤ y⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏closed_interval_inverse_thm⦎ = save_thm ( "closed_interval_inverse_thm", (
set_goal([], ⌜∀f df a b⦁
	a < b
∧	(∀x⦁ x ∈ ClosedInterval a b ⇒ f Cts x)
∧	(∀x⦁ x ∈ OpenInterval a b ⇒ (f Deriv df x) x)
∧	(∀x⦁ x ∈ OpenInterval a b ⇒ ℕℝ 0 < df x)
⇒	∃g⦁	(∀x⦁ x ∈ ClosedInterval a b ⇒ g(f x) = x)
	∧	(∀y⦁ y ∈ ClosedInterval (f a) (f b) ⇒ f(g y) = y)
	∧	(∀y⦁ g Cts y)
	∧	(∀x y⦁ x < y ⇒ g x < g y)⌝);
a(rewrite_tac[open_interval_def, closed_interval_def]
	THEN REPEAT strip_tac);
a(lemma_tac⌜∀y⦁ f a ≤ y ∧ y ≤ f b
	⇒ ∃x⦁ a ≤ x ∧ x ≤ b ∧ f x = y⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(cases_tac⌜f a = y⌝ THEN1 (∃_tac⌜a⌝ THEN asm_rewrite_tac[ℝ_≤_def]));
a(cases_tac⌜f b = y⌝ THEN1 (∃_tac⌜b⌝ THEN asm_rewrite_tac[ℝ_≤_def]));
a(lemma_tac⌜f a < y ∧ y < f b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ante_tac(list_∀_elim[⌜f⌝, ⌜a⌝, ⌜b⌝]intermediate_value_thm));
a(asm_rewrite_tac[]);
a(STRIP_T (strip_asm_tac o ∀_elim⌜y⌝));
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∀x y⦁ a ≤ x ∧ y ≤ b ∧ x < y ⇒ f x < f y⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac THEN bc_thm_tac deriv_0_less_thm);
a(∃_tac⌜df⌝ THEN REPEAT strip_tac
	THEN GET_ASMS_T (fn ths =>
		FIRST (mapfilter bc_thm_tac ths)
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	));
(* *** Goal "2.2" *** *)
a(lemma_tac⌜∃h⦁
	(∀x⦁ a ≤ x ⇒ h Cts x)
∧	(∀ x y⦁ a ≤ x ∧ x < y ⇒ h x < h y)
∧	(∀ y⦁ h a ≤ y ⇒ (∃ x⦁ a ≤ x ∧ h x = y))
∧	(∀x⦁ a ≤ x ∧ x ≤ b ⇒ f x = h x)⌝);
(* *** Goal "2.2.1" *** *)
a(∃_tac⌜λz⦁
	if z ≤ b
	then f z
	else f b + ~b + z⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "2.2.1.1" *** *)
a(ho_bc_thm_tac cond_cts_thm1 THEN conv_tac simple_β_η_norm_conv);
a(∃_tac⌜x + ℕℝ 1⌝ THEN ∃_tac⌜a⌝);
a(rewrite_tac[closed_interval_def]
	THEN REPEAT strip_tac
	THEN1 all_asm_fc_tac[]);
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
(* *** Goal "2.2.1.2" *** *)
a(cases_tac⌜y ≤ b⌝ THEN asm_rewrite_tac[]
	THEN1 (lemma_tac⌜x ≤ b⌝
		THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
		THEN ALL_ASM_FC_T asm_rewrite_tac[]));
a(cases_tac⌜¬x ≤ b⌝ THEN asm_rewrite_tac[]);
a(bc_thm_tac ℝ_≤_less_trans_thm
	THEN ∃_tac⌜f b⌝ THEN REPEAT strip_tac
	THEN_LIST[id_tac, PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(cases_tac⌜b = x⌝ THEN1 asm_rewrite_tac[]);
a(rewrite_tac[ℝ_≤_def] THEN ∨_left_tac);
a(DROP_NTH_ASM_T 6 bc_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.1.3" *** *)
a(cases_tac⌜f b < y⌝);
(* *** Goal "2.2.1.3.1" *** *)
a(∃_tac⌜y + ~(f b) + b⌝);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜¬y + ~(f b) + b ≤ b⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.1.3.2" *** *)
a(DROP_NTH_ASM_T 2 ante_tac);
a(LEMMA_T⌜a ≤ b⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN REPEAT strip_tac);
a(lemma_tac⌜y ≤ f b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(all_var_elim_asm_tac1);
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.1.4" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(all_fc_tac[closed_half_infinite_inverse_thm1]);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a(LIST_DROP_NTH_ASM_T [7] (ALL_FC_T asm_rewrite_tac));
a(LIST_DROP_NTH_ASM_T [6] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "2.2.2.2" *** *)
a(REPEAT_N 2 (POP_ASM_T ante_tac));
a(LEMMA_T⌜f b = h b ∧ f a = h a⌝ rewrite_thm_tac
	THEN1 (REPEAT strip_tac
		THEN DROP_NTH_ASM_T 5 bc_thm_tac
		THEN REPEAT strip_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(LEMMA_T⌜f(g y) = h(g y)⌝ asm_rewrite_thm_tac);
a(POP_ASM_T discard_tac THEN DROP_NTH_ASM_T 6 bc_thm_tac);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac
	THEN all_var_elim_asm_tac1);
a(DROP_NTH_ASM_T 4 (fn th =>
	let val th1 = conv_rule(ONCE_MAP_C eq_sym_conv) (rewrite_rule[ℝ_less_mono_⇔_≤_thm] th);
	in	LIST_DROP_NTH_ASM_T [2, 3]
		(MAP_EVERY (ante_tac o once_rewrite_rule [th1]))
	end));
a(LEMMA_T⌜g(h a) = a ∧ g(h b) = b⌝ rewrite_thm_tac
	THEN1 (REPEAT strip_tac
		THEN DROP_NTH_ASM_T 3 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜Sqrt⌝;
a(lemma_tac⌜∀x⦁ℕℝ 0 ≤ x ⇒ ∃y⦁ℕℝ 0 ≤ y ∧ y^2 = x⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN cases_tac⌜x = ℕℝ 0⌝
	THEN1 ∃_tac⌜ℕℝ 0⌝
	THEN asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(∃_tac⌜Exp(1/2 * Log x)⌝);
a(rewrite_tac[ℝ_≤_def, exp_clauses]);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) exp_clauses,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x⦁1/2*x + 1/2*x = x⌝]);
a(lemma_tac⌜ℕℝ 0 < x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[exp_log_thm]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∃ g⦁ (∀ x⦁ ℕℝ 0 ≤ x ⇒ g ((λx⦁x^2) x) = x)
	∧ (∀ y⦁ (λx⦁x^2) (ℕℝ 0) ≤ y ⇒ (λx⦁x^2) (g y) = y)
	∧ (∀ y⦁ g Cts y)
	∧ (∀ x y⦁ x < y ⇒ g x < g y)⌝);
(* *** Goal "2.1" *** *)
a(bc_thm_tac closed_half_infinite_inverse_thm);
a(lemma_tac⌜∀x⦁((λx⦁x^2) Deriv ℕℝ 2*x) x⌝
	THEN1 (strip_tac
		THEN RAT_DERIV_T strip_asm_tac));
a(lemma_tac⌜∀x⦁(λx⦁x^2) Cts x⌝
	THEN1 (strip_tac
		THEN bc_thm_tac deriv_cts_thm
		THEN ∃_tac⌜ℕℝ 2 * x⌝ THEN asm_rewrite_tac[]));
a(∃_tac⌜λx⦁ℕℝ 2*x⌝ THEN asm_rewrite_tac[]);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
a(all_asm_ante_tac THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a(LIST_DROP_NTH_ASM_T [6] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "2.2.2" *** *)
a(LIST_DROP_NTH_ASM_T [4] (ALL_FC_T rewrite_tac));
save_consistency_thm ⌜Sqrt⌝ (pop_thm());

val ⦏sqrt_def⦎ = save_thm("sqrt_def", get_spec ⌜Sqrt⌝);
=TEX
%%%%
%%%%
=SML

val ⦏sqrt_thm⦎ = save_thm ( "sqrt_thm", (
set_goal([], ⌜∀x⦁ℕℝ 0 ≤ x ⇒ Sqrt x ^ 2 = x⌝);
a(REPEAT strip_tac THEN all_fc_tac[sqrt_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_0_≤_thm⦎ = save_thm ( "sqrt_0_≤_thm", (
set_goal([], ⌜∀x⦁ℕℝ 0 ≤ x ⇒ ℕℝ 0 ≤ Sqrt x⌝);
a(REPEAT strip_tac THEN all_fc_tac[sqrt_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_cts_thm⦎ = save_thm ( "sqrt_cts_thm", (
set_goal([], ⌜∀x⦁ℕℝ 0 ≤ x ⇒ Sqrt Cts x⌝);
a(REPEAT strip_tac THEN all_fc_tac[sqrt_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_square_thm⦎ = save_thm ( "sqrt_square_thm", (
set_goal([], ⌜∀x⦁Sqrt(x ^ 2) = Abs x⌝);
a(REPEAT strip_tac);
a(strip_asm_tac (∀_elim⌜x⌝ ℝ_0_≤_square_thm));
a(all_fc_tac [sqrt_thm, sqrt_0_≤_thm]);
a(DROP_NTH_ASM_T 2 ante_tac
	THEN rewrite_tac[square_root_unique_thm]);
a(REPEAT strip_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN REPEAT strip_tac
	THEN1 asm_rewrite_tac[]);
a(cases_tac⌜x = ℕℝ 0⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T⌜¬ℕℝ 0 ≤ x⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏square_sqrt_thm⦎ = save_thm ( "square_sqrt_thm", (
set_goal([], ⌜∀x y⦁x = y ^ 2 ⇒ Sqrt x = Abs y⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[sqrt_square_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_0_1_thm⦎ = save_thm ( "sqrt_0_1_thm", (
set_goal([], ⌜Sqrt (ℕℝ 0) = ℕℝ 0 ∧ Sqrt (ℕℝ 1) = ℕℝ 1⌝);
a(lemma_tac ⌜ℕℝ 0 = ℕℝ  0 ^ 2 ∧ ℕℝ 1 = ℕℝ 1 ^ 2⌝
	THEN1 rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(ALL_FC_T (MAP_EVERY ante_tac)[square_sqrt_thm]);
a(rewrite_tac[] THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏square_times_thm⦎ = save_thm ( "square_times_thm", (
set_goal([], ⌜∀x y:ℝ⦁ (x*y)^2 = x^2 * y^2⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_times_thm⦎ = save_thm ( "sqrt_times_thm", (
set_goal([], ⌜∀x y⦁ℕℝ 0 ≤ x ∧ ℕℝ 0 ≤ y ⇒ Sqrt(x * y) = Sqrt x * Sqrt y⌝);
a(REPEAT strip_tac THEN lemma_tac⌜ℕℝ 0 ≤ x * y ⌝
	THEN1 all_fc_tac[ℝ_0_≤_0_≤_times_thm]);
a(all_fc_tac[sqrt_def]);
a(lemma_tac⌜ℕℝ 0 ≤ Sqrt x * Sqrt y ⌝
	THEN1 all_fc_tac[ℝ_0_≤_0_≤_times_thm]);
a(LEMMA_T⌜Sqrt x * Sqrt y = Abs(Sqrt x * Sqrt y)⌝ once_rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_abs_def]);
a(bc_thm_tac square_sqrt_thm);
a(asm_rewrite_tac[square_times_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏square_recip_thm⦎ = save_thm ( "square_recip_thm", (
set_goal([], ⌜∀x⦁¬x = ℕℝ 0 ⇒ (x ⋏-⋏1) ^ 2 = (x ^ 2) ⋏-⋏1⌝);
a(REPEAT strip_tac THEN asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_pos_thm⦎ = save_thm ( "sqrt_pos_thm", (
set_goal([], ⌜∀x⦁ℕℝ 0 < x ⇒ ℕℝ 0 < Sqrt x⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 ≤ x⌝ THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(all_fc_tac[sqrt_def]);
a(cases_tac⌜¬Sqrt x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(swap_nth_asm_concl_tac 3 THEN asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_recip_thm⦎ = save_thm ( "sqrt_recip_thm", (
set_goal([], ⌜∀x⦁ℕℝ 0 < x ⇒ Sqrt (x ⋏-⋏1) = (Sqrt x) ⋏-⋏1⌝);
a(REPEAT strip_tac);
a(all_fc_tac[sqrt_pos_thm]);
a(all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ Sqrt x ⋏-⋏1⌝ THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(LEMMA_T⌜Sqrt x ⋏-⋏1 = Abs(Sqrt x ⋏-⋏1)⌝ once_rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_abs_def]);
a(bc_thm_tac square_sqrt_thm);
a(lemma_tac⌜¬Sqrt x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[square_recip_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[sqrt_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_exp_log_thm⦎ = save_thm ( "sqrt_exp_log_thm", (
set_goal([], ⌜∀x⦁ℕℝ 0 < x ⇒ Sqrt x = Exp(1/2 * Log x)⌝);
a(REPEAT strip_tac);
a(LEMMA_T ⌜∀x⦁Exp x = Abs(Exp x)⌝ once_rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def, exp_clauses]);
a(bc_thm_tac square_sqrt_thm);
a(rewrite_tac[ℝ_ℕ_exp_square_thm,
	conv_rule(ONCE_MAP_C eq_sym_conv) exp_clauses]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(ALL_FC_T rewrite_tac[exp_log_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_deriv_thm⦎ = save_thm ( "sqrt_deriv_thm", (
set_goal([], ⌜∀x⦁ℕℝ 0 < x ⇒ (Sqrt Deriv 1/2 * Sqrt x * x ⋏-⋏1) x⌝);
a(REPEAT strip_tac THEN bc_thm_tac deriv_local_thm);
a(MAP_EVERY ∃_tac[⌜λx⦁Exp(1/2*Log x)⌝, ⌜x + ℕℝ 1⌝, ⌜ℕℝ 0⌝]
	THEN REPEAT strip_tac
	THEN ALL_FC_T rewrite_tac[sqrt_exp_log_thm,
		log_clauses]);
a(TRANS_DERIV_T ante_tac);
a(asm_rewrite_tac[] THEN conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_mono_thm⦎ = save_thm ( "sqrt_mono_thm", (
set_goal([], ⌜∀x y⦁ℕℝ 0 ≤ x ∧ x < y ⇒ Sqrt x < Sqrt y⌝);
a(REPEAT strip_tac THEN bc_thm_tac deriv_0_less_thm);
a(∃_tac⌜λx⦁ 1/2 * Sqrt x * x ⋏-⋏1⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac sqrt_cts_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[] THEN bc_thm_tac sqrt_deriv_thm
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(rewrite_tac[]);
a(bc_thm_tac ℝ_0_less_0_less_times_thm
	THEN REPEAT strip_tac);
a(bc_thm_tac ℝ_0_less_0_less_times_thm
	THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(bc_thm_tac sqrt_pos_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.2" *** *)
a(bc_thm_tac ℝ_0_less_0_less_recip_thm THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏square_mono_≤_thm⦎ = save_thm ( "square_mono_≤_thm", (
set_goal([], ⌜∀x y⦁ℕℝ 0 ≤ x ∧ ℕℝ 0 ≤ y ⇒ (x ≤ y ⇔ x^2 ≤ y^2)⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac⌜ℕℝ 0 ≤ x^2 ∧ ℕℝ 0 ≤ y^2⌝ THEN1 rewrite_tac[ℝ_0_≤_square_thm]);
a(cases_tac⌜x = ℕℝ 0⌝ THEN1 asm_rewrite_tac[]);
a(cases_tac⌜y = ℕℝ 0⌝ THEN1 asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(LEMMA_T⌜¬x ≤ ℕℝ 0⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(swap_nth_asm_concl_tac 2);
a(LEMMA_T⌜x^2 = ℕℝ 0⌝ ante_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rewrite_tac[ℝ_square_eq_0_thm]);
(* *** Goal "2" *** *)
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y : ℝ ⦁x ≤ y ⇔ ¬y < x⌝,
	prove_rule[]
	⌜∀p q⦁(¬p ⇔ ¬q) ⇔ (q ⇔ p)⌝]);
a(lemma_tac⌜ℕℝ 0 < x ∧ℕℝ 0 < y⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3, 4, 5, 6, 7, 8] discard_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[square_square_root_mono_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏id_over_sqrt_thm⦎ = save_thm ( "id_over_sqrt_thm", (
set_goal([], ⌜∀x⦁ℕℝ 0 < x ⇒ x * Sqrt x ⋏-⋏1 = Sqrt x⌝);
a(REPEAT strip_tac);
a(all_fc_tac[sqrt_pos_thm]);
a(lemma_tac⌜¬Sqrt x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜ℕℝ 0 ≤ x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[sqrt_def]);
a(DROP_NTH_ASM_T 2 (fn th => conv_tac (LEFT_C (LEFT_C (once_rewrite_conv[eq_sym_rule th])))));
a(rewrite_tac[ℝ_ℕ_exp_square_thm, ℝ_times_assoc_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_1_minus_sin_squared_thm⦎ = save_thm ( "sqrt_1_minus_sin_squared_thm", (
set_goal([], ⌜∀x⦁Sqrt(ℕℝ 1 - Sin x ^ 2) = Abs(Cos x)⌝);
a(REPEAT strip_tac);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) cos_squared_plus_sin_squared_thm,
	ℝ_plus_assoc_thm,
	sqrt_square_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sqrt_1_minus_cos_squared_thm⦎ = save_thm ( "sqrt_1_minus_cos_squared_thm", (
set_goal([], ⌜∀x⦁Sqrt(ℕℝ 1 - Cos x ^ 2) = Abs(Sin x)⌝);
a(REPEAT strip_tac);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) cos_squared_plus_sin_squared_thm,
	∀_elim⌜Sin x ^ 2⌝ ℝ_plus_order_thm,
	sqrt_square_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏tan_deriv_thm⦎ = save_thm ( "tan_deriv_thm", (
set_goal([], ⌜∀x⦁
	¬Cos x = ℕℝ 0 ⇒ (Tan Deriv ℕℝ 1 + Tan x ^ 2) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Tan⌝ η_axiom)]);
a(rewrite_tac[tan_def] THEN TRANS_DERIV_T ante_tac);
a(asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(REPEAT (conv_tac(ONCE_MAP_C ℝ_anf_conv)));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cotan_deriv_thm⦎ = save_thm ( "cotan_deriv_thm", (
set_goal([], ⌜∀x⦁
	¬Sin x = ℕℝ 0 ⇒ (Cotan Deriv ~(ℕℝ 1 + Cotan x ^ 2)) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Cotan⌝ η_axiom)]);
a(rewrite_tac[cotan_def] THEN TRANS_DERIV_T ante_tac);
a(asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(rewrite_tac[
	pc_rule1 "ℝ_lin_arith" prove_rule[]
		⌜∀a b:ℝ⦁ ~ a * b = ~(a * b)⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a((conv_tac(ONCE_MAP_C ℝ_anf_conv)));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sec_deriv_thm⦎ = save_thm ( "sec_deriv_thm", (
set_goal([], ⌜∀x⦁
	¬Cos x = ℕℝ 0 ⇒ (Sec Deriv Sec x * Tan x) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Sec⌝ η_axiom)]);
a(rewrite_tac[sec_def, tan_def] THEN TRANS_DERIV_T ante_tac);
a(asm_rewrite_tac[]);
a(REPEAT (conv_tac(ONCE_MAP_C ℝ_anf_conv)));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cosec_deriv_thm⦎ = save_thm ( "cosec_deriv_thm", (
set_goal([], ⌜∀x⦁
	¬Sin x = ℕℝ 0 ⇒ (Cosec Deriv ~(Cosec x) * Cotan x) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Cosec⌝ η_axiom)]);
a(rewrite_tac[cosec_def, cotan_def] THEN TRANS_DERIV_T ante_tac);
a(asm_rewrite_tac[]);
a(REPEAT (conv_tac(ONCE_MAP_C ℝ_anf_conv)));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cos_0_less_thm⦎ = save_thm ( "cos_0_less_thm", (
set_goal([], ⌜(∀ x⦁
	~ (1 / 2) * π < x ∧ x < (1 / 2 * π)
 	⇒ ℕℝ 0 < Cos x)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < x + (1/2) * π ∧ x + (1/2) * π < π⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[rewrite_rule[open_interval_def]
	sin_0_π_0_less_thm]);
a(POP_ASM_T ante_tac THEN rewrite_tac[sin_cos_plus_π_over_2_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜ArcSin⌝;
a(rewrite_tac[ℝ_abs_≤_less_interval_thm]);
a(LEMMA_T⌜∃ g⦁
 (∀ x⦁ x ∈ ClosedInterval (~(1 / 2 * π)) (1 / 2 * π) ⇒ g (Sin x) = x)
∧ (∀ y⦁ y ∈ ClosedInterval (Sin(~(1 / 2 * π))) (Sin (1/2 * π)) ⇒ Sin (g y) = y)
∧ (∀ y⦁ g Cts y)
∧ (∀ x y⦁ x < y ⇒ g x < g y)⌝
	(strip_asm_tac o rewrite_rule[sin_cos_π_over_2_thm,
	sin_cos_minus_thm]));
(* *** Goal "1" *** *)
a(bc_thm_tac closed_interval_inverse_thm);
a(∃_tac⌜Cos⌝ THEN rewrite_tac[sin_def,
	sin_cos_cts_thm]);
a(rewrite_tac[open_interval_def, 
	rewrite_rule[ℝ_times_minus_thm] cos_0_less_thm]);
a(strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
val _ = save_consistency_thm ⌜ArcSin⌝ (pop_thm());

val ⦏arc_sin_def⦎ = save_thm("arc_sin_def", get_spec⌜ArcSin⌝);
=TEX
%%%%
%%%%
=SML

val ⦏sin_arc_sin_thm⦎ = save_thm ( "sin_arc_sin_thm", (
set_goal([], ⌜∀x⦁
	Abs x ≤ ℕℝ 1 ⇒ Sin (ArcSin x) = x
⌝);
a(REPEAT strip_tac THEN all_fc_tac[arc_sin_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏arc_sin_sin_thm⦎ = save_thm ( "arc_sin_sin_thm", (
set_goal([], ⌜∀x⦁
	Abs x ≤ 1/2 * π ⇒ ArcSin (Sin x) = x
⌝);
a(REPEAT strip_tac THEN all_fc_tac[arc_sin_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏arc_sin_cts_thm⦎ = save_thm ( "arc_sin_cts_thm", (
set_goal([], ⌜∀x⦁
	Abs x ≤ ℕℝ 1 ⇒ ArcSin Cts x
⌝);
a(REPEAT strip_tac THEN all_fc_tac[arc_sin_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏abs_arc_sin_thm⦎ = save_thm ( "abs_arc_sin_thm", (
set_goal([], ⌜∀x⦁
	Abs x ≤ ℕℝ 1 ⇒ Abs(ArcSin x) ≤ 1 / 2 * π
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃y⦁Abs y ≤ 1/2 * π ∧ x = Sin y⌝);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac
	THEN rewrite_tac[ℝ_abs_≤_less_interval_thm,
		closed_interval_def]
	THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < π⌝ THEN1 strip_asm_tac π_def);
a(cases_tac⌜x = ℕℝ 1⌝ THEN1 
	(∃_tac⌜1/2 * π⌝
	THEN asm_rewrite_tac[sin_cos_π_over_2_thm]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(cases_tac⌜x = ~(ℕℝ 1)⌝ THEN1 
	(∃_tac⌜~(1/2 * π)⌝
	THEN asm_rewrite_tac[sin_cos_π_over_2_thm,
		sin_cos_minus_thm]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜~(ℕℝ 1) < x ∧ x < ℕℝ 1⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3, 4, 6, 7] discard_tac);
a(ante_tac(list_∀_elim[⌜Sin⌝, ⌜~(1/2 * π)⌝, ⌜1/2 * π⌝]intermediate_value_thm));
a(LEMMA_T ⌜~ (1 / 2 * π) < 1 / 2 * π⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rewrite_tac[sin_cos_cts_thm,
	sin_cos_π_over_2_thm,
	sin_cos_minus_thm]);
a(STRIP_T (strip_asm_tac o ∀_elim⌜x⌝));
a(∃_tac⌜x'⌝ THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(ALL_FC_T asm_rewrite_tac[arc_sin_sin_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cos_arc_sin_thm⦎ = save_thm ( "cos_arc_sin_thm", (
set_goal([], ⌜∀x⦁
	Abs x ≤ ℕℝ 1 ⇒ Cos(ArcSin x) = Sqrt(ℕℝ 1 - x^2)
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[sin_arc_sin_thm, abs_arc_sin_thm]);
a(LEMMA_T⌜x ^ 2 = Sin(ArcSin x) ^ 2⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a(rewrite_tac[rewrite_rule[]sqrt_1_minus_sin_squared_thm]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[closed_interval_def, ℝ_abs_≤_less_interval_thm]));
a(cases_tac⌜ArcSin x = ~(1/2 * π)⌝ THEN1
	asm_rewrite_tac[sin_cos_minus_thm, sin_cos_π_over_2_thm]);
a(cases_tac⌜ArcSin x = 1/2 * π⌝ THEN1
	asm_rewrite_tac[sin_cos_π_over_2_thm]);
a(lemma_tac⌜ArcSin x + 1/2 * π ∈ OpenInterval (ℕℝ 0) π⌝
	THEN1 (rewrite_tac[open_interval_def]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(ALL_FC_T (MAP_EVERY ante_tac) [sin_0_π_0_less_thm]);
a(rewrite_tac[sin_cos_plus_π_over_2_thm, ℝ_abs_def]);
a(REPEAT strip_tac THEN asm_rewrite_tac[ℝ_≤_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏arc_sin_1_minus_1_thm⦎ = save_thm ( "arc_sin_1_minus_1_thm", (
set_goal([], ⌜
	ArcSin(ℕℝ 1) = (1/2) * π ∧ ArcSin(~(ℕℝ 1)) = ~(1/2) * π
⌝);
a(LEMMA_T⌜~(ℕℝ 1) = Sin (~ (1/2 * π))⌝ rewrite_thm_tac
	THEN1 rewrite_tac[sin_cos_minus_thm, sin_cos_π_over_2_thm]);
a(LEMMA_T⌜ℕℝ 1 = Sin (1/2 * π) ∧ ~(1/2) * π = ~(1/2 * π)⌝ asm_rewrite_thm_tac
	THEN1 (conv_tac (ONCE_MAP_C (ℝ_anf_conv))
		THEN rewrite_tac[sin_cos_π_over_2_thm]));
a(REPEAT strip_tac THEN bc_thm_tac arc_sin_sin_thm
	THEN_TRY rewrite_tac[ℝ_abs_minus_thm]);
(* *** Goal "1" duplicates "2" *** *)
a(lemma_tac⌜ℕℝ 0 ≤ (1/2) * π⌝ 
	THEN1 (strip_asm_tac π_def THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(asm_rewrite_tac[ℝ_abs_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏arc_sin_deriv_thm⦎ = save_thm ( "arc_sin_deriv_thm", (
set_goal([], ⌜∀x⦁
	Abs x < ℕℝ 1 ⇒ (ArcSin Deriv Sqrt(ℕℝ 1 - x^2)⋏-⋏1) x
⌝);
a(rewrite_tac[ℝ_abs_≤_less_interval_thm,
		open_interval_def]
	THEN REPEAT strip_tac
	THEN bc_thm_tac inverse_deriv_thm);
a(MAP_EVERY ∃_tac [⌜Sin⌝, ⌜ℕℝ 1⌝, ⌜~(ℕℝ 1)⌝]);
a(asm_rewrite_tac[open_interval_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac (rewrite_rule[ℝ_abs_≤_less_interval_thm,
		closed_interval_def]
	sin_arc_sin_thm) THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜(Sin Deriv Cos(ArcSin x))(ArcSin x)⌝
	ante_tac THEN1 rewrite_tac[sin_def]);
a(ALL_FC_T rewrite_tac[rewrite_rule[ℝ_abs_≤_less_interval_thm,
		closed_interval_def, ℝ_≤_def] cos_arc_sin_thm]);
(* *** Goal "3" *** *)
a(bc_thm_tac arc_sin_cts_thm
	THEN rewrite_tac[ℝ_abs_≤_less_interval_thm,
		closed_interval_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(LEMMA_T⌜ℕℝ 0 < Sqrt(ℕℝ 1 + ~ (x ^ 2))⌝ ante_tac
	THEN_LIST [bc_thm_tac sqrt_pos_thm,
		PC_T1 "ℝ_lin_arith" prove_tac[]]);
a(rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(lemma_tac⌜ℕℝ 1 + ~ (x * x) = (ℕℝ 1 + x) * (ℕℝ 1 + ~x)
	∧ ℕℝ 0 < ℕℝ 1 + x ∧ ℕℝ 0 < ℕℝ 1 + ~x⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[] THEN LIST_DROP_NTH_ASM_T[3, 4, 5] discard_tac);
a(all_fc_tac[ℝ_0_less_0_less_times_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜ArcCos⌝;
a(∃_tac⌜λx⦁ArcSin (~x) + (1/2) * π⌝
	THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[rewrite_rule[ℝ_plus_assoc_thm](∀_elim⌜x + ~((1/2) * π)⌝sin_cos_plus_π_over_2_thm)]);
a(LEMMA_T⌜∀a b:ℝ⦁a + b = x ⇔ a = x + ~b⌝ rewrite_thm_tac
	THEN1 PC_T1"ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac arc_sin_sin_thm);
a(cases_tac⌜ ℕℝ 0 ≤ x + ~(1 / 2 * π)⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[sin_cos_plus_π_over_2_thm]);
a(LEMMA_T⌜∀a b:ℝ⦁~a = x ⇔ a = ~x⌝ rewrite_thm_tac
	THEN1 PC_T1"ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac sin_arc_sin_thm);
a(asm_rewrite_tac[ℝ_abs_minus_thm]);
(* *** Goal "3" *** *)
a(REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(bc_thm_tac comp_cts_thm);
a(rewrite_tac[minus_cts_thm]);
a(bc_thm_tac arc_sin_cts_thm);
a(asm_rewrite_tac[ℝ_abs_minus_thm]);
val _ = save_consistency_thm ⌜ArcCos⌝ (pop_thm());

val ⦏arc_cos_def⦎ = save_thm("arc_cos_def", get_spec⌜ArcCos⌝);
=TEX
%%%%
%%%%
=SML

val ⦏cos_arc_cos_thm⦎ = save_thm ( "cos_arc_cos_thm", (
set_goal([], ⌜∀x⦁
	Abs x ≤ ℕℝ 1 ⇒ Cos (ArcCos x) = x
⌝);
a(REPEAT strip_tac THEN all_fc_tac[arc_cos_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏arc_cos_cos_thm⦎ = save_thm ( "arc_cos_cos_thm", (
set_goal([], ⌜∀x⦁
	ℕℝ 0 ≤ x ∧ x ≤ π ⇒ ArcCos (Cos x) = x
⌝);
a(REPEAT strip_tac THEN all_fc_tac[arc_cos_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏arc_cos_cts_thm⦎ = save_thm ( "arc_cos_cts_thm", (
set_goal([], ⌜∀x⦁
	Abs x ≤ ℕℝ 1 ⇒ ArcCos Cts x
⌝);
a(REPEAT strip_tac THEN all_fc_tac[arc_cos_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏abs_arc_cos_thm⦎ = save_thm ( "abs_arc_cos_thm", (
set_goal([], ⌜∀x⦁
	Abs x ≤ ℕℝ 1 ⇒ ℕℝ 0 ≤ ArcCos x ∧ ArcCos x ≤ π
⌝);
a(∀_tac THEN ⇒_tac);
a(lemma_tac⌜∃y⦁ℕℝ 0 ≤ y ∧ y ≤ π ∧ x = Cos y⌝);
(* *** Goal "1" *** *)
a(POP_ASM_T ante_tac
	THEN rewrite_tac[ℝ_abs_≤_less_interval_thm,
		closed_interval_def]
	THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < π⌝ THEN1 strip_asm_tac π_def);
a(cases_tac⌜x = ℕℝ 1⌝ THEN1 
	(∃_tac⌜ℕℝ 0⌝
	THEN asm_rewrite_tac[cos_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(cases_tac⌜x = ~(ℕℝ 1)⌝ THEN1 
	(∃_tac⌜π⌝
	THEN asm_rewrite_tac[sin_cos_π_thm]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜~(ℕℝ 1) < x ∧ x < ℕℝ 1⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3, 4, 6, 7] discard_tac);
a(ante_tac(list_∀_elim[⌜Cos⌝, ⌜ℕℝ 0⌝, ⌜π⌝]intermediate_value_thm));
a(asm_rewrite_tac[sin_cos_cts_thm,
	sin_cos_π_thm, cos_def]);
a(STRIP_T (strip_asm_tac o ∀_elim⌜x⌝));
a(∃_tac⌜x'⌝ THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1);
a(ALL_FC_T asm_rewrite_tac[arc_cos_cos_thm]);
pop_thm()
));

=TEX
%%%%
%%%% HYPERBOLIC TRIGONOMETRIC FUNCTIONS
%%%%
=SML

val ⦏sinh_deriv_thm⦎ = save_thm ( "sinh_deriv_thm", (
set_goal([], ⌜∀x⦁ (Sinh Deriv Cosh x) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Sinh⌝ η_axiom)]);
a(rewrite_tac[cosh_def, sinh_def] THEN TRANS_DERIV_T ante_tac);
a(asm_rewrite_tac[]);
a(REPEAT (conv_tac(ONCE_MAP_C ℝ_anf_conv)));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cosh_deriv_thm⦎ = save_thm ( "cosh_deriv_thm", (
set_goal([], ⌜∀x⦁ (Cosh Deriv Sinh x) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Cosh⌝ η_axiom)]);
a(rewrite_tac[cosh_def, sinh_def] THEN TRANS_DERIV_T ante_tac);
a(asm_rewrite_tac[]);
a(REPEAT (conv_tac(ONCE_MAP_C ℝ_anf_conv)));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cosh_0_less_thm⦎ = save_thm ( "cosh_0_less_thm", (
set_goal([], ⌜∀x⦁ ℕℝ 0 < Cosh x⌝);
a(rewrite_tac[cosh_def] THEN contr_tac);
a(lemma_tac⌜ℕℝ 0 < Exp x ∧ ℕℝ 0 < Exp (~x)⌝
	THEN1 rewrite_tac[exp_0_less_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cosh_non_0_thm⦎ = save_thm ( "cosh_non_0_thm", (
set_goal([], ⌜∀x⦁ ¬Cosh x = ℕℝ 0⌝);
a(rewrite_tac[cosh_def] THEN contr_tac);
a(lemma_tac⌜ℕℝ 0 < Exp x ∧ ℕℝ 0 < Exp (~x)⌝
	THEN1 rewrite_tac[exp_0_less_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sinh_non_0_thm⦎ = save_thm ( "sinh_non_0_thm", (
set_goal([], ⌜∀x⦁ Sinh x = ℕℝ 0 ⇔ x = ℕℝ 0⌝);
a(rewrite_tac[sinh_def] THEN REPEAT strip_tac);
a(contr_tac THEN lemma_tac⌜x < ~x ∨ ~x < x⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN all_fc_tac[exp_less_mono_thm]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cosh_squared_minus_sinh_squared_thm⦎ = save_thm ( "cosh_squared_minus_sinh_squared_thm", (
set_goal([], ⌜∀x⦁ Cosh x ^ 2 - Sinh x ^ 2 = ℕℝ 1⌝);
a(rewrite_tac[sinh_def, cosh_def, ℝ_ℕ_exp_square_thm]
	THEN REPEAT strip_tac);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) exp_plus_thm]);
a(rewrite_tac[exp_clauses]);
pop_thm()
));

=TEX
=SML
val ⦏trans_deriv_thms1⦎ = sinh_deriv_thm :: cosh_deriv_thm :: trans_deriv_thms;
val ⦏TRANS_DERIV_T1⦎ = DERIV_T trans_deriv_thms1;
=TEX
%%%%
%%%%
=SML

val ⦏tanh_deriv_thm⦎ = save_thm ( "tanh_deriv_thm", (
set_goal([], ⌜∀x⦁ (Tanh Deriv ℕℝ 1 - Tanh x ^ 2) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Tanh⌝ η_axiom)]);
a(rewrite_tac[tanh_def] THEN TRANS_DERIV_T1 ante_tac);
a(strip_asm_tac(∀_elim⌜x⌝ cosh_non_0_thm));
a(ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
a(rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(REPEAT(CHANGED_T (conv_tac(ONCE_MAP_C ℝ_anf_conv))));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cotanh_deriv_thm⦎ = save_thm ( "cotanh_deriv_thm", (
set_goal([], ⌜∀x⦁ ¬x = ℕℝ 0 ⇒ (Cotanh Deriv ℕℝ 1 - Cotanh x ^ 2) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Cotanh⌝ η_axiom)]);
a(rewrite_tac[cotanh_def] THEN TRANS_DERIV_T1 ante_tac);
a(strip_asm_tac(∀_elim⌜x⌝ sinh_non_0_thm));
a(ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
a(rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(REPEAT(CHANGED_T (conv_tac(ONCE_MAP_C ℝ_anf_conv))));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sech_deriv_thm⦎ = save_thm ( "sech_deriv_thm", (
set_goal([], ⌜∀x⦁ (Sech Deriv ~(Sech x) * Tanh x) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Sech⌝ η_axiom)]);
a(rewrite_tac[sech_def, tanh_def] THEN TRANS_DERIV_T1 ante_tac);
a(rewrite_tac[cosh_non_0_thm]);
a(REPEAT(CHANGED_T (conv_tac(ONCE_MAP_C ℝ_anf_conv))));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cosech_deriv_thm⦎ = save_thm ( "cosech_deriv_thm", (
set_goal([], ⌜∀x⦁ ¬x = ℕℝ 0 ⇒ (Cosech Deriv ~(Cosech x) * Cotanh x) x⌝);
a(REPEAT strip_tac THEN pure_once_rewrite_tac[eq_sym_rule(∀_elim⌜Cosech⌝ η_axiom)]);
a(rewrite_tac[cotanh_def, cosech_def] THEN TRANS_DERIV_T1 ante_tac);
a(strip_asm_tac(∀_elim⌜x⌝ sinh_non_0_thm));
a(asm_rewrite_tac[]);
a(REPEAT(CHANGED_T (conv_tac(ONCE_MAP_C ℝ_anf_conv))));
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sinh_cts_thm⦎ = save_thm ( "sinh_cts_thm", (
set_goal([], ⌜∀x⦁ Sinh Cts x⌝);
a(REPEAT strip_tac THEN bc_thm_tac deriv_cts_thm);
a(∃_tac⌜Cosh x⌝ THEN rewrite_tac[sinh_deriv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cosh_cts_thm⦎ = save_thm ( "cosh_cts_thm", (
set_goal([], ⌜∀x⦁ Cosh Cts x⌝);
a(REPEAT strip_tac THEN bc_thm_tac deriv_cts_thm);
a(∃_tac⌜Sinh x⌝ THEN rewrite_tac[cosh_deriv_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sinh_mono_thm⦎ = save_thm ( "sinh_mono_thm", (
set_goal([], ⌜∀x y⦁ x < y ⇒ Sinh x < Sinh y⌝);
a(REPEAT strip_tac THEN bc_thm_tac deriv_0_less_thm);
a(∃_tac⌜Cosh⌝ THEN rewrite_tac[sinh_deriv_thm,
	cosh_0_less_thm, sinh_cts_thm]
	THEN REPEAT strip_tac THEN bc_thm_tac deriv_cts_thm);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sinh_cosh_0_thm⦎ = save_thm ( "sinh_cosh_0_thm", (
set_goal([], ⌜Sinh (ℕℝ 0) = ℕℝ 0 ∧ Cosh(ℕℝ 0) = ℕℝ 1⌝);
a(rewrite_tac[sinh_def, cosh_def, exp_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏sinh_cosh_minus_thm⦎ = save_thm ( "sinh_cosh_minus_thm", (
set_goal([], ⌜∀x⦁ Sinh (~x) = ~(Sinh x) ∧ Cosh(~x) = Cosh x⌝);
a(rewrite_tac[sinh_def, cosh_def]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀x⦁ ℕℝ 0 < x ⇒ 
	ℕℝ 0 < Log(ℕℝ 2 * x + ℕℝ 1) ∧ x < Sinh(Log(ℕℝ 2 * x + ℕℝ 1))⌝);
a(REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac⌜ℕℝ 0 < ℕℝ 2 * x + ℕℝ 1 ∧ℕℝ 0 < ℕℝ 2 * x⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜ℕℝ 0 < Log (ℕℝ 2 * x + ℕℝ 1)⌝
	THEN1 (once_rewrite_tac[exp_less_mono_thm]
		THEN rewrite_tac[exp_clauses]
		THEN ALL_FC_T asm_rewrite_tac[exp_log_thm]));
(* *** Goal "2" *** *)
a(rewrite_tac[sinh_def, ℝ_times_plus_distrib_thm, exp_clauses]);
a(lemma_tac⌜ℕℝ 0 < ℕℝ 2 * x + ℕℝ 1 ∧ℕℝ 0 < ℕℝ 2 * x⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[exp_log_thm]);
a(rewrite_tac[ℝ_times_plus_distrib_thm, ℝ_times_assoc_thm1,
	ℝ_plus_assoc_thm]);
a(all_fc_tac[rewrite_rule[](list_∀_elim[⌜ℕℝ 1⌝, ⌜(ℕℝ 2 * x + ℕℝ 1)⌝]ℝ_less_recip_less_thm)]);
a(bc_thm_tac(pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀z⦁z < ℕℝ 1 ⇒ ℕℝ 0 < 1/2 + 1/2 * ~z⌝));
a(REPEAT strip_tac);
val ⦏sinh_bound_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
(*
drop_main_goal();
*)
push_consistency_goal ⌜ArcSinh⌝;
a(lemma_tac⌜∀x⦁∃y⦁ Sinh y = x⌝);
(* *** Goal "1" *** *)
a(lemma_tac⌜∀x⦁ℕℝ 0 < x ⇒ ∃y⦁ Sinh y = x⌝
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(all_fc_tac[sinh_bound_lemma]);
a(ante_tac(list_∀_elim[⌜Sinh⌝, ⌜ℕℝ 0⌝, ⌜Log(ℕℝ 2 * x + ℕℝ 1)⌝]intermediate_value_thm));
a(asm_rewrite_tac[sinh_cosh_0_thm, sinh_cts_thm]);
a(STRIP_T (ante_tac o ∀_elim⌜x⌝));
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(cases_tac⌜x = ℕℝ 0⌝
	THEN1 (∃_tac⌜ℕℝ 0⌝ THEN asm_rewrite_tac[sinh_cosh_0_thm]));
a(cases_tac⌜ℕℝ 0 < x⌝ 
	THEN1 (DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac));
a(lemma_tac⌜ℕℝ 0 < ~x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
a(∃_tac⌜~y⌝ THEN asm_rewrite_tac[sinh_cosh_minus_thm]);
(* *** Goal "2" *** *)
a(ante_tac (∀_elim⌜Sinh⌝ total_inverse_thm));
a(asm_rewrite_tac[sinh_mono_thm]
	THEN REPEAT strip_tac);
a(∃_tac⌜g⌝ THEN asm_rewrite_tac[]);
val _ = save_consistency_thm ⌜ArcSinh⌝ (pop_thm());

val ⦏arc_sinh_def⦎ = save_thm("arc_sinh_def", get_spec⌜ArcSinh⌝);
=TEX
%%%%
%%%%
=SML

val ⦏sqrt_1_plus_sinh_squared_thm⦎ = save_thm ( "sqrt_1_plus_sinh_squared_thm", (
set_goal([], ⌜∀x⦁ Sqrt (ℕℝ 1 + Sinh x ^ 2) = Cosh x⌝);
a(REPEAT strip_tac);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) cosh_squared_minus_sinh_squared_thm,
	ℝ_plus_assoc_thm,
	sqrt_square_thm]);
a(rewrite_tac[ℝ_abs_def, ℝ_≤_def, cosh_0_less_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏cosh_arc_sinh_thm⦎ = save_thm ( "cosh_arc_sinh_thm", (
set_goal([], ⌜∀x⦁ Cosh(ArcSinh x) = Sqrt(ℕℝ 1 + x^2)⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜x ^ 2 = Sinh(ArcSinh x) ^ 2⌝ rewrite_thm_tac
	THEN1 rewrite_tac[arc_sinh_def]);
a(rewrite_tac[sqrt_1_plus_sinh_squared_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏arc_sinh_deriv_thm⦎ = save_thm ( "arc_sinh_deriv_thm", (
set_goal([], ⌜∀x⦁ (ArcSinh Deriv Sqrt(ℕℝ 1 + x^2)⋏-⋏1) x⌝);
a(REPEAT strip_tac THEN bc_thm_tac inverse_deriv_thm);
a(MAP_EVERY ∃_tac [⌜Sinh⌝, ⌜x + ℕℝ 1⌝, ⌜x + ~(ℕℝ 1)⌝]);
a(asm_rewrite_tac[open_interval_def, arc_sinh_def,
	conv_rule(ONCE_MAP_C eq_sym_conv) cosh_arc_sinh_thm,
	sinh_deriv_thm, cosh_non_0_thm] THEN REPEAT strip_tac);
pop_thm()
));

=TEX
\subsection{Integration}
%%%%
%%%% GAUGE INTEGRAL
%%%%
=SML

val ⦏gauge_∩_thm⦎ = save_thm ( "gauge_∩_thm", (
set_goal([], ⌜∀G1 G2⦁
	G1 ∈ Gauge ∧ G2 ∈ Gauge
⇒	(λx⦁G1 x ∩ G2 x) ∈ Gauge
⌝);
a(rewrite_tac[gauge_def] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
a(bc_thm_tac ∩_open_ℝ_thm THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏gauge_o_minus_thm⦎ = save_thm ( "gauge_o_minus_thm", (
set_goal([], ⌜∀G⦁
	G ∈ Gauge
⇒	(λx⦁{t | ~t ∈ G(~x)}) ∈ Gauge
⌝);
a(rewrite_tac[gauge_def, open_ℝ_def,
	open_interval_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext" (LIST_DROP_NTH_ASM_T [2]) all_fc_tac);
a(∃_tac⌜~y⌝ THEN ∃_tac ⌜~x'⌝
	THEN PC_T1 "sets_ext" REPEAT strip_tac
	THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏gauge_o_plus_thm⦎ = save_thm ( "gauge_o_plus_thm", (
set_goal([], ⌜∀G h⦁
	G ∈ Gauge
⇒	(λx⦁ {t | t + h ∈ G (x + h)}) ∈ Gauge
⌝);
a(rewrite_tac[gauge_def, open_ℝ_def,
	open_interval_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext" (LIST_DROP_NTH_ASM_T [2]) all_fc_tac);
a(∃_tac⌜x' + ~h⌝ THEN ∃_tac ⌜y + ~h⌝
	THEN PC_T1 "sets_ext" REPEAT strip_tac
	THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏gauge_o_times_thm⦎ = save_thm ( "gauge_o_times_thm", (
set_goal([], ⌜∀c G⦁
	G ∈ Gauge
∧	¬c = ℕℝ 0
⇒	(λx⦁ {t | c*t ∈ G (c*x)}) ∈ Gauge
⌝);
a(lemma_tac⌜∀G c⦁
	G ∈ Gauge
∧	ℕℝ 0 < c
⇒	(λx⦁ {t | c*t ∈ G (c*x)}) ∈ Gauge⌝);
(* *** Goal "1" *** *)
a(PC_T1 "sets_ext" rewrite_tac[gauge_def,
		open_ℝ_def, open_interval_def]
	THEN REPEAT strip_tac
	THEN_LIST [id_tac, asm_rewrite_tac[]]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(∃_tac⌜c ⋏-⋏1 * x'⌝ THEN ∃_tac ⌜c ⋏-⋏1 * y⌝);
a(all_fc_tac[ℝ_0_less_0_less_recip_thm,
	pc_rule1"ℝ_lin_arith" prove_rule[]
	⌜∀u⦁ℕℝ 0 < c ⇒ ¬c = ℕℝ 0⌝]);
a(strip_tac);
(* *** Goal "1.1" *** *)
a(ALL_FC_T (MAP_EVERY ante_tac) [ℝ_times_mono_thm]);
a(ALL_FC_T (fn ths => rewrite_tac ths
	THEN rewrite_tac[ℝ_times_assoc_thm1]
	THEN rewrite_tac ths) [ℝ_recip_clauses]);
a(REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 bc_thm_tac);
a(ALL_FC_T (MAP_EVERY ante_tac) [ℝ_times_mono_thm]);
a(ALL_FC_T (fn ths => rewrite_tac ths
	THEN rewrite_tac[ℝ_times_assoc_thm1]
	THEN rewrite_tac ths) [ℝ_recip_clauses]);
a(REPEAT strip_tac);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(cases_tac⌜ℕℝ 0 < c⌝ THEN1 all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(all_fc_tac[gauge_o_minus_thm]);
a(DROP_NTH_ASM_T 4 discard_tac);
a(lemma_tac⌜ℕℝ 0 < ~c⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5] (ALL_FC_T (MAP_EVERY ante_tac)));
a(rewrite_tac[] THEN conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏gauge_refinement_thm⦎ = save_thm ( "gauge_refinement_thm", (
set_goal([], ⌜∀G1 G2⦁
	G1 ∈ Gauge ∧ G2 ∈ Gauge
⇒	∃G⦁ G ∈ Gauge ∧ (∀x⦁ G x ⊆ G1 x) ∧ (∀x⦁ G x ⊆ G2 x)
⌝);
a(REPEAT strip_tac);
a(∃_tac⌜λx⦁G1 x ∩ G2 x⌝ THEN
	ALL_FC_T rewrite_tac[gauge_∩_thm]);
a(PC_T1 "sets_ext" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏gauge_refine_3_thm⦎ = save_thm ( "gauge_refine_3_thm", (
set_goal([], ⌜∀G1 G2 G3⦁
	G1 ∈ Gauge ∧ G2 ∈ Gauge ∧ G3 ∈ Gauge
⇒	∃G⦁ G ∈ Gauge ∧ (∀x⦁ G x ⊆ G1 x) ∧ (∀x⦁ G x ⊆ G2 x) ∧ (∀x⦁ G x ⊆ G3 x)
⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜G1⌝, ⌜G2⌝] gauge_refinement_thm));
a(strip_asm_tac(list_∀_elim[⌜G3⌝, ⌜G⌝] gauge_refinement_thm));
a(∃_tac⌜G'⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏fine_refinement_thm⦎ = save_thm ( "fine_refinement_thm", (
set_goal([], ⌜∀G1 G2 t I n⦁
	(∀x⦁ G1 x ⊆ G2 x)
∧	(t, I, n) ∈ G1 Fine
⇒	(t, I, n) ∈ G2 Fine
⌝);
a(rewrite_tac[fine_def] THEN REPEAT strip_tac);
a(all_asm_fc_tac[]);
a(PC_T1 "sets_ext" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏chosen_tag_thm⦎ = save_thm ( "chosen_tag_thm", (
set_goal([], ⌜∀a⦁ ∃G1⦁
	G1 ∈ Gauge
∧	∀G2⦁ G2 ∈ Gauge
∧	(∀x⦁ G2 x ⊆ G1 x)
⇒	∀t I n m⦁	 m < n
	∧	(t, I, n) ∈ TaggedPartition
	∧	(t, I, n) ∈ G2 Fine
	∧	a ∈ ClosedInterval (I m) (I (m+1))
	⇒	t m = a
⌝);
a(REPEAT strip_tac THEN rewrite_tac[fine_def, gauge_def,
	tagged_partition_def]
	THEN REPEAT strip_tac);
a(∃_tac⌜λx⦁
	if	x = a
	then	Universe
	else	{t | t < a} ∪ {t | a < t}⌝	
	THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(cases_tac⌜x = a⌝ THEN asm_rewrite_tac[
	empty_universe_open_closed_thm]);
a(bc_tac[∪_open_ℝ_thm]
	THEN asm_rewrite_tac[half_infinite_intervals_open_thm]);
(* *** Goal "2" *** *)
a(cases_tac⌜x = a⌝ THEN PC_T1 "sets_ext" asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(LIST_DROP_NTH_ASM_T [2] (PC_T1 "sets_ext" all_fc_tac));
a(LIST_DROP_NTH_ASM_T [6] (PC_T1 "sets_ext" all_fc_tac));
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
a(PC_T1 "sets_ext" asm_rewrite_tac[]);
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏chosen_tags_thm⦎ = save_thm ( "chosen_tags_thm", (
set_goal([], ⌜∀list⦁ ∃G1⦁
	G1 ∈ Gauge
∧	∀G2⦁ G2 ∈ Gauge
∧	(∀x⦁ G2 x ⊆ G1 x)
⇒	∀t I n m a⦁m < n
	∧	(t, I, n) ∈ TaggedPartition
	∧	(t, I, n) ∈ G2 Fine
	∧	a ∈ ClosedInterval (I m) (I (m+1))
	∧	a ∈ Elems list
	⇒	t m = a
⌝);
a(REPEAT strip_tac);
a(list_induction_tac⌜list⌝ THEN rewrite_tac[elems_def]);
(* *** Goal "1" *** *)
a(∃_tac⌜λx⦁ Universe⌝ THEN asm_rewrite_tac[gauge_def,
	empty_universe_open_closed_thm]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜x⌝] chosen_tag_thm));
a(strip_asm_tac (list_∀_elim[⌜G1⌝, ⌜G1'⌝] gauge_refinement_thm));
a(∃_tac⌜G⌝ THEN REPEAT strip_tac
	THEN all_fc_tac[pc_rule1 "sets_ext" prove_rule[]
	⌜∀a b c⦁(∀x⦁ a x ⊆ b x) ∧ (∀x⦁b x ⊆ c x) ⇒ ∀x⦁a x ⊆ c x⌝]);
(* *** Goal "2.1" *** *)
a(all_var_elim_asm_tac);
a(LIST_DROP_NTH_ASM_T [12] all_fc_tac);
(* *** Goal "2.3" *** *)
a(all_fc_tac[fine_refinement_thm]);
a(LIST_DROP_NTH_ASM_T [18] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_gauge_thm⦎ = save_thm ( "riemann_gauge_thm", (
set_goal([], ⌜∀e⦁ ℕℝ 0 < e
⇒	∃G⦁ G ∈ Gauge
∧	∀t I n m⦁	 m < n
	∧	(t, I, n) ∈ TaggedPartition
	∧	(t, I, n) ∈ G Fine
	⇒	I(m + 1) - I m < e
⌝);
a(REPEAT strip_tac THEN rewrite_tac[
	gauge_def, tagged_partition_def, fine_def]
	THEN REPEAT strip_tac);
a(∃_tac⌜λx:ℝ⦁ OpenInterval (x - 1/4 * e) (x + 1/4 * e)⌝);
a(rewrite_tac[open_interval_open_thm]);
a(PC_T1 "sets_ext" rewrite_tac [open_interval_def,
	closed_interval_def]);
a(REPEAT strip_tac THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [3, 2, 1]
	(MAP_EVERY (strip_asm_tac o ∀_elim⌜m⌝)));
a(TOP_ASM_T (ante_tac o list_∀_elim[⌜I m⌝]));
a(POP_ASM_T (ante_tac o list_∀_elim[⌜I(m+1)⌝]));
a(asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏tagged_partition_∃_thm⦎ = list_save_thm ( ["tagged_partition_∃_thm", "cousin_lemma"], (
set_goal([], ⌜∀G a b⦁
	G ∈ Gauge ∧ a ≤ b
⇒	∃t I n⦁
		I 0 = a ∧ I n = b
	∧	(t, I, n) ∈ TaggedPartition
	∧	(t, I, n) ∈ G Fine
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac(rewrite_rule[](∀_elim⌜λc d⦁∃t I n⦁ I 0 = c ∧ I n = d
	∧	(t, I, n) ∈ TaggedPartition
	∧	(t, I, n) ∈ G Fine⌝bisection_thm)));
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(MAP_EVERY ∃_tac[
	⌜λm⦁if m < n then t m else t' (m - n)⌝,
	⌜λm⦁if m ≤ n then I m else I' (m - n)⌝,
	⌜n + n'⌝]);
a(LIST_DROP_NTH_ASM_T [1, 2, 5, 6] (MAP_EVERY ante_tac)
	THEN rewrite_tac[tagged_partition_def, fine_def]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(cases_tac⌜n' = 0⌝ THEN1 all_var_elim_asm_tac1
	THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(cases_tac⌜m + 1 ≤ n⌝ THEN1
	(lemma_tac⌜m ≤ n ∧ m < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]
		THEN ALL_ASM_FC_T asm_rewrite_tac[]));
a(asm_rewrite_tac[]);
a(cases_tac⌜m = n⌝ THEN1 asm_rewrite_tac[]);
(* *** Goal "1.2.1" *** *)
a(all_var_elim_asm_tac);
a((DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜0⌝)
		THEN asm_rewrite_tac[]));
(* *** Goal "1.2.2" *** *)
a(lemma_tac⌜¬m ≤ n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]
		THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜n ≤ m⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(LEMMA_T ⌜(n + i) + 1 = (i + 1) + n⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" prove_tac[]);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
(* *** Goal "1.3" *** *)
a(cases_tac⌜m + 1 ≤ n⌝ THEN1
	(lemma_tac⌜m < n ∧ m ≤ n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[])
		THEN ALL_ASM_FC_T asm_rewrite_tac[]);
a(cases_tac⌜m = n⌝ THEN1 asm_rewrite_tac[]);
(* *** Goal "1.3.1" *** *)
a(all_var_elim_asm_tac);
a((DROP_NTH_ASM_T 3 (ante_tac o ∀_elim⌜0⌝)
		THEN asm_rewrite_tac[]));
(* *** Goal "1.3.2" *** *)
a(lemma_tac⌜¬m ≤ n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]
		THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜n ≤ m⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
a(LEMMA_T ⌜(n + i) + 1 = (i + 1) + n⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
(* *** Goal "1.4" *** *)
a(cases_tac⌜m + 1 ≤ n⌝ THEN1
	(lemma_tac⌜m ≤ n ∧ m < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[])
		THEN ALL_ASM_FC_T asm_rewrite_tac[]);
a(cases_tac⌜m = n⌝ THEN1 asm_rewrite_tac[]);
(* *** Goal "1.4.1" *** *)
a(all_var_elim_asm_tac);
a((DROP_NTH_ASM_T 2(ante_tac o ∀_elim⌜0⌝)
		THEN asm_rewrite_tac[]));
(* *** Goal "1.4.2" *** *)
a(lemma_tac⌜¬m ≤ n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]
		THEN asm_rewrite_tac[]);
a(LEMMA_T ⌜n ≤ m⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
a(LEMMA_T ⌜(n + i) + 1 = (i + 1) + n⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" prove_tac[]);
a(LIST_DROP_NTH_ASM_T [4] all_fc_tac);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 2 (strip_asm_tac
	o rewrite_rule[gauge_def, open_interval_def, open_ℝ_delta_thm]));
a(spec_nth_asm_tac 1 ⌜y⌝);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜d⌝ THEN REPEAT strip_tac);
a(cases_tac⌜z = x⌝ THEN1 all_var_elim_asm_tac);
(* *** Goal "2.1" *** *)
a(MAP_EVERY ∃_tac[⌜λm:ℕ⦁x⌝, ⌜λm⦁x⌝, ⌜0⌝]);
a(rewrite_tac[tagged_partition_def, fine_def]);
(* *** Goal "2.2" *** *)
a(MAP_EVERY ∃_tac[
	⌜λm:ℕ⦁ if m = 0 then y else z⌝,
	⌜λm⦁if m = 0 then x else z⌝,
	⌜1⌝]);
a(rewrite_tac[tagged_partition_def, fine_def,
	closed_interval_def,
	pc_rule1 "lin_arith" prove_rule[]
	⌜∀m ⦁ m < 1 ⇔ m = 0⌝]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac1
	THEN rewrite_tac[]
	THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(PC_T1 "sets_ext" REPEAT strip_tac);
a(DROP_NTH_ASM_T 7 bc_thm_tac);
a(cases_tac⌜ℕℝ 0 ≤ x' + ~y⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

val ⦏cousin_lemma⦎ = tagged_partition_∃_thm;
=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_induction_thm⦎ = save_thm ( "riemann_sum_induction_thm", (
set_goal([], ⌜∀f t I n⦁
	RiemannSum f (t, I, 0) = ℕℝ 0
∧	RiemannSum f (t, I, (n+1)) =
	RiemannSum f (t, I, n) +
	f(t n) * (I(n+1) - I n)
⌝);
a(REPEAT strip_tac
	THEN rewrite_tac[riemann_sum_def, series_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏series_induction_thm1⦎ = save_thm ( "series_induction_thm1", (
set_goal([], ⌜∀s n⦁
	Series s (n + 1) = s 0 + Series (λm⦁s(m + 1)) n
⌝);
a(REPEAT strip_tac);
a(rewrite_tac[series_shift_thm,
	∧_left_elim series_def,
	rewrite_rule[]
		(list_∀_elim[⌜s⌝, ⌜0⌝] (∧_right_elim series_def))]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ℝ_abs_series_thm⦎ = save_thm ( "ℝ_abs_series_thm", (
set_goal([], ⌜∀s n⦁
	Abs(Series s n) ≤ Series (λm⦁Abs(s m)) n
⌝);
a(REPEAT strip_tac);
a(induction_tac ⌜n⌝ THEN rewrite_tac[series_def]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac
	⌜Abs (Series s n) + Abs(s n)⌝
	THEN asm_rewrite_tac[ℝ_abs_plus_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_induction_thm1⦎ = save_thm ( "riemann_sum_induction_thm1", (
set_goal([], ⌜∀f t I n⦁
	RiemannSum f (t, I, 0) = ℕℝ 0
∧	RiemannSum f (t, I, (n+1)) =
	f(t 0) * (I 1 - I 0) +
	RiemannSum f ((λm⦁t(m+1)), (λm⦁I(m+1)), n)
⌝);
a(REPEAT strip_tac
	THEN rewrite_tac[riemann_sum_def, series_induction_thm1]);
a(rewrite_tac[series_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_plus_thm⦎ = save_thm ( "riemann_sum_plus_thm", (
set_goal([], ⌜∀f g t I n⦁
	RiemannSum (λx⦁f x + g x) (t, I, n) =
	RiemannSum f (t, I, n) + RiemannSum g (t, I, n)
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_const_times_thm⦎ = save_thm ( "riemann_sum_const_times_thm", (
set_goal([], ⌜∀f c t I n⦁
	RiemannSum (λx⦁c * f x) (t, I, n) =
	c * RiemannSum f (t, I, n)
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_minus_thm⦎ = save_thm ( "riemann_sum_minus_thm", (
set_goal([], ⌜∀f t I n⦁
	RiemannSum (λx⦁~(f x)) (t, I, n) =
	~ (RiemannSum f (t, I, n))
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_local_thm⦎ = save_thm ( "riemann_sum_local_thm", (
set_goal([], ⌜∀f t I s J n⦁
	(∀m⦁m < n ⇒ t m = s m)
∧	(∀m⦁m ≤ n ⇒ I m = J m)
⇒	RiemannSum f (t, I, n) =
	RiemannSum f (s, J, n)
⌝);
a(REPEAT ∀_tac);
a(induction_tac ⌜n⌝ THEN rewrite_tac[riemann_sum_induction_thm]);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜m' < n + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(REPEAT strip_tac);
a(lemma_tac⌜m' ≤ n + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(spec_nth_asm_tac 2 ⌜n⌝);
a(spec_nth_asm_tac 2 ⌜n⌝);
a(spec_nth_asm_tac 3 ⌜n+1⌝);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_o_minus_thm⦎ = save_thm ( "riemann_sum_o_minus_thm", (
set_goal([], ⌜∀f t I n⦁
	RiemannSum f (t, I, n) =
	RiemannSum (λ x⦁ f (~ x)) ((λm⦁~(t(n - 1 - m))), (λm⦁~(I (n - m))), n)
⌝);
a(REPEAT strip_tac);
a(intro_∀_tac(⌜t⌝, ⌜t⌝) THEN intro_∀_tac(⌜I⌝, ⌜I⌝) 
	THEN induction_tac⌜n⌝
	THEN1 rewrite_tac[riemann_sum_induction_thm]
	THEN REPEAT strip_tac);
a(conv_tac (LEFT_C(rewrite_conv[riemann_sum_induction_thm1])));
a(conv_tac (RIGHT_C(rewrite_conv[riemann_sum_induction_thm])));
a(rewrite_tac[∀_elim⌜I 1⌝ ℝ_plus_order_thm]);
a(POP_ASM_T (fn th => (conv_tac(LEFT_C(rewrite_conv[th])))));
a(bc_thm_tac riemann_sum_local_thm);
a(REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(LEMMA_T⌜m + 1 ≤ n⌝ (strip_asm_tac o rewrite_rule [≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(m+1)+i = (m+i)+1⌝]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(m+i)+1 = (i+1)+m⌝]);
(* *** Goal "2" *** *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule [≤_def]));
a(all_var_elim_asm_tac1);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜m+i = i+m⌝]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(i+m)+1 = (i+1)+m⌝]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_o_times_thm⦎ = save_thm ( "riemann_sum_o_times_thm", (
set_goal([], ⌜∀f t I n c⦁
	¬c = ℕℝ 0
⇒	RiemannSum (λ x⦁ f (c * x)) (t, I, n)  =
	c ⋏-⋏1 * RiemannSum f ((λm⦁c*(t m)), (λm⦁c*(I m)), n)
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜n⌝
	THEN asm_rewrite_tac[riemann_sum_induction_thm,
	ℝ_times_plus_distrib_thm]);
a(rewrite_tac[∀_elim⌜c⌝ ℝ_times_order_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
		⌜∀x⦁~(c * x) = c * ~x⌝]);
a(rewrite_tac[ℝ_times_assoc_thm1]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏partition_reverse_clauses⦎ = save_thm ( "partition_reverse_clauses", (
set_goal([], ⌜∀f t I n G⦁
	((t, I, n) ∈ TaggedPartition ⇒
	((λm⦁~(t(n - 1 - m))), (λm⦁~(I (n - m))), n) ∈ TaggedPartition)
∧	((t, I, n) ∈ G Fine ⇒
	((λm⦁~(t(n - 1 - m))), (λm⦁~(I (n - m))), n) ∈ (λ x⦁ {t|~ t ∈ G (~ x)}) Fine)
⌝);
a(rewrite_tac[tagged_partition_def, fine_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T⌜m + 1 ≤ n⌝ (strip_asm_tac o rewrite_rule [≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1
	THEN rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
		⌜∀x y:ℝ⦁ ~x < ~y ⇔ y < x⌝]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(m+1)+i = (i+1)+m⌝]);
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜m + 1 ≤ n⌝ (strip_asm_tac o rewrite_rule [≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1
	THEN rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(m+1)+i = (i+m)+1⌝]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜ (i+m)+1 = (i+1)+m⌝]);
a(LEMMA_T⌜∀x y z⦁x ∈ ClosedInterval z y ⇔
	~x ∈ ClosedInterval (~y) (~z)⌝ once_rewrite_thm_tac
	THEN1 (rewrite_tac [closed_interval_def]
		THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(rewrite_tac[]);
a(DROP_NTH_ASM_T 2 bc_thm_tac);
a(PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "3" *** *)
a(LEMMA_T⌜m + 1 ≤ n⌝ (strip_asm_tac o rewrite_rule [≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(m+1)+i = (i+m)+1⌝]);
a(rewrite_tac[pc_rule1 "lin_arith" prove_rule[]
	⌜(i+m)+1 = (i+1)+m⌝]);
a(DROP_NTH_ASM_T 2 (ante_tac o ∀_elim⌜i⌝));
a(PC_T1 "sets_ext" rewrite_tac[closed_interval_def,
	pc_rule1 "lin_arith" prove_rule[]
	⌜i < (m + 1) + i⌝,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x j⦁ (~(I j) ≤ x ⇔ ~x ≤ I j) ∧
		(x ≤ ~(I j) ⇔ I j ≤ ~x)⌝]);
a(DROP_ASMS_T discard_tac THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏tagged_partition_append_thm⦎ = save_thm ( "tagged_partition_append_thm", (
set_goal([], ⌜∀s J m t I n⦁
	(s, J, m) ∈ TaggedPartition
∧	(t, I, n) ∈ TaggedPartition
∧	J m = I 0
⇒	((λk⦁ if k < m then s k else t (k - m)),
	 (λk⦁ if k ≤ m then J k else I (k - m)),
	 m + n) ∈ TaggedPartition
⌝);
a(rewrite_tac[tagged_partition_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(cases_tac⌜m' + 1 ≤ m⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a(LEMMA_T ⌜m' ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 7 bc_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(cases_tac⌜m' = m⌝ THEN1 all_var_elim_asm_tac);
(* *** Goal "1.2.1" *** *)
a(asm_rewrite_tac[] THEN all_asm_fc_tac[]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]);
(* *** Goal "1.2.2" *** *)
a(LEMMA_T ⌜¬m' ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜m ≤ m'⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(rewrite_tac[∀_elim⌜i⌝ plus_order_thm]);
a(rewrite_tac[∀_elim⌜m⌝ plus_order_thm]);
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜m' + 1 ≤ m⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a(LEMMA_T ⌜m' < m ∧ m' ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 6 bc_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(cases_tac⌜m' = m⌝ THEN1 all_var_elim_asm_tac);
(* *** Goal "2.2.1" *** *)
a(asm_rewrite_tac[] THEN all_asm_fc_tac[]);
a(DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(LEMMA_T ⌜¬m' < m ∧ ¬m' ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜m ≤ m'⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(rewrite_tac[∀_elim⌜i⌝ plus_order_thm]);
a(rewrite_tac[∀_elim⌜m⌝ plus_order_thm]);
a(all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏fine_append_thm⦎ = save_thm ( "fine_append_thm", (
set_goal([], ⌜∀G s J m t I n⦁
	(s, J, m) ∈ G Fine
∧	(t, I, n) ∈ G Fine
∧	J m = I 0
⇒	((λk⦁ if k < m then s k else t (k - m)),
	 (λk⦁ if k ≤ m then J k else I (k - m)),
	 m + n) ∈ G Fine
⌝);
a(rewrite_tac[fine_def] THEN REPEAT strip_tac);
a(cases_tac⌜m' + 1 ≤ m⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜m' ≤ m ∧ m' < m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 5 bc_thm_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜m' = m⌝ THEN1 all_var_elim_asm_tac);
(* *** Goal "2.1" *** *)
a(asm_rewrite_tac[] THEN all_asm_fc_tac[]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(LEMMA_T ⌜¬m' ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜m ≤ m'⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(rewrite_tac[∀_elim⌜i⌝ plus_order_thm]);
a(rewrite_tac[∀_elim⌜m⌝ plus_order_thm]);
a(all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_0_thm⦎ = save_thm ( "riemann_sum_0_thm", (
set_goal([], ⌜∀t I n⦁
	RiemannSum (λx⦁ℕℝ 0) (t, I, n) = ℕℝ 0
⌝);
a(REPEAT strip_tac);
a(induction_tac⌜n⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_append_thm⦎ = save_thm ( "riemann_sum_append_thm", (
set_goal([], ⌜∀f t I m n⦁
	RiemannSum f (t, I, m + n) =
	RiemannSum f (t, I, m) +
	RiemannSum f ((λk⦁ t(m + k)), (λk⦁I(m + k)), n)
⌝);
a(REPEAT strip_tac);
a(rewrite_tac[riemann_sum_def]);
a(induction_tac ⌜n⌝ THEN1 rewrite_tac[series_def]);
a(asm_rewrite_tac[plus_assoc_thm1, series_def,
	ℝ_plus_assoc_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_¬_0_thm⦎ = save_thm ( "riemann_sum_¬_0_thm", (
set_goal([], ⌜∀f t I n⦁
	¬RiemannSum f (t, I, n) = ℕℝ 0
⇒	∃m⦁	m < n ∧ ¬f(t m) = ℕℝ 0
	∧	RiemannSum f (t, I, n) =
		RiemannSum f (t, I, m+1)
⌝);
a(REPEAT ∀_tac);
a(induction_tac ⌜n⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(∃_tac⌜n⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]);
a(swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜¬f(t n) = ℕℝ 0⌝
	THEN1 (∃_tac⌜n⌝ THEN asm_rewrite_tac[]));
a(∃_tac⌜m'⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏partition_mono_thm⦎ = save_thm ( "partition_mono_thm", (
set_goal([], ⌜∀t I n k m⦁
	(t, I, n) ∈ TaggedPartition
∧	k ≤ m ∧ m < n
⇒	I k < I (m+1) ⌝);
a(rewrite_tac[tagged_partition_def] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[≤_def]));
a(all_var_elim_asm_tac1);
a(POP_ASM_T ante_tac THEN POP_ASM_T discard_tac
	THEN induction_tac⌜i⌝
	THEN1 rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(i_contr_tac THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(DROP_NTH_ASM_T 2 (strip_asm_tac o rewrite_rule[plus_assoc_thm]));
a(all_asm_fc_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏tag_mono_thm⦎ = save_thm ( "tag_mono_thm", (
set_goal([], ⌜∀t I n k m⦁
	(t, I, n) ∈ TaggedPartition
∧	k ≤ m ∧ m < n
⇒	t k ≤ t m⌝);
a(REPEAT_N 5 strip_tac);
a(induction_tac⌜m⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜k = m + 1⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "4" *** *)
a(bc_thm_tac ℝ_≤_trans_thm
	THEN ∃_tac⌜t m⌝ THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o
	rewrite_rule[tagged_partition_def, closed_interval_def]));
a(lemma_tac⌜m < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [2, 3] all_fc_tac);
a(all_fc_tac[ℝ_≤_trans_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏tag_upper_bound_thm⦎ = save_thm ( "tag_upper_bound_thm", (
set_goal([], ⌜∀t I n k m⦁
	(t, I, n) ∈ TaggedPartition
∧	k ≤ m ∧ m < n
⇒	t k ≤ I(m + 1)⌝);
a(REPEAT strip_tac);
a(all_fc_tac[tag_mono_thm]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜t m⌝
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 (fn th => all_fc_tac[rewrite_rule[tagged_partition_def,
	closed_interval_def]th]));
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏tag_lower_bound_thm⦎ = save_thm ( "tag_lower_bound_thm", (
set_goal([], ⌜∀t I n k m⦁
	(t, I, n) ∈ TaggedPartition
∧	k ≤ m ∧ m < n
⇒	I k ≤ t m⌝);
a(REPEAT strip_tac);
a(all_fc_tac[tag_mono_thm]);
a(bc_thm_tac ℝ_≤_trans_thm THEN ∃_tac⌜t k⌝
	THEN REPEAT strip_tac);
a(lemma_tac⌜k < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 5 (fn th => all_fc_tac[rewrite_rule[tagged_partition_def,
	closed_interval_def]th]));
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏subpartition_thm⦎ = save_thm ( "subpartition_thm", (
set_goal([], ⌜∀n m t I⦁
	m ≤ n
∧	(t, I, n) ∈ TaggedPartition
⇒	(t, I, m) ∈ TaggedPartition
⌝);
a(rewrite_tac[tagged_partition_def, closed_interval_def]
 	THEN REPEAT strip_tac
	THEN all_fc_tac[pc_rule1"lin_arith" prove_rule[]
	⌜∀a b c:ℕ⦁a < b ∧ b ≤ c ⇒ a < c⌝] THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏subpartition_fine_thm⦎ = save_thm ( "subpartition_fine_thm", (
set_goal([], ⌜∀n m t I n G⦁
	m ≤ n
∧	(t, I, n) ∈ G Fine
⇒	(t, I, m) ∈ G Fine
⌝);
a(rewrite_tac[fine_def]
 	THEN REPEAT strip_tac
	THEN all_fc_tac[pc_rule1"lin_arith" prove_rule[]
	⌜∀a b c:ℕ⦁a < b ∧ b ≤ c ⇒ a < c⌝] THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_local_thm1⦎ = save_thm ( "riemann_sum_local_thm1", (
set_goal([], ⌜∀f g t I n⦁
	(∀x⦁I 0 ≤ x ∧ x ≤ I n ⇒ f x = g x)
∧	(t, I, n) ∈ TaggedPartition
⇒	RiemannSum f (t, I, n) =
	RiemannSum g (t, I, n)
⌝);
a(REPEAT ∀_tac);
a(induction_tac ⌜n⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]
 	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 3);
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
a(fc_tac[partition_mono_thm]);
a(list_spec_nth_asm_tac 1[⌜n⌝, ⌜n⌝]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 3);
a(bc_thm_tac subpartition_thm
	THEN ∃_tac⌜n+1⌝
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜f(t n) = g(t n)⌝ rewrite_thm_tac);
a(DROP_NTH_ASM_T 2 bc_thm_tac);
a(fc_tac[tag_lower_bound_thm]);
a(list_spec_nth_asm_tac 1[⌜0⌝, ⌜n⌝]);
a(fc_tac[tag_upper_bound_thm]);
a(list_spec_nth_asm_tac 1[⌜n⌝, ⌜n⌝]);
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_0_≤_thm⦎ = save_thm ( "riemann_sum_0_≤_thm", (
set_goal([], ⌜∀f t I n⦁
	(∀x⦁ℕℝ 0 ≤ f x)
∧	(t, I, n) ∈ TaggedPartition
⇒	ℕℝ 0 ≤ RiemannSum f (t, I, n)
⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(induction_tac⌜n⌝ THEN asm_rewrite_tac[riemann_sum_induction_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 2);
a(bc_thm_tac subpartition_thm
	THEN ∃_tac⌜n+1⌝
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜ℕℝ 0 ≤ f (t n) * (I (n + 1) + ~ (I n))⌝
	THEN_LIST [bc_thm_tac ℝ_0_≤_0_≤_times_thm,
		PC_T1 "ℝ_lin_arith" asm_prove_tac[]]
	THEN asm_rewrite_tac[]);
a(lemma_tac⌜I n < I (n + 1)⌝
	THEN_LIST [bc_thm_tac partition_mono_thm,
		PC_T1 "ℝ_lin_arith" asm_prove_tac[]]);
a(∃_tac⌜n+1⌝ THEN ∃_tac⌜t⌝ THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏tag_unique_thm⦎ = save_thm ( "tag_unique_thm", (
set_goal([], ⌜∀t I n k m⦁
	(t, I, n) ∈ TaggedPartition
∧	k < m ∧ m < n ∧ t k = t m
⇒	m = k + 1⌝);
a(contr_tac);
a(lemma_tac⌜k + 1 < m ∧ k < n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(GET_ASM_T ⌜(t, I, n) ∈ TaggedPartition⌝
	(strip_asm_tac o rewrite_rule[tagged_partition_def, closed_interval_def]));
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(LEMMA_T⌜1 ≤ m⌝ (strip_asm_tac o
	once_rewrite_rule[plus_comm_thm] o
	rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(lemma_tac⌜k + 1 ≤ i ∧ i < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_fc_tac[partition_mono_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏partition_cover_thm⦎ = save_thm ( "partition_cover_thm", (
set_goal([], ⌜∀t I n x⦁
	(t, I, n) ∈ TaggedPartition
∧	I 0 < x ∧ x ≤ I n
⇒	∃m⦁ m < n ∧ I m < x ∧ x ≤ I(m+1)⌝);
a(REPEAT_N 4 strip_tac);
a(induction_tac ⌜n⌝ THEN REPEAT strip_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 4);
a(DROP_NTH_ASM_T 3 ante_tac THEN DROP_ASMS_T discard_tac);
a(rewrite_tac[tagged_partition_def]
	THEN REPEAT strip_tac
	THEN (GET_ASMS_T (FIRST o mapfilter bc_thm_tac)
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
(* *** Goal "2" *** *)
a(∃_tac⌜n⌝ THEN rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜m'⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏partition_cover_thm1⦎ = save_thm ( "partition_cover_thm1", (
set_goal([], ⌜∀t I n x⦁
	(t, I, n) ∈ TaggedPartition
∧	I 0 ≤ x ∧ x < I n
⇒	∃m⦁ m < n ∧ I m ≤ x ∧ x < I(m+1)⌝);
a(REPEAT_N 4 strip_tac);
a(induction_tac ⌜n⌝ THEN REPEAT strip_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 4);
a(DROP_NTH_ASM_T 3 ante_tac THEN DROP_ASMS_T discard_tac);
a(rewrite_tac[tagged_partition_def]
	THEN REPEAT strip_tac
	THEN (GET_ASMS_T (FIRST o mapfilter bc_thm_tac)
		THEN PC_T1 "lin_arith" asm_prove_tac[]));
(* *** Goal "2" *** *)
a(∃_tac⌜n⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(∃_tac⌜m'⌝ THEN asm_rewrite_tac[]);
a(PC_T1 "lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏riemann_sum_χ_singleton_thm⦎ = save_thm ( "riemann_sum_χ_singleton_thm", (
set_goal([], ⌜∀c t I n⦁
	(t, I, n) ∈ TaggedPartition
⇒	RiemannSum (χ{c}) (t, I, n) = ℕℝ 0
∨	(∃m⦁m < n ∧ RiemannSum (χ{c}) (t, I, n) = I(m+1) - I(m))
∨	(∃m⦁m + 1 < n ∧ RiemannSum (χ{c}) (t, I, n) = I(m+2) - I(m))
⌝);
a(REPEAT_N 7 strip_tac);
a(all_fc_tac[riemann_sum_¬_0_thm]);
a(rename_tac[] THEN POP_ASM_T rewrite_thm_tac);
a(POP_ASM_T ante_tac THEN rewrite_tac[χ_def]);
a(cases_tac⌜t m = c⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜m = 0⌝ THEN1 all_var_elim_asm_tac1);
(* *** Goal "1" *** *)
a(∨_left_tac THEN ∃_tac⌜0⌝);
a(pure_rewrite_tac[riemann_sum_induction_thm]);
a(asm_rewrite_tac[χ_def]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜1 ≤ m⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(POP_ASM_T ante_tac THEN POP_ASM_T discard_tac);
a(STRIP_T(strip_asm_tac o once_rewrite_rule[plus_comm_thm]));
a(all_var_elim_asm_tac1);
a(rewrite_tac[riemann_sum_induction_thm]);
a(LEMMA_T⌜RiemannSum (χ {t (i + 1)}) (t, I, i) = ℕℝ 0⌝
	rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 2 discard_tac);
a(contr_tac THEN all_fc_tac[riemann_sum_¬_0_thm]);
a(DROP_NTH_ASM_T 2 ante_tac);
a(rewrite_tac[χ_def]);
a(cases_tac⌜t m = t(i+1)⌝ THEN asm_rewrite_tac[]);
a(lemma_tac⌜m < i + 1⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_fc_tac[tag_unique_thm]);
a(all_var_elim_asm_tac1 THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(cases_tac⌜t i = t (i+1)⌝);
(* *** Goal "2.2.1" *** *)
a(∨_right_tac THEN ∃_tac⌜i⌝ 
	THEN asm_rewrite_tac[χ_def, plus_assoc_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(∨_left_tac THEN ∃_tac⌜i+1⌝ 
	THEN asm_rewrite_tac[χ_def, plus_assoc_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_plus_thm⦎ = save_thm ( "int_ℝ_plus_thm", (
set_goal([], ⌜∀f g c d⦁
	f Int⋎R c ∧ g Int⋎R d ⇒ (λx⦁f x + g x) Int⋎R c + d
⌝);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < 1/2 * e⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac);
a(LIST_DROP_NTH_ASM_T [2, 3] all_fc_tac);
a(strip_asm_tac (list_∀_elim[⌜G⌝, ⌜G'⌝] gauge_refinement_thm));
a(strip_asm_tac (list_∀_elim[⌜b⌝, ⌜b'⌝]ℝ_max_2_thm));
a(strip_asm_tac (list_∀_elim[⌜a⌝, ⌜a'⌝]ℝ_min_2_thm));
a(lemma_tac⌜z' < z⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(MAP_EVERY ∃_tac[⌜G''⌝, ⌜z'⌝, ⌜z⌝] THEN REPEAT strip_tac);
a(lemma_tac⌜I 0 < a ∧ I 0 < a' ∧ b < I n ∧ b' < I n⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[fine_refinement_thm]);
a(LIST_DROP_NTH_ASM_T [19, 22] all_fc_tac);
a(REPEAT_N 2 (POP_ASM_T ante_tac));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm]);
a(DROP_ASMS_T discard_tac);
a(rewrite_tac[riemann_sum_plus_thm]);
a(cases_tac⌜ℕℝ 0 ≤
	(RiemannSum f (t, I, n) + RiemannSum g (t, I, n)) + ~ c + ~ d⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_minus_thm⦎ = save_thm ( "int_ℝ_minus_thm", (
set_goal([], ⌜∀f c⦁
	f Int⋎R c ⇒ (λx⦁~(f x)) Int⋎R ~c
⌝);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(MAP_EVERY ∃_tac[⌜G⌝, ⌜a⌝, ⌜b⌝] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(pure_rewrite_tac[riemann_sum_minus_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x⦁~x + c = ~ (x + ~c)⌝,
	ℝ_abs_minus_thm]);
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_0_thm⦎ = save_thm ( "int_ℝ_0_thm", (
set_goal([], ⌜ (λx⦁ℕℝ 0) Int⋎R ℕℝ 0 ⌝);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
a(asm_rewrite_tac[riemann_sum_0_thm]);
a(MAP_EVERY ∃_tac[⌜λx:ℝ⦁(Universe:ℝ SET)⌝, ⌜ℕℝ 0⌝, ⌜ℕℝ 1⌝]);
a(rewrite_tac[gauge_def, empty_universe_open_closed_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_const_times_thm⦎ = save_thm ( "int_ℝ_const_times_thm", (
set_goal([], ⌜∀f c d⦁
	f Int⋎R d ⇒ (λx⦁c*(f x)) Int⋎R c*d
⌝);
a(REPEAT strip_tac THEN cases_tac⌜c = ℕℝ 0⌝
	THEN1 asm_rewrite_tac[int_ℝ_0_thm]);
a(DROP_NTH_ASM_T 2 ante_tac);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
a(all_fc_tac[ℝ_¬_0_abs_thm]);
a(lemma_tac⌜ℕℝ 0 < Abs c ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜ℕℝ 0 < Abs c ⋏-⋏1 * e⌝ 
	THEN1 all_fc_tac[ℝ_0_less_0_less_times_thm]);
a(DROP_NTH_ASM_T 5 (strip_asm_tac o ∀_elim⌜Abs c ⋏-⋏1 * e⌝));
a(MAP_EVERY ∃_tac[⌜G⌝, ⌜a⌝, ⌜b⌝] THEN REPEAT strip_tac);
a(rewrite_tac[riemann_sum_const_times_thm]);
a(rewrite_tac[ℝ_abs_times_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y⦁c * x + ~(c * y) = c*(x + ~y)⌝]);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(lemma_tac⌜¬Abs c = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜e = (Abs c * Abs c ⋏-⋏1) * e⌝ once_rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(rewrite_tac[ℝ_times_assoc_thm]
	THEN bc_thm_tac ℝ_times_mono_thm);
a(REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_diff_0_thm⦎ = save_thm ( "int_ℝ_diff_0_thm", (
set_goal([], ⌜∀f g c⦁
	(λx⦁ f x - g x) Int⋎R ℕℝ 0
⇒	(f Int⋎R c ⇔ g Int⋎R c)
⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[int_ℝ_minus_thm]);
a(EXTEND_PC_T1 "'mmp1" all_fc_tac[int_ℝ_plus_thm]);
a(DROP_NTH_ASM_T 7 ante_tac THEN DROP_ASMS_T discard_tac);
a(rewrite_tac[ℝ_plus_assoc_thm1, η_axiom]);
(* *** Goal "2" *** *)
a(EXTEND_PC_T1 "'mmp1" all_fc_tac[int_ℝ_plus_thm]);
a(POP_ASM_T ante_tac THEN DROP_ASMS_T discard_tac);
a(rewrite_tac[ℝ_plus_assoc_thm, η_axiom]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_unique_thm⦎ = save_thm ( "int_ℝ_unique_thm", (
set_goal([], ⌜∀f c d⦁
	f Int⋎R c ∧ f Int⋎R d ⇒ c = d
⌝);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
a(CASES_T ⌜d + ~c = ℕℝ 0⌝ ante_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(rewrite_tac[ℝ_¬_0_abs_thm] THEN strip_tac THEN i_contr_tac);
a(lemma_tac⌜ℕℝ 0 < 1/2 * (Abs (d + ~ c))⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac);
a(LIST_DROP_NTH_ASM_T [2, 3] all_fc_tac);
a(strip_asm_tac (list_∀_elim[⌜G⌝, ⌜G'⌝] gauge_refinement_thm));
a(strip_asm_tac (list_∀_elim[⌜b⌝, ⌜b'⌝]ℝ_max_2_thm));
a(strip_asm_tac (list_∀_elim[⌜a⌝, ⌜a'⌝]ℝ_min_2_thm));
a(lemma_tac⌜z' ≤ z⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[∀_elim⌜G''⌝ cousin_lemma]);
a(lemma_tac⌜I 0 < a ∧ I 0 < a' ∧ b < I n ∧ b' < I n⌝
	THEN1 (asm_rewrite_tac[] THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[fine_refinement_thm]);
a(LIST_DROP_NTH_ASM_T [19, 22] all_fc_tac);
a(REPEAT_N 2 (POP_ASM_T ante_tac));
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[ℝ_abs_diff_bounded_thm]);
a(DROP_ASMS_T discard_tac);
a(cases_tac⌜ℕℝ 0 ≤ d + ~c⌝
	THEN asm_rewrite_tac[ℝ_abs_def]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_0_≤_thm⦎ = save_thm ( "int_ℝ_0_≤_thm", (
set_goal([], ⌜∀f c⦁
	(∀x⦁ℕℝ 0 ≤ f x) ∧ f Int⋎R c ⇒ ℕℝ 0 ≤ c
⌝);
a(rewrite_tac [int_ℝ_def] THEN contr_tac);
a(lemma_tac ⌜ℕℝ 0 < ~c⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [2,3] all_fc_tac);
a(lemma_tac⌜∃A⦁ A < a⌝ THEN1
	(∃_tac⌜a + ~(ℕℝ 1)⌝ 
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜∃B⦁ b < B ∧ A ≤ B⌝ THEN1
	(∃_tac⌜b + ℕℝ 1⌝ 
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[cousin_lemma]);
a(all_var_elim_asm_tac1);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_abs_≤_less_interval_thm,
	open_interval_def]);
a(all_fc_tac[riemann_sum_0_≤_thm]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_≤_thm⦎ = save_thm ( "int_ℝ_≤_thm", (
set_goal([], ⌜∀f g c d⦁
	(∀x⦁f x ≤ g x)
∧	f Int⋎R c
∧	g Int⋎R d
⇒	c ≤ d
⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜(λx⦁g x + (λz⦁~(f z)) x) Int⋎R d + ~c⌝
	ante_tac
	THEN1 (bc_tac [int_ℝ_plus_thm, int_ℝ_minus_thm]
		THEN REPEAT strip_tac));
a(rewrite_tac[] THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 4 ante_tac);
a(once_rewrite_tac[ℝ_≤_0_≤_thm] THEN REPEAT strip_tac);
a(bc_thm_tac int_ℝ_0_≤_thm);
a(∃_tac⌜(λ x⦁ g x + ~ (f x))⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_0_dominated_thm⦎ = save_thm ( "int_ℝ_0_dominated_thm", (
set_goal([], ⌜∀f g⦁
	(∀x⦁ℕℝ 0 ≤ f x)
∧ 	(∀x⦁f x ≤ g x)
∧	(g Int⋎R ℕℝ 0)
⇒	(f Int⋎R ℕℝ 0)
⌝);
a(rewrite_tac [int_ℝ_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(MAP_EVERY ∃_tac[⌜G⌝, ⌜a⌝, ⌜b⌝] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(POP_ASM_T ante_tac);
a(lemma_tac⌜∀x⦁ℕℝ 0 ≤ g x⌝ THEN1
	(REPEAT strip_tac THEN bc_thm_tac ℝ_≤_trans_thm
		THEN ∃_tac⌜f x⌝ THEN asm_rewrite_tac[]));
a(rewrite_tac[ℝ_abs_def]);
a(ALL_FC_T rewrite_tac[riemann_sum_0_≤_thm]);
a(LEMMA_T⌜g = λx⦁f x + (λz⦁(g z + ~(f z))) x⌝ once_rewrite_thm_tac
	THEN1 (rewrite_tac[] THEN REPEAT strip_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(pure_rewrite_tac[riemann_sum_plus_thm]);
a(LEMMA_T⌜ℕℝ 0 ≤ RiemannSum (λ z⦁ g z + ~ (f z)) (t, I, n)⌝ ante_tac
	THEN_LIST [bc_thm_tac riemann_sum_0_≤_thm,
		PC_T1 "ℝ_lin_arith" prove_tac[]]);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(LEMMA_T⌜f x ≤ g x⌝ ante_tac
	THEN_LIST [asm_rewrite_tac[],
		PC_T1 "ℝ_lin_arith" prove_tac[]]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_χ_singleton_lemma⦎ = save_thm ( "int_ℝ_χ_singleton_lemma", (
set_goal([], ⌜ ∀G e c t I n⦁
	ℕℝ 0 < e
∧	G ∈ Gauge
∧	(∀ t I n m⦁
		m < n
	∧	(t, I, n) ∈ TaggedPartition
	∧	(t, I, n) ∈ G Fine
	⇒	I (m + 1) - I m < e)
∧	(t, I, n) ∈ TaggedPartition
∧	(t, I, n) ∈ G Fine
⇒	Abs(RiemannSum (χ{c}) (t, I, n)) < ℕℝ 2 * e⌝);
a(rewrite_tac[χ_def] THEN REPEAT strip_tac);
a(fc_tac[rewrite_rule[]riemann_sum_χ_singleton_thm]);
a(POP_ASM_T (strip_asm_tac o ∀_elim⌜c⌝)
	THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(lemma_tac⌜I m < I (m+1)⌝
	THEN1 (bc_thm_tac partition_mono_thm
		THEN contr_tac
		THEN all_asm_fc_tac[]
		THEN all_asm_fc_tac[]));
a(rewrite_tac[ℝ_abs_≤_less_interval_thm,
	open_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜m < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [6] all_fc_tac);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[plus_assoc_thm]));
a(LEMMA_T⌜I m < I ((m+1)+1)⌝ ante_tac
	THEN1 (bc_thm_tac partition_mono_thm
		THEN contr_tac
		THEN all_asm_fc_tac[]
		THEN all_asm_fc_tac[]));
a(rewrite_tac[plus_assoc_thm,
	ℝ_abs_≤_less_interval_thm,
	open_interval_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_χ_singleton_thm⦎ = save_thm ( "int_ℝ_χ_singleton_thm", (
set_goal([], ⌜ ∀c⦁ χ {c} Int⋎R ℕℝ 0 ⌝);
a(rewrite_tac[int_ℝ_def, χ_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < 1/2 * e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac);
a(all_fc_tac[rewrite_rule[]riemann_gauge_thm]);
a(MAP_EVERY ∃_tac [⌜G⌝, ⌜x - ℕℝ 1⌝, ⌜x + ℕℝ 1⌝]);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(all_fc_tac[rewrite_rule[]int_ℝ_χ_singleton_lemma]);
a(POP_ASM_T (ante_tac o ∀_elim⌜c⌝));
a(rewrite_tac[ℝ_times_assoc_thm1]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_singleton_support_thm⦎ = save_thm ( "int_ℝ_singleton_support_thm", (
set_goal([], ⌜ ∀f c⦁
	(∀x⦁¬f x = ℕℝ 0 ⇒ x = c)
⇒	f Int⋎R ℕℝ 0 ⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜f = λx⦁f c * χ{c} x⌝ once_rewrite_thm_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN rewrite_tac[χ_def]);
a(cases_tac⌜x = c⌝ THEN asm_rewrite_tac[]);
a(contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜ℕℝ 0 = f c * ℕℝ 0⌝ pure_once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac int_ℝ_const_times_thm);
a(rewrite_tac[int_ℝ_χ_singleton_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_finite_support_thm⦎ = save_thm ( "int_ℝ_finite_support_thm", (
set_goal([], ⌜ ∀f list⦁
	(∀x⦁¬f x = ℕℝ 0 ⇒ x ∈ Elems list)
⇒	f Int⋎R ℕℝ 0 ⌝);
a(REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN intro_∀_tac(⌜f⌝, ⌜f⌝));
a(list_induction_tac ⌜list⌝ THEN rewrite_tac[elems_def]
	THEN REPEAT strip_tac);
a(LEMMA_T ⌜f = λx⦁ℕℝ 0⌝ rewrite_thm_tac
	THEN asm_rewrite_tac[int_ℝ_0_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜f =
	λy⦁ (λy⦁ if y ∈ Elems list ∧ ¬y = x then f y else ℕℝ 0) y
	+ (λy⦁ if y = x then f x else ℕℝ 0) y⌝
	once_rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[] THEN REPEAT strip_tac);
a(cases_tac⌜x' = x⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜x' ∈ Elems list⌝ THEN asm_rewrite_tac[]);
a(contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a(LEMMA_T ⌜ℕℝ 0 = ℕℝ 0 + ℕℝ 0⌝ pure_once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac int_ℝ_plus_thm THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(DROP_NTH_ASM_T 2 bc_thm_tac);
a(∀_tac THEN rewrite_tac[]);
a(cases_tac⌜x' ∈ Elems list⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(bc_thm_tac int_ℝ_singleton_support_thm);
a(∃_tac⌜x⌝);
a(∀_tac THEN rewrite_tac[]);
a(cases_tac⌜x' = x⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏ int_ℝ_χ_0_⊆_thm⦎ = save_thm ( " int_ℝ_χ_0_⊆_thm", (
set_goal([], ⌜ ∀A B⦁ A ⊆ B ∧ χ B Int⋎R ℕℝ 0 ⇒ χ A Int⋎R ℕℝ 0⌝);
a(PC_T1 "sets_ext1" rewrite_tac[]
	THEN REPEAT strip_tac THEN bc_thm_tac int_ℝ_0_dominated_thm);
a(∃_tac⌜χ B⌝ THEN asm_rewrite_tac[χ_def]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(cases_tac⌜x ∈ A⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜x ∈ A⌝ THEN cases_tac⌜x ∈ B⌝
	THEN asm_rewrite_tac[]);
a(all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_χ_0_∩_thm⦎ = save_thm ( "int_ℝ_χ_0_∩_thm", (
set_goal([], ⌜ ∀A B⦁
	χ A Int⋎R ℕℝ 0
⇒	χ (A ∩ B) Int⋎R ℕℝ 0⌝);
a(REPEAT strip_tac THEN bc_thm_tac  int_ℝ_χ_0_⊆_thm);
a(∃_tac⌜A⌝ THEN REPEAT strip_tac THEN PC_T1 "sets_ext1" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏χ_∪_∩_thm⦎ = save_thm ( "χ_∪_∩_thm", (
set_goal([], ⌜
	∀A B x⦁ χ (A ∪ B) x = χ A x + χ B x - χ(A ∩ B) x
⌝);
a(PC_T1 "sets_ext" rewrite_tac[χ_def] THEN REPEAT strip_tac);
a(cases_tac ⌜x ∈ A⌝ THEN cases_tac⌜x ∈ B⌝
	THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_χ_0_∪_thm⦎ = save_thm ( "int_ℝ_χ_0_∪_thm", (
set_goal([], ⌜ ∀A B⦁
	χ A Int⋎R ℕℝ 0 ∧ χ B Int⋎R ℕℝ 0
⇒	χ (A ∪ B) Int⋎R ℕℝ 0⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜χ (A ∩ B) Int⋎R ℕℝ 0⌝ THEN1 ALL_FC_T rewrite_tac[int_ℝ_χ_0_∩_thm]);
a(LEMMA_T ⌜(χ(A ∪ B) = λx⦁χ A x + (λz⦁χ B z + (λu⦁~(χ(A ∩ B)u))z) x) ∧ ℕℝ 0 = ℕℝ 0 + ℕℝ 0⌝ pure_once_rewrite_thm_tac
	THEN1 rewrite_tac[χ_∪_∩_thm]);
a(bc_thm_tac int_ℝ_plus_thm THEN REPEAT strip_tac);
a(LEMMA_T ⌜ℕℝ 0 = ℕℝ 0 + ℕℝ 0⌝ pure_once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac int_ℝ_plus_thm THEN REPEAT strip_tac);
a(LEMMA_T ⌜ℕℝ 0 = ~(ℕℝ 0)⌝ pure_once_rewrite_thm_tac
	THEN1 rewrite_tac[]);
a(bc_thm_tac int_ℝ_minus_thm THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_half_infinite_interval_thm⦎ = save_thm ( "int_half_infinite_interval_thm", (
set_goal([], ⌜ ∀f c a⦁
	(f Int c) {x | a ≤ x}
⇔	(f Int c) {x | a < x}⌝);
a(REPEAT ∀_tac THEN rewrite_tac[int_def]
	THEN bc_thm_tac int_ℝ_diff_0_thm);
a(rewrite_tac[] THEN bc_thm_tac int_ℝ_singleton_support_thm);
a(∃_tac⌜a⌝ THEN ∀_tac
	THEN PC_T1 "sets_ext" rewrite_tac[χ_def, ℝ_≤_def]);
a(cases_tac⌜a = x⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏chosen_value_thm⦎ = save_thm ( "chosen_value_thm", (
set_goal([], ⌜ ∀y f c A⦁
	(f Int c) A
⇔	((λx⦁ if x = y then ℕℝ 0 else f x) Int c) A⌝);
a(rewrite_tac[int_def]);
a(REPEAT ∀_tac THEN bc_thm_tac int_ℝ_diff_0_thm);
a(rewrite_tac[] THEN bc_thm_tac int_ℝ_singleton_support_thm);
a(∃_tac⌜y⌝ THEN ∀_tac
	THEN PC_T1 "sets_ext" rewrite_tac[χ_def]);
a(cases_tac⌜x = y⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_interval_thm⦎ = save_thm ( "int_interval_thm", (
set_goal([], ⌜ ∀f g a b c⦁
	(f Int c) (ClosedInterval a b)
⇔	(f Int c) (OpenInterval a b)⌝);
a(REPEAT ∀_tac THEN rewrite_tac[int_def]
	THEN bc_thm_tac int_ℝ_diff_0_thm);
a(rewrite_tac[] THEN bc_thm_tac int_ℝ_finite_support_thm);
a(∃_tac⌜[a;b]⌝ THEN ∀_tac
	THEN PC_T1 "sets_ext" rewrite_tac[χ_def,
		open_interval_def, closed_interval_def,
		elems_def, ℝ_≤_def]);
a(cases_tac⌜a = x⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜x = b⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f c⦁
	f Int⋎R c ⇒ (λx⦁f(~x)) Int⋎R c
⌝);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(MAP_EVERY ∃_tac[⌜(λ x⦁ {t|~ t ∈ G (~ x)})⌝,
	⌜~b⌝, ⌜~a⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[gauge_o_minus_thm]);
(* *** Goal "2" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac⌜∃s J⦁
	RiemannSum (λ x⦁ f (~ x)) (t, I, n) =
	RiemannSum f (s, J, n)
∧	Abs(RiemannSum f (s, J, n) + ~c) < e⌝
	THEN_LIST [id_tac, asm_rewrite_tac[]]);
a(∃_tac⌜λm⦁~(t(n - 1 - m))⌝
	THEN ∃_tac⌜λm⦁~(I (n - m))⌝
	THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a(conv_tac(LEFT_C (once_rewrite_conv[riemann_sum_o_minus_thm])));
a(rewrite_tac[η_axiom]);
(* *** Goal "3.2" *** *)
a(DROP_NTH_ASM_T 5 bc_thm_tac);
a(ALL_FC_T (MAP_EVERY ante_tac) [partition_reverse_clauses]);
a(rewrite_tac[pc_rule1"sets_ext"prove_rule[]
	⌜∀a⦁{x | x ∈ a} = a⌝, η_axiom]);
a(REPEAT strip_tac);
(* *** Goal "3.2.1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "3.2.2" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ⦏int_ℝ_o_minus_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_o_minus_thm⦎ = save_thm ( "int_ℝ_o_minus_thm", (
set_goal([], ⌜∀f c⦁
	f Int⋎R c ⇔ (λx⦁f(~x)) Int⋎R c
⌝);
a(REPEAT strip_tac THEN all_fc_tac[int_ℝ_o_minus_lemma]);
a(POP_ASM_T ante_tac);
a(rewrite_tac[η_axiom]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f c h⦁
	f Int⋎R c ⇒ (λx⦁f(x + h)) Int⋎R c
⌝);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(MAP_EVERY ∃_tac[⌜(λ x⦁ {t| t + h ∈ G (x + h)})⌝,
	⌜a + ~h⌝, ⌜b + ~h⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[gauge_o_plus_thm]);
(* *** Goal "2" *** *)
a(lemma_tac⌜∃s J⦁
	RiemannSum (λ x⦁ f (x + h)) (t, I, n) =
	RiemannSum f (s, J, n)
∧	Abs(RiemannSum f (s, J, n) + ~c) < e⌝
	THEN_LIST [id_tac, asm_rewrite_tac[]]);
a(∃_tac⌜λm⦁t m + h⌝
	THEN ∃_tac⌜λm⦁I m + h⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_ASMS_T discard_tac THEN induction_tac⌜n⌝
	THEN asm_rewrite_tac[riemann_sum_induction_thm]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 5 bc_thm_tac);
a(DROP_NTH_ASM_T 4 ante_tac);
a(DROP_NTH_ASM_T 1 ante_tac);
a(rewrite_tac[tagged_partition_def, fine_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
(* *** Goal "2.2.2" *** *)
a(DROP_NTH_ASM_T 2 (ante_tac o ∀_elim⌜m⌝) THEN asm_rewrite_tac[closed_interval_def]);
(* *** Goal "2.2.3" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.4" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.5" *** *)
a(DROP_NTH_ASM_T 4 (ante_tac o ∀_elim⌜m⌝)
	THEN PC_T1 "sets_ext" asm_rewrite_tac[closed_interval_def,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀k r⦁ (I k + h ≤ r ⇔ I k ≤ r + ~h)
		∧ (r ≤ I k + h ⇔ r + ~h ≤ I k)⌝]);
a(DROP_ASMS_T discard_tac THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(POP_ASM_T ante_tac THEN rewrite_tac[ℝ_plus_assoc_thm]);
val ⦏int_ℝ_o_plus_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_o_plus_thm⦎ = save_thm ( "int_ℝ_o_plus_thm", (
set_goal([], ⌜∀f c h⦁
	f Int⋎R c ⇔ (λx⦁f(x + h)) Int⋎R c
⌝);
a(REPEAT strip_tac);
 
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[int_ℝ_o_plus_lemma]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜f = λx⦁(λ x⦁ f (x + h))(x + ~h)⌝
	pure_once_rewrite_thm_tac
	THEN1 rewrite_tac[ℝ_plus_assoc_thm]);
a(bc_thm_tac int_ℝ_o_plus_lemma THEN REPEAT strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f c d⦁
	ℕℝ 0 < d
∧	f Int⋎R c
⇒	(λx⦁f(d*x)) Int⋎R d ⋏-⋏1 *c
⌝);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < d * e⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_times_thm]);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜d*e⌝));
a(lemma_tac⌜¬d = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[riemann_sum_o_times_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y z:ℝ⦁ x*y + ~(x*z) = x*(y + ~z)⌝,
	ℝ_abs_times_thm]);
a(lemma_tac⌜ℕℝ 0 < d ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜¬d ⋏-⋏1 = ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[gauge_o_times_thm]);
a(MAP_EVERY ∃_tac[⌜(λ x⦁ {t|d * t ∈ G (d * x)})⌝,
	⌜d ⋏-⋏1 * a⌝, ⌜d ⋏-⋏1 * b⌝]
	THEN REPEAT strip_tac
	THEN1 all_fc_tac[ℝ_times_mono_thm]);
(* *** Goal "2" *** *)
a(LEMMA_T⌜Abs (d ⋏-⋏1) = d ⋏-⋏1⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]);
a(FC_T1 fc_⇔_canon once_rewrite_tac[∀_elim⌜d⌝ ℝ_times_mono_⇔_thm]);
a(rewrite_tac[ℝ_times_assoc_thm1]
	THEN ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(DROP_NTH_ASM_T 10 bc_thm_tac);
a(rewrite_tac[]);
a(FC_T1 fc_⇔_canon once_rewrite_tac[∀_elim⌜d ⋏-⋏1⌝ ℝ_times_mono_⇔_thm]);
a(rewrite_tac[ℝ_times_assoc_thm1]
	THEN ALL_FC_T asm_rewrite_tac[ℝ_recip_clauses]);
a(LIST_DROP_NTH_ASM_T [14, 9, 4, 1] (MAP_EVERY ante_tac)
	THEN DROP_ASMS_T discard_tac
	THEN PC_T1 "sets_ext" rewrite_tac[
		tagged_partition_def,
		fine_def,
		closed_interval_def,
		pc_rule1 "ℝ_lin_arith" prove_rule[]
		⌜∀x y : ℝ⦁x ≤ y ⇔ ¬y < x⌝]);
a(REPEAT_UNTIL (not o is_⇒) strip_tac);
a(FC_T1 fc_⇔_canon asm_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) ℝ_times_mono_⇔_thm]);
a(REPEAT_N 3 strip_tac);
a(LEMMA_T⌜x = d * d ⋏-⋏1 * x⌝ once_rewrite_thm_tac
	THEN1 (rewrite_tac[ℝ_times_assoc_thm1]
		THEN ALL_FC_T rewrite_tac[ℝ_recip_clauses]));
a(FC_T1 fc_⇔_canon asm_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) ℝ_times_mono_⇔_thm]);
a(REPEAT strip_tac THEN all_asm_fc_tac[]);
val ⦏int_ℝ_o_times_lemma1⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_o_times_thm⦎ = save_thm ( "int_ℝ_o_times_thm", (
set_goal([], ⌜∀f c d⦁
	¬ℕℝ 0 = d
∧	f Int⋎R c
⇒	(λx⦁f(d*x)) Int⋎R Abs d ⋏-⋏1 *c
⌝);
a(REPEAT strip_tac);
a(cases_tac⌜ℕℝ 0 < d⌝
	THEN	asm_rewrite_tac[ℝ_abs_def, ℝ_≤_def]
	THEN1 all_fc_tac[int_ℝ_o_times_lemma1]);
a(all_fc_tac[int_ℝ_o_minus_thm]);
a(lemma_tac⌜ℕℝ 0 < ~d⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 4 discard_tac
	THEN all_fc_tac[int_ℝ_o_times_lemma1]);
a(POP_ASM_T ante_tac THEN rewrite_tac[]);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀b f⦁
	(∀x⦁ b ≤ x ⇒ f x = ℕℝ 0)
⇒	∃G1⦁	G1 ∈ Gauge
	∧	∀G2⦁	G2 ∈ Gauge
		∧	(∀x⦁ G2 x ⊆ G1 x)
		⇒	∀ t I n⦁
			(t, I, n) ∈ TaggedPartition
		∧	(t, I, n) ∈ G2 Fine
		∧	I 0 < b ∧ b ≤ I n
		⇒	∃s J m⦁
			(s, J, m + 1) ∈ TaggedPartition
		∧	(s, J, m + 1) ∈ G2 Fine
		∧	RiemannSum f (t, I, n) = RiemannSum f (s, J, (m+1))
		∧	J 0 = I 0 ∧ J(m+1) = b
⌝);
a(REPEAT strip_tac);
a(strip_asm_tac(list_∀_elim[⌜b⌝]
	(rewrite_rule[closed_interval_def] chosen_tag_thm)));
a(∃_tac⌜G1⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(all_fc_tac[partition_cover_thm]);
a(lemma_tac⌜I m ≤ b⌝ THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(LIST_DROP_NTH_ASM_T [11] all_fc_tac
	THEN  all_var_elim_asm_tac1);
a(MAP_EVERY ∃_tac[⌜t⌝, ⌜λk⦁if k ≤ m then I k else t m⌝, ⌜m⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 8 ante_tac
	THEN rewrite_tac[tagged_partition_def,
		closed_interval_def]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(cases_tac⌜m' = m⌝ THEN1 asm_rewrite_tac[]);
a(LEMMA_T ⌜m' ≤ m ∧ m' + 1 ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 4 bc_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(cases_tac⌜m' = m⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac ⌜m' ≤ m ∧ m' < n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "1.3" *** *)
a(cases_tac⌜m' = m⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac ⌜m' + 1 ≤ m ∧ m' < n⌝
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [5] (ALL_FC_T asm_rewrite_tac));
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 7 ante_tac
	THEN rewrite_tac[fine_def]
	THEN REPEAT strip_tac);
a(cases_tac⌜m' = m⌝ THEN1 asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a(all_var_elim_asm_tac1);
a(bc_thm_tac (pc_rule1 "sets_ext" prove_rule[]
	⌜∀a b c⦁a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c⌝)
	THEN ∃_tac⌜ClosedInterval (I m) (I(m+1))⌝);
a(REPEAT strip_tac
	THEN1 (PC_T1 "sets_ext" rewrite_tac[closed_interval_def]
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(LEMMA_T ⌜m' ≤ m ∧ m' + 1 ≤ m⌝ rewrite_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 3 bc_thm_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(LEMMA_T⌜
	RiemannSum f (t, (λ k⦁ if k ≤ m then I k else t m), m + 1) =
	RiemannSum f (t, (λ k⦁ if k ≤ m then I k else t m), m)⌝ rewrite_thm_tac);
(* *** Goal "3.1" *** *)
a(rewrite_tac[riemann_sum_induction_thm]);
a(LEMMA_T⌜f (t m) = ℕℝ 0⌝ rewrite_thm_tac
	THEN DROP_NTH_ASM_T 12 bc_thm_tac
	THEN strip_tac);
(* *** Goal "3.2" *** *)
a(LEMMA_T⌜
	RiemannSum f (t, (λ k⦁ if k ≤ m then I k else t m), m) =
	RiemannSum f (t, I, m)⌝ rewrite_thm_tac);
(* *** Goal "3.2.1" *** *)
a(bc_thm_tac riemann_sum_local_thm);
a(DROP_ASMS_T discard_tac THEN REPEAT strip_tac THEN
	asm_rewrite_tac[]);
(* *** Goal "3.2.2" *** *)
a(LEMMA_T ⌜m ≤ n⌝ (strip_asm_tac o rewrite_rule[≤_def])
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(rewrite_tac[riemann_sum_append_thm]);
a(LEMMA_T⌜∀j⦁ j ≤ i ⇒
	RiemannSum f ((λ k⦁ t (m + k)), (λ k⦁ I (m + k)), j) = ℕℝ 0⌝ (strip_asm_tac o ∀_elim⌜i⌝));
a(strip_tac THEN induction_tac ⌜j:ℕ⌝
	THEN asm_rewrite_tac[riemann_sum_induction_thm]
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac);
a(LEMMA_T ⌜f (t (m + j)) = ℕℝ 0⌝ rewrite_thm_tac);
a(DROP_NTH_ASM_T 14 bc_thm_tac);
a(bc_thm_tac tag_mono_thm);
a(∃_tac⌜m + i⌝ THEN ∃_tac⌜I⌝
	THEN REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "4" *** *)
a(rewrite_tac[]);
(* *** Goal "5" *** *)
a(rewrite_tac[]);
val ⦏support_bounded_above_lemma⦎ = pop_thm();
=TEX
%%%%
%%%% It is marginally shorter and a little more entertaining and instructive to prove the following by symmetry rather than by scissors and paste from the previous proof.
%%%%
=TEX
=SML
set_goal([], ⌜∀G1 G2⦁
	(∀x:ℝ⦁ G2 x ⊆ {t : ℝ |~ t ∈ G1 (~ x)}) ⇔
	(∀y:ℝ⦁ (λz⦁{t|~ t ∈ G2 (~ z)}) y ⊆ G1 y)⌝);
a(PC_T1 "sets_ext" rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ALL_ASM_FC_T (MAP_EVERY ante_tac) [] THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 2 bc_thm_tac THEN asm_rewrite_tac[]);
val ⦏reflect_⊆_lemma⦎ = pop_thm();
=SML
set_goal([], ⌜∀a f⦁
	(∀x⦁ x ≤ a ⇒ f x = ℕℝ 0)
⇒	∃G1⦁	G1 ∈ Gauge
	∧	∀G2⦁	G2 ∈ Gauge
		∧	(∀x⦁ G2 x ⊆ G1 x)
		⇒	∀ t I n⦁
			(t, I, n) ∈ TaggedPartition
		∧	(t, I, n) ∈ G2 Fine
		∧	I 0 ≤ a ∧ a < I n
		⇒	∃s J m⦁
			(s, J, m + 1) ∈ TaggedPartition
		∧	(s, J, m + 1) ∈ G2 Fine
		∧	RiemannSum f (t, I, n) = RiemannSum f (s, J, (m+1))
		∧	J 0 = a ∧ J(m+1) = I n
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∀x⦁ ~a ≤ x ⇒ (λx⦁f(~x))x = ℕℝ 0⌝
	THEN1 (REPEAT strip_tac THEN rewrite_tac[]
		THEN DROP_NTH_ASM_T 2 bc_thm_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[support_bounded_above_lemma]);
a(all_fc_tac[gauge_o_minus_thm]);
a(LIST_DROP_NTH_ASM_T [3, 4, 5] discard_tac);
a(∃_tac⌜(λ x⦁ {t|~ t ∈ G1 (~ x)})⌝
	THEN asm_rewrite_tac[]
	THEN pure_rewrite_tac [reflect_⊆_lemma]
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 7 discard_tac THEN all_fc_tac[gauge_o_minus_thm]);
a(lemma_tac⌜(λ m⦁ ~ (I (n - m))) 0 < ~a
	∧ ~a ≤ (λ m⦁ ~ (I (n - m))) n⌝
	THEN1 (rewrite_tac[] THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac [partition_reverse_clauses]);
a(LIST_DROP_NTH_ASM_T [12] all_fc_tac);
a(LIST_DROP_NTH_ASM_T (interval 6 16) discard_tac);
a(MAP_EVERY ∃_tac[⌜(λ k⦁ ~ (s (m - k)))⌝,
	⌜(λ k⦁ ~ (J ((m + 1) - k)))⌝, ⌜m⌝]);
a(asm_rewrite_tac[]);
a(ALL_FC_T (MAP_EVERY ante_tac) [partition_reverse_clauses]);
a(rewrite_tac[pc_rule1 "sets_ext" prove_rule[]
	⌜∀a⦁{x | x ∈ a} = a⌝, η_axiom]);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 5 ante_tac THEN DROP_ASMS_T discard_tac);
a(rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) riemann_sum_o_minus_thm]);
a(STRIP_T rewrite_thm_tac);
a(conv_tac(LEFT_C (once_rewrite_conv[riemann_sum_o_minus_thm])));
a(rewrite_tac[η_axiom]);
val ⦏support_bounded_below_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀a b f⦁
	a < b
∧	(∀x⦁x ≤ a ⇒ f x = ℕℝ 0)
∧	(∀x⦁b ≤ x ⇒ f x = ℕℝ 0)
⇒	∃G1⦁
	G1 ∈ Gauge
∧	∀ G2⦁ 	G2 ∈ Gauge
	∧	(∀x⦁ G2 x ⊆ G1 x)
	⇒	∀ t I n⦁
		(t, I, n) ∈ TaggedPartition
	∧	(t, I, n) ∈ G2 Fine
	∧	I 0 < a ∧ b < I n
	⇒	∃s J m⦁
			(s, J, m + 1) ∈ TaggedPartition
		∧	(s, J, m + 1) ∈ G2 Fine
		∧	RiemannSum f (t, I, n) = RiemannSum f (s, J, (m+1))
		∧	J 0 = a ∧ J(m+1) = b
⌝);
a(REPEAT strip_tac);
a(all_fc_tac[support_bounded_above_lemma]);
a(all_fc_tac[support_bounded_below_lemma]);
a(strip_asm_tac (list_∀_elim[⌜G1⌝, ⌜G1'⌝] gauge_refinement_thm));
a(∃_tac⌜G⌝ THEN REPEAT strip_tac);
a(all_fc_tac[pc_rule1 "sets_ext" prove_rule[]
		⌜∀a b c⦁(∀x⦁a x ⊆ b x) ∧ (∀x⦁b x ⊆ c x) ⇒ (∀x⦁a x ⊆ c x)⌝]);
a(lemma_tac⌜I 0 ≤ a ∧ a < I n⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [14] all_fc_tac);
a(lemma_tac⌜J 0 < b ∧ b ≤ J (m+1)⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [22] all_fc_tac);
a(MAP_EVERY ∃_tac[⌜s'⌝, ⌜J'⌝, ⌜m'⌝] THEN asm_rewrite_tac[]);
val ⦏bounded_support_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_support_bounded_below_thm⦎ = save_thm ( "int_ℝ_support_bounded_below_thm", (
set_goal([], ⌜∀a c f⦁
	(∀x⦁x ≤ a ⇒ f x = ℕℝ 0)
⇒	(	(f Int⋎R c)
	⇔	∀e⦁ ℕℝ 0 < e ⇒
		∃G b⦁ G ∈ Gauge ∧ a < b ∧
		∀t I n⦁	(t, I, n) ∈ TaggedPartition
		∧	I 0 = a ∧ b < I n
		∧	(t, I, n) ∈ G Fine
		⇒	Abs(RiemannSum f (t, I, n) - c) < e)
⌝);
a(rewrite_tac[int_ℝ_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(strip_asm_tac(list_∀_elim[⌜a⌝, ⌜b⌝]ℝ_max_2_thm));
a(∃_tac⌜G⌝ THEN ∃_tac⌜z⌝ THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(lemma_tac⌜¬n = 0⌝
	THEN1 (contr_tac
		THEN all_var_elim_asm_tac1
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜b < I n⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜I 0 < a'⌝ THEN1 all_asm_fc_tac[]);
a(lemma_tac⌜∃c⦁ c < a' ∧ c ≤ I 0⌝
	THEN1 (∃_tac⌜a' - ℕℝ 1⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[cousin_lemma]);
a(all_fc_tac[tagged_partition_append_thm]);
a(all_fc_tac[fine_append_thm]);
a(lemma_tac⌜
	(λ k⦁ if k ≤ n' then I' k else I (k - n')) 0 < a'
∧	b < (λ k⦁ if k ≤ n' then I' k else I (k - n')) (n' + n)⌝
	THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [19] all_fc_tac);
a(POP_ASM_T ante_tac);
a(LEMMA_T⌜∀x y⦁ x = y ⇒ Abs x < e ⇒ Abs y < e⌝ bc_thm_tac
	THEN1 (REPEAT ∀_tac THEN ⇒_tac THEN asm_rewrite_tac[]));
a(rewrite_tac[riemann_sum_append_thm]);
a(LEMMA_T⌜∀x y z⦁ x = y ∧ z = ℕℝ 0 ⇒ z + x = y⌝ bc_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(bc_thm_tac riemann_sum_local_thm);
a(rewrite_tac[η_axiom]
	THEN REPEAT strip_tac);
a(cases_tac⌜m = 0⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(contr_tac THEN all_fc_tac[riemann_sum_¬_0_thm]);
a(POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a(asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 24 bc_thm_tac);
a(LEMMA_T⌜1 ≤ n'⌝ (strip_asm_tac o once_rewrite_rule[plus_comm_thm] o
		rewrite_rule[≤_def])
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "lin_arith" prove_tac[]));
a(all_var_elim_asm_tac1);
a(lemma_tac ⌜m ≤ i⌝
 	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "lin_arith" prove_tac[]));
a(ante_tac(list_∀_elim[⌜t'⌝, ⌜I'⌝, ⌜i+1⌝, ⌜m⌝, ⌜i⌝]tag_upper_bound_thm));
a(asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(all_fc_tac[support_bounded_below_lemma]);
a(strip_asm_tac (list_∀_elim[⌜G⌝, ⌜G1⌝] gauge_refinement_thm));
a(MAP_EVERY ∃_tac[⌜G'⌝, ⌜a⌝, ⌜b⌝] THEN REPEAT strip_tac);
a(lemma_tac⌜I 0 ≤ a ∧ a < I n⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T [10] all_fc_tac);
a(asm_rewrite_tac[]);
a(lemma_tac⌜(s, J, m + 1) ∈ G Fine⌝
	THEN1 all_fc_tac[fine_refinement_thm]);
a(lemma_tac⌜b < J(m+1)⌝ THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [18] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀a f g c⦁
	(∀x⦁ a < x ⇒ f x = g x)
∧	(∀e⦁ ℕℝ 0 < e ⇒
	∃G b⦁ G ∈ Gauge ∧ a < b ∧
	∀t I n⦁	(t, I, n) ∈ TaggedPartition
	∧	I 0 = a ∧ b < I n
	∧	(t, I, n) ∈ G Fine
	⇒	Abs(RiemannSum f (t, I, n) - c) < e)
⇒	(∀e⦁ ℕℝ 0 < e ⇒
	∃G b⦁ G ∈ Gauge ∧ a < b ∧
	∀t I n⦁	(t, I, n) ∈ TaggedPartition
	∧	I 0 = a ∧ b < I n
	∧	(t, I, n) ∈ G Fine
	⇒	Abs(RiemannSum g (t, I, n) - c) < e)
⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(LEMMA_T ⌜g = λy⦁f y + (λ x⦁ if a < x then ℕℝ 0 else g x  + ~(f x)) y⌝
	once_rewrite_thm_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN cases_tac⌜a < x⌝
	THEN ALL_ASM_FC_T asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜ℕℝ 0 < 1/4 * e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac
	THEN LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(strip_asm_tac (list_∀_elim[⌜Abs(g a + ~(f a))⌝, ⌜ℕℝ 0⌝] ℝ_max_2_thm));
a(strip_asm_tac(∀_elim⌜z⌝ℝ_0_less_0_less_recip_thm));
a(strip_asm_tac (list_∀_elim[⌜1/4 * e⌝, ⌜z ⋏-⋏1⌝] ℝ_0_less_0_less_times_thm));
a(strip_asm_tac(∀_elim⌜(1/4 * e) * z ⋏-⋏1⌝(rewrite_rule[]riemann_gauge_thm)));
a(strip_asm_tac (list_∀_elim[⌜G⌝, ⌜G'⌝] gauge_refinement_thm));
a(∃_tac⌜G''⌝ THEN ∃_tac⌜b⌝ THEN REPEAT strip_tac);
a(pure_rewrite_tac[riemann_sum_plus_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y z:ℝ⦁(x + y) + ~z = (x + ~z) + y⌝]);
a(bc_thm_tac(pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y:ℝ⦁ℕℝ 0 < 1/4*e ∧ Abs (x + y) ≤ Abs x + Abs y ∧ Abs x < 1/4*e ∧ Abs y < 1/2*e ⇒ Abs(x + y) < e⌝)
	THEN rewrite_tac[ℝ_abs_plus_thm]);
a(REPEAT strip_tac
	THEN1 DROP_NTH_ASM_T 14 bc_thm_tac
	THEN REPEAT strip_tac
	THEN1 all_fc_tac[fine_refinement_thm]);
a(LEMMA_T ⌜RiemannSum (λ x⦁ if a < x then ℕℝ 0 else g x + ~(f x)) (t, I, n) =
	RiemannSum (λ x⦁ (g a + ~(f a)) * χ {a} x) (t, I, n)⌝
	rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac(riemann_sum_local_thm1)
	THEN asm_rewrite_tac[ℝ_≤_def]
	THEN DROP_ASMS_T discard_tac
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[χ_def]);
(* *** Goal "2.1.1" *** *)
a(LEMMA_T⌜¬x = a⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(all_var_elim_asm_tac1
	THEN LEMMA_T⌜¬I n = a⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(rewrite_tac [riemann_sum_const_times_thm,
	ℝ_abs_times_thm]);
a(cases_tac⌜Abs(RiemannSum (χ {a}) (t, I, n)) = ℕℝ 0⌝
	THEN1 (asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(strip_asm_tac(∀_elim⌜RiemannSum (χ {a}) (t, I, n)⌝ ℝ_0_≤_abs_thm));
a(lemma_tac⌜ℕℝ 0 < Abs(RiemannSum (χ {a}) (t, I, n))⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_less_trans_thm
	THEN ∃_tac⌜z * Abs(RiemannSum (χ {a}) (t, I, n))⌝);
a(ALL_FC_T rewrite_tac[
	once_rewrite_rule[ℝ_times_comm_thm] ℝ_times_mono_thm]);
a(bc_thm_tac ℝ_less_≤_trans_thm
	THEN ∃_tac⌜(z * z ⋏-⋏1) * 1/2 * e⌝);
a(lemma_tac⌜¬z = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(conv_tac(LEFT_C(rewrite_conv[ℝ_times_assoc_thm])));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜z ⋏-⋏1 * 1 / 2 * e = ℕℝ 2 * ((1 / 4 * e) * z ⋏-⋏1)⌝]);
a(bc_thm_tac int_ℝ_χ_singleton_lemma);
a(∃_tac⌜G'⌝);
a(rename_tac[] THEN ALL_FC_T asm_rewrite_tac[ℝ_0_less_0_less_times_thm,
	fine_refinement_thm]);
val ⦏int_support_bounded_below_lemma_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏int_support_bounded_below_lemma⦎ = save_thm ( "int_support_bounded_below_lemma", (
set_goal([], ⌜∀a f g c⦁
	(∀x⦁ a < x ⇒ f x = g x)
⇒		((∀e⦁ ℕℝ 0 < e ⇒
		∃G b⦁ G ∈ Gauge ∧ a < b ∧
		∀t I n⦁	(t, I, n) ∈ TaggedPartition
		∧	I 0 = a ∧ b < I n
		∧	(t, I, n) ∈ G Fine
		⇒	Abs(RiemannSum f (t, I, n) - c) < e)
⇔		(∀e⦁ ℕℝ 0 < e ⇒
		∃G b⦁ G ∈ Gauge ∧ a < b ∧
		∀t I n⦁	(t, I, n) ∈ TaggedPartition
		∧	I 0 = a ∧ b < I n
		∧	(t, I, n) ∈ G Fine
		⇒	Abs(RiemannSum g (t, I, n) - c) < e))
⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[rewrite_rule[] int_support_bounded_below_lemma_lemma]);
a(∃_tac⌜G⌝ THEN ∃_tac⌜b⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 3 (strip_asm_tac o conv_rule (ONCE_MAP_C eq_sym_conv)));
a(all_fc_tac[rewrite_rule[] int_support_bounded_below_lemma_lemma]);
a(∃_tac⌜G⌝ THEN ∃_tac⌜b⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_bounded_below_thm⦎ = save_thm ( "int_bounded_below_thm", (
set_goal([], ⌜∀a b c f⦁
	(f Int c) {x | a ≤ x}
⇔	∀e⦁ ℕℝ 0 < e ⇒
	∃G b⦁ G ∈ Gauge ∧ a < b ∧
	∀t I n⦁	(t, I, n) ∈ TaggedPartition
	∧	I 0 = a ∧ b < I n
	∧	(t, I, n) ∈ G Fine
	⇒	Abs(RiemannSum f (t, I, n) - c) < e
⌝);
a(rewrite_tac[int_half_infinite_interval_thm]);
a(rewrite_tac[int_def] THEN REPEAT ∀_tac);
a(lemma_tac⌜∀ x⦁ x ≤ a ⇒ χ {x|a < x} x * f x = ℕℝ 0⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN rewrite_tac[χ_def]);
a(LEMMA_T⌜¬a < x⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(FC_T1 fc_⇔_canon rewrite_tac [rewrite_rule[]
	(list_∀_elim[⌜a⌝, ⌜c⌝, ⌜λ x⦁ χ {x|a < x} x * f x⌝] int_ℝ_support_bounded_below_thm)]);
a(lemma_tac⌜∀x⦁a < x ⇒ (λ x⦁ χ {x|a < x} x * f x) x = f x⌝
	THEN1 (rewrite_tac[χ_def]
		THEN REPEAT strip_tac
		THEN asm_rewrite_tac[]));
a(FC_T1 fc_⇔_canon  rewrite_tac[rewrite_rule[]
	int_support_bounded_below_lemma]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_bounded_support_thm⦎ = save_thm ( "int_ℝ_bounded_support_thm", (
set_goal([], ⌜∀a b c f⦁
	a < b
∧	(∀x⦁x ≤ a ⇒ f x = ℕℝ 0)
∧	(∀x⦁b ≤ x ⇒ f x = ℕℝ 0)
⇒	(	(f Int⋎R c)
	⇔	∀e⦁ ℕℝ 0 < e ⇒
		∃G⦁ G ∈ Gauge ∧
		∀t I n⦁	(t, I, n) ∈ TaggedPartition
		∧	I 0 = a ∧ I n = b
		∧	(t, I, n) ∈ G Fine
		⇒	Abs(RiemannSum f (t, I, n) - c) < e)
⌝);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 2 ante_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[int_ℝ_support_bounded_below_thm]);
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [1] all_fc_tac);
a(∃_tac⌜G⌝ THEN REPEAT strip_tac);
a(all_var_elim_asm_tac1);
a(lemma_tac⌜¬n = 0⌝
	THEN1 (contr_tac
		THEN all_var_elim_asm_tac1));
a(cases_tac⌜b' < I n⌝ THEN1 
	(LEMMA_T ⌜I 0 = I 0⌝ asm_tac THEN1 strip_tac
		THEN all_asm_fc_tac[]));
a(lemma_tac⌜∃c⦁ b' < c ∧ I n ≤ c⌝
	THEN1 (∃_tac⌜b' + ℕℝ 1⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[cousin_lemma]);
a(DROP_NTH_ASM_T 4 (strip_asm_tac o eq_sym_rule));
a(all_fc_tac[tagged_partition_append_thm]);
a(all_fc_tac[fine_append_thm]);
a(lemma_tac⌜¬n' = 0⌝
	THEN1 (contr_tac
		THEN all_var_elim_asm_tac1
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜
	(λ k⦁ if k ≤ n then I k else I' (k - n)) 0 = I 0
∧	b' < (λ k⦁ if k ≤ n then I k else I' (k - n)) (n + n')⌝
	THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [16] all_fc_tac);
a(POP_ASM_T ante_tac);
a(LEMMA_T⌜∀x y⦁ x = y ⇒ Abs x < e ⇒ Abs y < e⌝ bc_thm_tac
	THEN1 (REPEAT ∀_tac THEN ⇒_tac THEN asm_rewrite_tac[]));
a(rewrite_tac[riemann_sum_append_thm]);
a(LEMMA_T⌜∀x y z⦁ x = y ∧ z = ℕℝ 0 ⇒ x + z = y⌝ bc_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(bc_thm_tac riemann_sum_local_thm);
a(rewrite_tac[] THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a(contr_tac THEN all_fc_tac[riemann_sum_¬_0_thm]);
a(POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a(asm_rewrite_tac[]);
a(DROP_NTH_ASM_T 21 bc_thm_tac);
a(asm_rewrite_tac[]);
a(bc_thm_tac tag_lower_bound_thm);
a(∃_tac⌜n'⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(POP_ASM_T ante_tac 
	THEN rewrite_tac[int_ℝ_def]
	THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(all_fc_tac[bounded_support_lemma]);
a(strip_asm_tac (list_∀_elim[⌜G⌝, ⌜G1⌝] gauge_refinement_thm));
a(MAP_EVERY ∃_tac[⌜G'⌝, ⌜a⌝, ⌜b⌝] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [8] all_fc_tac);
a(asm_rewrite_tac[]);
a(lemma_tac⌜(s, J, m + 1) ∈ G Fine⌝
	THEN1 all_fc_tac[fine_refinement_thm]);
a(LIST_DROP_NTH_ASM_T [15] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML


val ⦏int_bounded_support_lemma_lemma⦎ = (* save_thm *) snd (
	"int_bounded_support_lemma_lemma", (
set_goal([], ⌜∀a b f g⦁
	a < b
∧	(∀x⦁ a < x ∧ x < b ⇒ f x = g x)
∧	(∀e⦁ ℕℝ 0 < e ⇒
	∃G⦁ G ∈ Gauge ∧
	∀t I n⦁	(t, I, n) ∈ TaggedPartition
	∧	I 0 = a ∧ I n = b
	∧	(t, I, n) ∈ G Fine
	⇒	Abs(RiemannSum f (t, I, n) - c) < e)
⇒	(∀e⦁ ℕℝ 0 < e ⇒
	∃G⦁ G ∈ Gauge ∧
	∀t I n⦁	(t, I, n) ∈ TaggedPartition
	∧	I 0 = a ∧ I n = b
	∧	(t, I, n) ∈ G Fine
	⇒	Abs(RiemannSum g (t, I, n) - c) < e)
⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(LEMMA_T ⌜g = λy⦁f y + (λ x⦁ if a < x ∧ x < b then ℕℝ 0 else g x  + ~(f x)) y⌝
	once_rewrite_thm_tac);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN cases_tac⌜a < x⌝
	THEN cases_tac ⌜x < b⌝
	THEN ALL_ASM_FC_T asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜ℕℝ 0 < 1/8 * e⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 2 discard_tac
	THEN LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(strip_asm_tac (list_∀_elim[⌜Abs(g a + ~(f a))⌝, ⌜Abs(g b + ~(f b))⌝, ⌜ℕℝ 0⌝] ℝ_max_3_thm)
	THEN rename_tac[(⌜t:ℝ⌝, "z")]);
a(strip_asm_tac(∀_elim⌜z⌝ℝ_0_less_0_less_recip_thm));
a(strip_asm_tac (list_∀_elim[⌜1/8 * e⌝, ⌜z ⋏-⋏1⌝] ℝ_0_less_0_less_times_thm));
a(strip_asm_tac(∀_elim⌜(1/8 * e) * z ⋏-⋏1⌝(rewrite_rule[]riemann_gauge_thm)));
a(strip_asm_tac (list_∀_elim[⌜G⌝, ⌜G'⌝] gauge_refinement_thm));
a(∃_tac⌜G''⌝ THEN REPEAT strip_tac);
a(pure_rewrite_tac[riemann_sum_plus_thm]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y z:ℝ⦁(x + y) + ~z = (x + ~z) + y⌝]);
a(bc_thm_tac(pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y:ℝ⦁ℕℝ 0 < 1/8*e ∧ Abs (x + y) ≤ Abs x + Abs y ∧ Abs x < 1/8*e ∧ Abs y < 1/2*e ⇒ Abs(x + y) < e⌝)
	THEN rewrite_tac[ℝ_abs_plus_thm]);
a(REPEAT strip_tac
	THEN1 DROP_NTH_ASM_T 15 bc_thm_tac
	THEN1 REPEAT strip_tac
	THEN1 all_fc_tac[fine_refinement_thm]);
a(LEMMA_T ⌜RiemannSum (λ x⦁ if a < x ∧ x < b then ℕℝ 0 else g x + ~(f x)) (t, I, n) =
	RiemannSum (λ x⦁ (g a + ~(f a)) * χ {a} x + (g b + ~(f b)) * χ {b} x) (t, I, n)⌝
	rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(bc_thm_tac(riemann_sum_local_thm1)
	THEN asm_rewrite_tac[ℝ_≤_def]
	THEN DROP_NTH_ASM_T 19 ante_tac
	THEN DROP_ASMS_T discard_tac
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[χ_def]);
(* *** Goal "2.1.1" *** *)
a(LEMMA_T⌜¬x = a ∧ ¬x = b⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.2" *** *)
a(all_var_elim_asm_tac1
	THEN LEMMA_T⌜¬b = a⌝ asm_rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.3" *** *)
a(all_var_elim_asm_tac1
	THEN LEMMA_T⌜¬x = b⌝ asm_rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.4" *** *)
a(all_var_elim_asm_tac1
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(EXTEND_PC_T1 "'sho_rw" pure_rewrite_tac [riemann_sum_plus_thm,
	riemann_sum_const_times_thm]);
a(bc_thm_tac(pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y:ℝ⦁ℕℝ 0 < 1/8*e ∧ Abs (x + y) ≤ Abs x + Abs y ∧ Abs x < 1/4*e ∧ Abs y < 1/4*e ⇒ Abs(x + y) < 1/2 * e⌝)
	THEN asm_rewrite_tac[ℝ_abs_plus_thm, ℝ_abs_times_thm]);
a(REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(cases_tac⌜Abs(RiemannSum (χ {a}) (t, I, n)) = ℕℝ 0⌝
	THEN1 (asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(strip_asm_tac(∀_elim⌜RiemannSum (χ {a}) (t, I, n)⌝ ℝ_0_≤_abs_thm));
a(lemma_tac⌜ℕℝ 0 < Abs(RiemannSum (χ {a}) (t, I, n))⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_less_trans_thm
	THEN ∃_tac⌜z * Abs(RiemannSum (χ {a}) (t, I, n))⌝);
a(ALL_FC_T rewrite_tac[
	once_rewrite_rule[ℝ_times_comm_thm] ℝ_times_mono_thm]);
a(bc_thm_tac ℝ_less_≤_trans_thm
	THEN ∃_tac⌜(z * z ⋏-⋏1) * 1/4 * e⌝);
a(lemma_tac⌜¬z = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(conv_tac(LEFT_C(rewrite_conv[ℝ_times_assoc_thm])));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜z ⋏-⋏1 * 1 / 4 * e = ℕℝ 2 * ((1 / 8 * e) * z ⋏-⋏1)⌝]);
a(bc_thm_tac int_ℝ_χ_singleton_lemma);
a(∃_tac⌜G'⌝);
a(rename_tac[] THEN ALL_FC_T asm_rewrite_tac[ℝ_0_less_0_less_times_thm,
	fine_refinement_thm]);
(* *** Goal "2.2.2" *** *)
a(cases_tac⌜Abs(RiemannSum (χ {b}) (t, I, n)) = ℕℝ 0⌝
	THEN1 (asm_rewrite_tac[] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(strip_asm_tac(∀_elim⌜RiemannSum (χ {b}) (t, I, n)⌝ ℝ_0_≤_abs_thm));
a(lemma_tac⌜ℕℝ 0 < Abs(RiemannSum (χ {b}) (t, I, n))⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(bc_thm_tac ℝ_less_trans_thm
	THEN ∃_tac⌜z * Abs(RiemannSum (χ {b}) (t, I, n))⌝);
a(ALL_FC_T rewrite_tac[
	once_rewrite_rule[ℝ_times_comm_thm] ℝ_times_mono_thm]);
a(bc_thm_tac ℝ_less_≤_trans_thm
	THEN ∃_tac⌜(z * z ⋏-⋏1) * 1/4 * e⌝);
a(lemma_tac⌜¬z = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(conv_tac(LEFT_C(rewrite_conv[ℝ_times_assoc_thm])));
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜z ⋏-⋏1 * 1 / 4 * e = ℕℝ 2 * ((1 / 8 * e) * z ⋏-⋏1)⌝]);
a(bc_thm_tac int_ℝ_χ_singleton_lemma);
a(∃_tac⌜G'⌝);
a(rename_tac[] THEN ALL_FC_T asm_rewrite_tac[ℝ_0_less_0_less_times_thm,
	fine_refinement_thm]);
pop_thm()
));


=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀a b f g⦁
	a < b
∧	(∀x⦁ a < x ∧ x < b ⇒ f x = g x)
⇒		((∀e⦁ ℕℝ 0 < e ⇒
		∃G⦁ G ∈ Gauge ∧
		∀t I n⦁	(t, I, n) ∈ TaggedPartition
		∧	I 0 = a ∧ I n = b
		∧	(t, I, n) ∈ G Fine
		⇒	Abs(RiemannSum f (t, I, n) - c) < e)
⇔		(∀e⦁ ℕℝ 0 < e ⇒
		∃G⦁ G ∈ Gauge ∧
		∀t I n⦁	(t, I, n) ∈ TaggedPartition
		∧	I 0 = a ∧ I n = b
		∧	(t, I, n) ∈ G Fine
		⇒	Abs(RiemannSum g (t, I, n) - c) < e))
⌝);
a(rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_fc_tac[rewrite_rule[] int_bounded_support_lemma_lemma]);
a(∃_tac⌜G⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(DROP_NTH_ASM_T 3 (strip_asm_tac o conv_rule (ONCE_MAP_C eq_sym_conv)));
a(all_fc_tac[rewrite_rule[] int_bounded_support_lemma_lemma]);
a(∃_tac⌜G⌝ THEN asm_rewrite_tac[]);
val ⦏int_bounded_support_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏bounded_int_thm⦎ = save_thm ( "bounded_int_thm", (
set_goal([], ⌜∀a b c f⦁
	a < b
⇒	((f Int c) (ClosedInterval a b)
⇔	∀e⦁ ℕℝ 0 < e ⇒
	∃G⦁ G ∈ Gauge ∧
	∀t I n⦁	(t, I, n) ∈ TaggedPartition
	∧	I 0 = a ∧ I n = b
	∧	(t, I, n) ∈ G Fine
	⇒	Abs(RiemannSum f (t, I, n) - c) < e)
⌝);
a(rewrite_tac[int_interval_thm]);
a(rewrite_tac[int_def, open_interval_def] THEN REPEAT ∀_tac THEN ⇒_tac);
a(lemma_tac⌜
	(∀ x⦁ x ≤ a ⇒ χ {t|a < t ∧ t < b} x * f x = ℕℝ 0)
∧	(∀ x⦁ b ≤ x ⇒ χ {t|a < t ∧ t < b} x * f x = ℕℝ 0)⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac THEN rewrite_tac[χ_def]);
(* *** Goal "1.1" *** *)
a(LEMMA_T⌜¬a < x⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(LEMMA_T⌜¬x < b⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(ante_tac(rewrite_rule[]
	(list_∀_elim[⌜a⌝, ⌜b⌝, ⌜c⌝, ⌜λ x⦁ χ {t|a < t ∧ t < b} x * f x⌝] int_ℝ_bounded_support_thm)));
a(asm_rewrite_tac[]);
a(STRIP_T rewrite_thm_tac);
a(lemma_tac⌜∀x⦁a < x ∧ x < b ⇒ (λ x⦁ χ {t|a < t ∧ t < b} x * f x) x = f x⌝
	THEN1 (rewrite_tac[χ_def]
		THEN REPEAT strip_tac
		THEN asm_rewrite_tac[]));
a(ALL_FC_T1 fc_⇔_canon  rewrite_tac[rewrite_rule[]
	int_bounded_support_lemma]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀a b f g c⦁
	a < b
∧	(∀x⦁x ∈ ClosedInterval a b ⇒ f x = g x)
∧	(g Int c) (ClosedInterval a b)
⇒	 (f Int c) (ClosedInterval a b)
⌝);
a(REPEAT strip_tac THEN POP_ASM_T ante_tac);
a(FC_T1 fc_⇔_canon rewrite_tac[bounded_int_thm]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[closed_interval_def]));
a(REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜G⌝ THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [5] all_fc_tac);
a(all_var_elim_asm_tac1);
a(ALL_FC_T asm_rewrite_tac[riemann_sum_local_thm1]);
val ⦏bounded_int_local_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏bounded_int_local_thm⦎ = save_thm ( "bounded_int_local_thm", (
set_goal([], ⌜∀a b f g c⦁
	a < b
∧	(∀x⦁x ∈ ClosedInterval a b ⇒ f x = g x)
⇒	((g Int c) (ClosedInterval a b)
⇔	 (f Int c) (ClosedInterval a b))
⌝);
a(REPEAT strip_tac THEN all_fc_tac[bounded_int_local_lemma]);
a(DROP_NTH_ASM_T 2 (strip_asm_tac o conv_rule (ONCE_MAP_C eq_sym_conv)));
a(all_fc_tac[bounded_int_local_lemma]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜ ∀f df x e⦁ 
	(f Deriv df x) x
∧	ℕℝ 0 < e
⇒	∃d⦁ℕℝ 0 < d ∧
	∀u⦁ Abs(u - x) < d 
	⇒	Abs(df x*(u - x) - (f u - f x)) ≤ e * Abs (u - x)
⌝);
a(rewrite_tac[deriv_def] THEN REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [2] all_fc_tac);
a(∃_tac⌜d⌝ THEN REPEAT strip_tac);
a(cases_tac⌜u = x⌝ THEN1 asm_rewrite_tac[]);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(POP_ASM_T ante_tac);
a(lemma_tac⌜¬u + ~x = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜df x * (u + ~ x) + ~ (f u) + f x
	= ~(((f u + ~ (f x))/(u + ~ x) + ~ (df x)) * (u + ~x))⌝ (fn th => rewrite_tac[th, ℝ_abs_minus_thm]));
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[hd(fc_canon ℝ_over_times_recip_thm)]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀ x t y z:ℝ⦁ (x*t + y) * z = x * t * z + y * z⌝]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2" *** *)
a(strip_tac THEN rewrite_tac[ℝ_abs_times_thm]);
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(bc_thm_tac(pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀ x y z:ℝ⦁ x < y ⇒ x ≤ y⌝));
a(all_fc_tac[ℝ_¬_0_abs_thm]);
a(bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac);
val ⦏straddle_thm_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏straddle_thm⦎ = save_thm ( "straddle_thm", (
set_goal([], ⌜ ∀f df x e⦁ 
	(f Deriv df x) x
∧	ℕℝ 0 < e
⇒	∃d⦁ℕℝ 0 < d ∧
	∀u v⦁	u ∈ OpenInterval (x - d) (x + d)
	∧	v ∈ OpenInterval (x - d) (x + d)
	∧	u ≤ x ∧ x ≤ v
	⇒	Abs(df x*(v - u)- (f v - f u)) ≤ e * (v - u)
⌝);
a(REPEAT strip_tac THEN all_fc_tac[straddle_thm_lemma]);
a(∃_tac⌜d⌝ THEN rewrite_tac[open_interval_def]
	THEN REPEAT strip_tac);
a(GET_NTH_ASM_T 7 (ante_tac o ∀_elim⌜u⌝));
a(DROP_NTH_ASM_T 7 (ante_tac o ∀_elim⌜v⌝));
a(ALL_FC_T1 fc_⇔_canon asm_rewrite_tac[ℝ_abs_diff_bounded_thm]);
a(pure_rewrite_tac[ℝ_abs_minus_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜u + ~x = ~(x + ~u)⌝]);
a(lemma_tac⌜ℕℝ 0 ≤ v + ~x ∧ ℕℝ 0 ≤ x + ~u⌝ 
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜Abs(v + ~x) = v + ~x ∧ Abs(x + ~u) = x + ~u⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_abs_def]);
a(REPEAT strip_tac);
a(LEMMA_T⌜ df x * (v + ~ u)  + ~(f v) + f u 
	= (df x*(v + ~x) + ~(f v) + f x)
	+ ~(df x*(~x + u) + ~(f u) + f x)⌝ pure_rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac ℝ_≤_trans_thm);
a(∃_tac⌜Abs(df x*(v + ~x) + ~(f v) + f x)
	+ Abs(df x*(~x + u) + ~(f u) + f x)⌝
	THEN pure_rewrite_tac[ℝ_abs_plus_minus_thm]);
a(REPEAT_N 2 (POP_ASM_T ante_tac));
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏straddle_gauge_thm⦎ = save_thm ( "straddle_gauge_thm", (
set_goal([], ⌜ ∀ A e f df⦁ 
	(∀x⦁ x ∈ A ⇒ (f Deriv df x) x)
∧	ℕℝ 0 < e
⇒	∃G⦁G ∈ Gauge ∧
	∀t I n m⦁ (t, I, n) ∈ TaggedPartition
	∧	(t, I, n) ∈ G Fine
	∧	m < n ∧ t m ∈ A
	⇒	Abs (df (t m) * (I(m+1) - I m) - (f (I(m+1)) - f(I m))) ≤ e * (I(m+1) - I m)
⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜∃D⦁(∀x⦁ℕℝ 0 < D x)
∧ 	∀x⦁x ∈ A ⇒
	∀ u v ⦁ u ∈ OpenInterval (x - D x) (x + D x)
	∧ v ∈ OpenInterval (x - D x) (x + D x)
	∧ u ≤ x ∧ x ≤ v
	⇒ Abs (df x * (v - u) - (f v - f u)) ≤ e * (v - u)⌝ (strip_asm_tac o rewrite_rule[]));
(* *** Goal "1" *** *)
a(prove_∃_tac THEN ∀_tac);
a(cases_tac⌜¬x' ∈ A⌝ THEN asm_rewrite_tac[]
	THEN1 ∃_tac⌜ℕℝ 1⌝ THEN1 REPEAT strip_tac);
a(LIST_DROP_NTH_ASM_T [3] all_fc_tac);
a(all_fc_tac[rewrite_rule[]straddle_thm]);
a(∃_tac⌜d⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(∃_tac⌜λx⦁OpenInterval (x - D x) (x + D x)⌝
	THEN rewrite_tac[gauge_def,
		open_interval_open_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(LEMMA_T⌜ℕℝ 0 < D x⌝ ante_tac
	THEN1 asm_rewrite_tac[]);
a(rewrite_tac[open_interval_def] THEN
	PC_T1 "ℝ_lin_arith" prove_tac[]);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 4 (strip_asm_tac o rewrite_rule[tagged_partition_def, closed_interval_def]));
a(DROP_NTH_ASM_T 5 (strip_asm_tac o rewrite_rule[fine_def, closed_interval_def]));
a(PC_T1 "sets_ext" POP_ASM_T (strip_asm_tac o ∀_elim⌜m⌝));
a(lemma_tac⌜I m ≤ I (m+1)⌝
	THEN1 (spec_nth_asm_tac 3 ⌜m⌝
		THEN asm_rewrite_tac[ℝ_≤_def]));
a(GET_NTH_ASM_T 2 (strip_asm_tac o ∀_elim⌜I m⌝));
a(GET_NTH_ASM_T 3 (strip_asm_tac o ∀_elim⌜I(m+1)⌝));
a(DROP_NTH_ASM_T 5 (strip_asm_tac o ∀_elim⌜m⌝));
a(LIST_DROP_NTH_ASM_T [10] all_fc_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀f df e t I n⦁
	ℕℝ 0 < e
∧	(t, I, n) ∈ TaggedPartition
∧	(∀m⦁	m < n
	⇒	Abs (df (t m) * (I(m+1) - I m) - (f (I(m+1)) - f(I m))) ≤ e * (I(m+1) - I m))
⇒	Abs(RiemannSum df (t, I, n) - (f(I n) - f(I 0))) ≤ e * (I n - I 0)
⌝);
a(REPEAT ∀_tac THEN rewrite_tac[]);
a(induction_tac⌜n⌝
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[riemann_sum_induction_thm]);
(* *** Goal "1" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 4);
a(bc_thm_tac subpartition_thm
	THEN ∃_tac⌜n+1⌝
	THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(i_contr_tac THEN swap_nth_asm_concl_tac 4);
a(POP_ASM_T bc_thm_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "3" *** *)
a(LEMMA_T ⌜
	(RiemannSum df (t, I, n) +
	df (t n) * (I (n + 1) + ~ (I n))) + 
	~ (f (I (n + 1))) + f (I 0) =
	(RiemannSum df (t, I, n) + ~(f(I n)) + f(I 0)) +
	df (t n) * (I (n + 1) + ~ (I n)) + 
	~ (f (I (n + 1))) + f (I n)
⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(LEMMA_T ⌜
	e * (I (n + 1) + ~ (I 0)) =
	e * (I n + ~ (I 0)) +
	e * (I (n + 1) + ~(I n))
⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" prove_tac[]);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀a b c d:ℝ⦁Abs(a + b) ≤ Abs a + Abs b
	∧ Abs a ≤ c ∧ Abs b ≤ d ⇒
	Abs (a + b) ≤ c + d⌝)
	THEN1 rewrite_tac[ℝ_abs_plus_thm]);
a(REPEAT strip_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
val ⦏int_deriv_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML
set_goal([], ⌜∀a b sf f⦁
	a < b
∧	(∀x⦁ a ≤ x ∧ x < b ⇒ (sf Deriv f x) x)
∧	(sf Cts b) ∧ f b = ℕℝ 0
⇒	(f Int sf b - sf a) (ClosedInterval a b)
⌝);
a(rewrite_tac[cts_def] THEN REPEAT strip_tac);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[bounded_int_thm]);
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < 1/2 * e⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 4 (strip_asm_tac o ∀_elim⌜1/2*e⌝));
a(strip_asm_tac(rewrite_rule[closed_interval_def]
	(∀_elim⌜b⌝ chosen_tag_thm)));
a(lemma_tac⌜ℕℝ 0 < b + ~a⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜ℕℝ 0 < (b + ~a) ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜ℕℝ 0 < (1/2 * e) *(b + ~a) ⋏-⋏1⌝
	THEN1 all_fc_tac[ℝ_0_less_0_less_times_thm]);
a(all_fc_tac[rewrite_rule[](
	list_∀_elim[⌜{x | a ≤ x ∧ x < b}⌝,
		⌜(1/2 * e) * (b + ~a)⋏-⋏1⌝]
			straddle_gauge_thm)]);
a(strip_asm_tac (∀_elim⌜d⌝ riemann_gauge_thm));
a(strip_asm_tac(list_∀_elim[⌜G1⌝, ⌜G⌝, ⌜G'⌝] gauge_refine_3_thm));
a(∃_tac⌜G''⌝ THEN REPEAT strip_tac);
a(cases_tac⌜n = 0⌝ THEN all_var_elim_asm_tac1);
a(LEMMA_T ⌜1 ≤ n⌝ ante_tac
	THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(rewrite_tac [≤_def] THEN once_rewrite_tac[plus_comm_thm]
	THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 2 discard_tac THEN all_var_elim_asm_tac1);
a(rewrite_tac[riemann_sum_induction_thm]);
a(DROP_NTH_ASM_T 14 (ante_tac o ∀_elim⌜G''⌝));
a(asm_rewrite_tac[] THEN strip_tac);
a(LEMMA_T ⌜t i = I(i+1)⌝ asm_rewrite_thm_tac);
(* *** Goal "1" *** *)
a(POP_ASM_T bc_thm_tac);
a(∃_tac⌜I⌝ THEN ∃_tac⌜i + 1⌝ THEN asm_rewrite_tac[]);
a(rewrite_tac[ℝ_≤_def] THEN ∨_left_tac);
a(bc_thm_tac partition_mono_thm);
a(∃_tac⌜i+1⌝ THEN ∃_tac⌜t⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(POP_ASM_T discard_tac);
a(once_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀rs x y⦁
	rs + ~x + y = ((sf(I i)) + ~x) + (rs + ~(sf(I i)) + y)⌝]);
a(bc_thm_tac (pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y⦁ Abs (x + y) ≤ Abs x + Abs y
	∧ Abs x < 1/2 * e ∧ Abs y < 1/2 * e ⇒
	Abs(x + y) < e⌝)
	THEN rewrite_tac[ℝ_abs_plus_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 15 bc_thm_tac);
a(LEMMA_T ⌜i < i + 1⌝ asm_tac THEN1 REPEAT strip_tac);
a(LEMMA_T ⌜(t, I, i + 1) ∈ G' Fine⌝ strip_asm_tac THEN1 all_fc_tac[fine_refinement_thm]);
a(LIST_DROP_NTH_ASM_T [9] all_fc_tac);
a(lemma_tac⌜I i < I (i + 1)⌝
	THEN1 all_fc_tac[partition_mono_thm]);
a(LEMMA_T ⌜i ≤ i⌝ asm_tac THEN1 REPEAT strip_tac);
a(LEMMA_T ⌜I i < I (i+1)⌝ strip_asm_tac THEN1 all_fc_tac[partition_mono_thm]);
a(rewrite_tac[ℝ_abs_def]);
a(LEMMA_T⌜¬ℕℝ 0 ≤ I i + ~ (I (i + 1))⌝ rewrite_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(bc_thm_tac ℝ_≤_less_trans_thm 
	THEN ∃_tac⌜(((1 / 2 * e) * (I (i + 1) + ~ (I 0)) ⋏-⋏1)) * (I i + ~(I 0))⌝
	THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(bc_thm_tac (rewrite_rule[]int_deriv_lemma));
a(LEMMA_T ⌜i ≤ i + 1⌝ asm_tac THEN1 REPEAT strip_tac);
a(all_fc_tac[subpartition_thm,
	subpartition_fine_thm]);
a(REPEAT strip_tac);
a(DROP_NTH_ASM_T 13 bc_thm_tac);
a(∃_tac⌜i⌝ THEN ALL_FC_T asm_rewrite_tac[fine_refinement_thm]);
a(LEMMA_T ⌜0 ≤ m⌝ asm_tac THEN1 REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[tag_lower_bound_thm]);
a(bc_thm_tac ℝ_≤_less_trans_thm THEN ∃_tac⌜I (m+1)⌝);
a(LEMMA_T ⌜m ≤ m⌝ asm_tac THEN1 REPEAT strip_tac);
a(ALL_FC_T rewrite_tac[tag_upper_bound_thm]);
a(bc_thm_tac partition_mono_thm);
a(∃_tac⌜i+1⌝ THEN ∃_tac⌜t⌝ THEN REPEAT strip_tac);
a(PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜¬ I(i+1) + ~(I 0) = ℕℝ 0⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜1/2 * e = (1 / 2 * e) * (I (i + 1) + ~ (I 0)) ⋏-⋏1 * (I (i+1) + ~ (I 0))⌝
	(fn th => conv_tac(RIGHT_C (once_rewrite_conv[th])))
	THEN1 ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
a(rewrite_tac[ℝ_times_assoc_thm]);
a(REPEAT (bc_thm_tac ℝ_times_mono_thm THEN REPEAT strip_tac));
a(bc_thm_tac partition_mono_thm);
a(∃_tac⌜i+1⌝ THEN ∃_tac⌜t⌝ THEN REPEAT strip_tac);
val ⦏gen_int_deriv_lemma⦎ = pop_thm();
=TEX
%%%%
%%%%
=SML

val ⦏int_deriv_thm2⦎ = save_thm ( "int_deriv_thm2", (
set_goal([], ⌜∀a b sf f⦁
	a < b
∧	(∀x⦁ a ≤ x ∧ x < b ⇒ (sf Deriv f x) x)
∧	(sf Cts b)
⇒	(f Int sf b - sf a) (ClosedInterval a b)
⌝);
a(REPEAT strip_tac);
a(pure_once_rewrite_tac[∀_elim⌜b⌝ chosen_value_thm]);
a(bc_thm_tac gen_int_deriv_lemma);
a(asm_rewrite_tac[] THEN REPEAT strip_tac);
a(cases_tac⌜x = b⌝ THEN1 all_var_elim_asm_tac1);
a(asm_rewrite_tac[] THEN all_asm_fc_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_deriv_thm3⦎ = save_thm ( "int_deriv_thm3", (
set_goal([], ⌜∀a b sf f⦁
	a < b
∧	(∀x⦁ a < x ∧ x ≤ b ⇒ (sf Deriv f x) x)
∧	(sf Cts a)
⇒	(f Int sf b - sf a) (ClosedInterval a b)
⌝);
a(REPEAT strip_tac);
a(LEMMA_T⌜((λx⦁f( ~x)) Int (λx⦁~(sf(~x))) (~a) - (λx⦁~(sf(~x))) (~b)) (ClosedInterval (~b) (~a))⌝
	ante_tac);
(* *** Goal "1" *** *)
a(bc_thm_tac int_deriv_thm2);
a(rewrite_tac[]);
a(REPEAT strip_tac THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.1" *** *)
a(RAT_DERIV_T ante_tac THEN conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(STRIP_T bc_thm_tac);
a(DROP_NTH_ASM_T 4 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a(simple_cts_tac);
a(bc_thm_tac comp_cts_thm);
a(asm_rewrite_tac[minus_cts_thm]);
(* *** Goal "2" *** *)
a(DROP_ASMS_T discard_tac THEN rewrite_tac[int_def]);
a(REPEAT strip_tac THEN all_fc_tac[int_ℝ_o_minus_thm]);
a(POP_ASM_T ante_tac THEN POP_ASM_T discard_tac);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv));
a(LEMMA_T⌜∀g h x⦁g = h ⇒ h Int⋎R x ⇒ g Int⋎R x⌝ bc_thm_tac
	THEN1 (REPEAT ∀_tac THEN PC_T "predicates" strip_tac THEN asm_rewrite_tac[]));
a(rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
a(once_rewrite_tac[ℝ_times_comm_thm]
	THEN rewrite_tac[χ_def]);
a(LEMMA_T ⌜~ b ≤ ~ x ∧ ~ x ≤ ~ a ⇔ a ≤ x ∧ x ≤ b⌝ rewrite_thm_tac);
a(PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_deriv_thm⦎ = save_thm ( "int_deriv_thm", (
set_goal([], ⌜∀a b sf f⦁
	a < b
∧	(∀x⦁ a < x ∧ x < b ⇒ (sf Deriv f x) x)
∧	(sf Cts a) ∧ (sf Cts b)
⇒	(f Int sf b - sf a) (ClosedInterval a b)
⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜∃y⦁a < y ∧ y < b⌝
	THEN1 (∃_tac⌜1/2*(a + b)⌝ THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(lemma_tac⌜sf Cts y⌝
	THEN1 (bc_thm_tac deriv_cts_thm
		THEN ∃_tac⌜f y⌝
		THEN all_asm_fc_tac[]));
a(lemma_tac⌜(f Int sf b - sf y)(ClosedInterval y b)⌝);
(* *** Goal "1" *** *)
a(bc_thm_tac int_deriv_thm2 THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 8 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜(f Int sf y - sf a)(ClosedInterval a y)⌝);
(* *** Goal "2.1" *** *)
a(bc_thm_tac int_deriv_thm3 THEN REPEAT strip_tac);
a(DROP_NTH_ASM_T 9 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(REPEAT_N 2 (POP_ASM_T ante_tac));
a(rewrite_tac[int_def, χ_def] THEN REPEAT strip_tac);
a(LEMMA_T⌜
	(λ x⦁	(λ x⦁ (if x ∈ ClosedInterval a y then ℕℝ 1 else ℕℝ 0) * f x) x +
		(λ x⦁ (if x ∈ ClosedInterval y b then ℕℝ 1 else ℕℝ 0) * f x) x)
             Int⋎R
	(sf y + ~ (sf a)) + sf b + ~ (sf y)⌝ ante_tac
	THEN1 all_fc_tac[int_ℝ_plus_thm]);
a(LIST_DROP_NTH_ASM_T [1, 2, 3, 6, 7, 8, 9] discard_tac);
a(bc_thm_tac (taut_rule⌜∀p1 p2⦁(p1 ⇔ p2) ⇒ p1 ⇒ p2⌝));
a(conv_tac (ONCE_MAP_C ℝ_anf_conv));
a(bc_thm_tac int_ℝ_diff_0_thm);
a(bc_thm_tac int_ℝ_singleton_support_thm);
a(∃_tac⌜y⌝ THEN rewrite_tac[closed_interval_def, open_interval_def]);
a(∀_tac);
a(cases_tac ⌜a ≤ x ∧ x ≤ b⌝
	THEN cases_tac⌜a ≤ x ∧ x ≤ y⌝
	THEN cases_tac ⌜y ≤ x ∧ x ≤ b⌝
	THEN asm_rewrite_tac[]
	THEN_TRY PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_deriv_thm1⦎ = save_thm ( "int_deriv_thm1", (
set_goal([], ⌜∀a b sf f⦁
	a < b
∧	(∀x⦁ x ∈ ClosedInterval a b ⇒ (sf Deriv f x) x)
⇒	(f Int sf b - sf a) (ClosedInterval a b)
⌝);
a(REPEAT strip_tac);
a(bc_thm_tac int_deriv_thm2);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[closed_interval_def]));
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(bc_thm_tac deriv_cts_thm);
a(∃_tac⌜f b⌝ THEN POP_ASM_T bc_thm_tac
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_ℝ_χ_interval_thm⦎ = save_thm ( "int_ℝ_χ_interval_thm", (
set_goal([], ⌜∀a b⦁
	a ≤ b
⇒	(χ (ClosedInterval a b) Int⋎R b - a)
⌝);
a(rewrite_tac[ℝ_≤_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ante_tac(list_∀_elim[⌜a⌝, ⌜b⌝,
	⌜λx:ℝ⦁ x⌝,
	⌜λx:ℝ⦁ ℕℝ 1⌝]
	int_deriv_thm1));
a(asm_rewrite_tac[closed_interval_def, int_def,
	η_axiom]);
a(REPEAT strip_tac);
a(i_contr_tac THEN swap_nth_asm_concl_tac 1);
a(RAT_DERIV_T strip_asm_tac);
(* *** Goal "2" *** *)
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
a(bc_thm_tac int_ℝ_singleton_support_thm);
a(∃_tac⌜b⌝ THEN rewrite_tac[closed_interval_def,
	χ_def, pc_rule1 "ℝ_lin_arith" prove_rule[]
		⌜∀x⦁b ≤ x ∧ x ≤ b ⇔ x = b⌝]);
a(∀_tac THEN cases_tac⌜x = b⌝ THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_example_thm⦎ = save_thm ( "int_example_thm", (
set_goal([], ⌜((λx⦁Sqrt(ℕℝ 1 - x^2)⋏-⋏1) Int π) (ClosedInterval (~(ℕℝ 1)) (ℕℝ 1))⌝);
a(ante_tac(list_∀_elim[⌜~(ℕℝ 1)⌝, ⌜ℕℝ 1⌝,
	⌜ArcSin⌝,
	⌜λx⦁Sqrt (ℕℝ 1 - x ^ 2)⋏-⋏1⌝]
	int_deriv_thm));
a(rewrite_tac[
	rewrite_rule[ℝ_abs_≤_less_interval_thm,
		open_interval_def] arc_sin_deriv_thm,
	rewrite_rule[] (∀_elim⌜ℕℝ 1⌝arc_sin_cts_thm),
	rewrite_rule[] (∀_elim⌜~(ℕℝ 1)⌝arc_sin_cts_thm),
	arc_sin_1_minus_1_thm]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏int_recip_thm⦎ = save_thm ( "int_recip_thm", (
set_goal([], ⌜∀a b⦁ℕℝ 0 < a ∧ a < b
⇒	((λx⦁x ⋏-⋏1) Int Log b - Log a) (ClosedInterval a b)⌝);
a(REPEAT strip_tac THEN bc_thm_tac int_deriv_thm1);
a(rewrite_tac[closed_interval_def] THEN REPEAT strip_tac);
a(TRANS_DERIV_T strip_asm_tac);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏log_minus_log_estimate_thm⦎ = save_thm ( "log_minus_log_estimate_thm", (
set_goal([], ⌜∀a b⦁ℕℝ 0 < a ∧ a < b
⇒	Log b - Log a ≤ (b - a) * a ⋏-⋏1⌝);
a(REPEAT strip_tac THEN once_rewrite_tac[ℝ_times_comm_thm]
	THEN bc_thm_tac int_ℝ_≤_thm);
a(∃_tac⌜λx⦁a ⋏-⋏1 * χ(ClosedInterval a b) x⌝
	THEN ∃_tac⌜λx⦁ χ(ClosedInterval a b) x * x ⋏-⋏1⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[χ_def, closed_interval_def]);
a(cases_tac⌜a ≤ x ∧ x ≤ b⌝ THEN asm_rewrite_tac[]);
a(cases_tac⌜a = x⌝ THEN1 asm_rewrite_tac[]);
a(lemma_tac⌜a < x⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(all_fc_tac[ℝ_less_recip_less_thm]);
a(asm_rewrite_tac[ℝ_≤_def]);
(* *** Goal "2" *** *)
a(ALL_FC_T rewrite_tac[rewrite_rule[int_def] int_recip_thm]);
(* *** Goal "3" *** *)
a(bc_thm_tac int_ℝ_const_times_thm);
a(lemma_tac⌜a ≤ b⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[rewrite_rule[] int_ℝ_χ_interval_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏harmonic_series_estimate_thm⦎ = save_thm ( "harmonic_series_estimate_thm", (
set_goal([], ⌜∀m⦁
	Log (ℕℝ (m+1)) ≤ Series (λm⦁ ℕℝ (m+1) ⋏-⋏1) m⌝);
a(REPEAT strip_tac THEN induction_tac⌜m:ℕ⌝);
(* *** Goal "1" *** *)
a(rewrite_tac[log_clauses, series_def]);
(* *** Goal "2" *** *)
a(ante_tac(list_∀_elim[⌜ℕℝ(m+1)⌝, ⌜ℕℝ((m+1)+1)⌝]
	log_minus_log_estimate_thm));
a(rewrite_tac[series_def, ℕℝ_less_thm]);
a(LEMMA_T⌜(ℕℝ ((m + 1) + 1) + ~ (ℕℝ (m + 1))) = ℕℝ 1⌝
	rewrite_thm_tac
	THEN1 (rewrite_tac[ℕℝ_plus_homomorphism_thm]
		THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(intro_∀_tac(⌜ℕℝ (m + 1) ⋏-⋏1⌝, ⌜t:ℝ⌝));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏harmonic_series_divergent_thm⦎ = save_thm ( "harmonic_series_divergent_thm", (
set_goal([], ⌜∀c⦁ ¬ Series (λm⦁ ℕℝ (m+1) ⋏-⋏1) -> c⌝);
a(contr_tac THEN all_fc_tac[lim_seq_bounded_thm]);
a(strip_asm_tac(∀_elim⌜Exp b⌝ ℝ_archimedean_thm));
a(lemma_tac⌜ℕℝ 0 < Exp b⌝ THEN1 rewrite_tac[exp_clauses]);
a(strip_asm_tac (∀_elim⌜m⌝ℕ_cases_thm)
	THEN all_var_elim_asm_tac1
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T ⌜Log(Exp b) < Log(ℕℝ(i+1))⌝ ante_tac
	THEN1 all_fc_tac[log_less_mono_thm]);
a(rewrite_tac[log_def] THEN contr_tac);
a(strip_asm_tac(∀_elim⌜i⌝ harmonic_series_estimate_thm));
a(lemma_tac⌜ℕℝ 0 ≤ (Series (λ m⦁ ℕℝ (m + 1) ⋏-⋏1) i)⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(DROP_NTH_ASM_T 6 (ante_tac o ∀_elim⌜i⌝)
	THEN asm_rewrite_tac[ℝ_abs_def]);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%% AREAS OF PLANE SETS
%%%%
=SML

val ⦏area_unique_thm⦎ = save_thm ( "area_unique_thm", (
set_goal([], ⌜∀A c d⦁ A Area c ∧ A Area d ⇒ c = d⌝);
a(rewrite_tac[area_def] THEN REPEAT strip_tac);
a(LEMMA_T⌜sf'= sf⌝ asm_tac
	THEN_LIST [rewrite_tac[] THEN REPEAT strip_tac,
		all_var_elim_asm_tac1 THEN all_fc_tac[int_ℝ_unique_thm]]);
a(spec_nth_asm_tac 3 ⌜x⌝);
a(spec_nth_asm_tac 2 ⌜x⌝);
a(all_fc_tac[int_ℝ_unique_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_translate_thm⦎ = save_thm ( "area_translate_thm", (
set_goal([], ⌜∀A c u v⦁
	A Area c ⇒ {(x, y) | (x + u, y + v) ∈ A} Area c⌝);
a(rewrite_tac[area_def] THEN REPEAT strip_tac);
a(∃_tac⌜λx⦁sf(x + u)⌝
	THEN asm_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) int_ℝ_o_plus_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜χ {y|(x + u, y + v) ∈ A} = 
	λz⦁χ {y|(x + u, y) ∈ A} (z + v)⌝
	(fn th => asm_rewrite_tac[th,
	conv_rule(ONCE_MAP_C eq_sym_conv) int_ℝ_o_plus_thm])
	THEN1 rewrite_tac[χ_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_dilate_thm⦎ = save_thm ( "area_dilate_thm", (
set_goal([], ⌜∀A c d e⦁
	A Area c ∧ ¬d = ℕℝ 0 ∧ ¬e = ℕℝ 0
⇒	{(x, y) | (d ⋏-⋏1*x, e ⋏-⋏1*y) ∈ A} Area Abs d * Abs e *c⌝);
a(rewrite_tac[area_def] THEN REPEAT strip_tac);
a(all_fc_tac[ℝ_¬_recip_0_thm]);
a(lemma_tac⌜¬Abs d = ℕℝ 0 ∧ ¬Abs e = ℕℝ 0⌝ THEN1 asm_rewrite_tac[ℝ_abs_eq_0_thm]);
a(∃_tac⌜λx⦁Abs e*sf(d ⋏-⋏1 * x)⌝
	THEN asm_rewrite_tac[ℝ_ℕ_exp_square_thm,
		ℝ_times_assoc_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac[∀_elim⌜Abs e⌝ ℝ_times_order_thm]);
a(ho_bc_thm_tac int_ℝ_const_times_thm);
a(LEMMA_T⌜Abs d * c = Abs (d ⋏-⋏1) ⋏-⋏1 * c⌝ rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[ℝ_recip_clauses,
	ℝ_abs_recip_thm]);
a(bc_thm_tac int_ℝ_o_times_thm);
a(conv_tac(ONCE_MAP_C eq_sym_conv) THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(LEMMA_T ⌜χ {y|(d ⋏-⋏1 * x, e ⋏-⋏1 * y) ∈ A} = 
	λz⦁χ {y|(d ⋏-⋏1*x, y) ∈ A} (e ⋏-⋏1 *z)⌝
	rewrite_thm_tac
	THEN1 rewrite_tac[χ_def]);
a(LEMMA_T⌜Abs e = Abs (e ⋏-⋏1) ⋏-⋏1⌝ rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac[ℝ_recip_clauses,
	ℝ_abs_recip_thm]);
a(bc_thm_tac int_ℝ_o_times_thm);
a(conv_tac(ONCE_MAP_C eq_sym_conv) THEN asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_dilate_thm1⦎ = save_thm ( "area_dilate_thm1", (
set_goal([], ⌜∀A c d⦁
	A Area c ∧ ¬d = ℕℝ 0
⇒	{(x, y) | (d ⋏-⋏1*x, d ⋏-⋏1*y) ∈ A} Area d ^ 2 * c⌝);
a(REPEAT strip_tac
	THEN ALL_FC_T (MAP_EVERY ante_tac) [area_dilate_thm]);
a(LEMMA_T ⌜Abs d * Abs d * c = d ^ 2 * c⌝
	 rewrite_thm_tac);
a(once_rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv) ℝ_abs_squared_thm]);
a(rewrite_tac[ℝ_ℕ_exp_square_thm, ℝ_times_assoc_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_empty_thm⦎ = save_thm ( "area_empty_thm", (
set_goal([], ⌜{} Area ℕℝ 0⌝);
a(rewrite_tac[area_def] THEN REPEAT strip_tac);
a(∃_tac⌜λx:ℝ⦁ ℕℝ 0⌝
	THEN rewrite_tac[int_ℝ_0_thm]);
(* *** Goal "1" *** *)
a(rewrite_tac[pc_rule1 "sets_ext" prove_rule[] ⌜{y|F} = {}⌝]);
a(LEMMA_T⌜χ{} = λx:ℝ⦁ℕℝ 0⌝
	(fn th => rewrite_tac[th, int_ℝ_0_thm]));
a(rewrite_tac[χ_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_∪_thm⦎ = save_thm ( "area_∪_thm", (
set_goal([], ⌜∀A B c d y⦁
	A Area c ∧ B Area d ∧ A ∩ B Area y
⇒	A ∪ B Area c + d - y⌝);
a(rewrite_tac[area_def] THEN REPEAT strip_tac);
a(∃_tac⌜λx⦁sf x + (λz⦁sf' z + (λu⦁~(sf'' u)) z)x⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(REPEAT(bc_thm_tac int_ℝ_plus_thm THEN REPEAT strip_tac));
a(bc_thm_tac int_ℝ_minus_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(rewrite_tac[]);
a(LEMMA_T⌜
	χ {y|(x, y) ∈ A ∪ B} =
	λv⦁χ {y|(x, y) ∈ A} v +
		(λz⦁χ {y|(x, y) ∈ B} z +
		(λu⦁~(χ {y|(x, y) ∈ A ∩ B} u)) z) v⌝
	pure_rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[] THEN PC_T1 "sets_ext1" rewrite_tac[χ_def]
	THEN REPEAT strip_tac);
a(MAP_EVERY cases_tac[⌜(x, x') ∈ A⌝, ⌜(x, x') ∈ B⌝]
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(REPEAT(bc_thm_tac int_ℝ_plus_thm THEN REPEAT strip_tac
	THEN1 asm_rewrite_tac[]));
a(bc_thm_tac int_ℝ_minus_thm THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_∩_thm⦎ = save_thm ( "area_∩_thm", (
set_goal([], ⌜∀A B c d y⦁
	A Area c ∧ B Area d ∧ A ∪ B Area y
⇒	A ∩ B Area c + d - y⌝);
a(rewrite_tac[area_def] THEN REPEAT strip_tac);
a(∃_tac⌜λx⦁sf x + (λz⦁sf' z + (λu⦁~(sf'' u)) z)x⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(REPEAT(bc_thm_tac int_ℝ_plus_thm THEN REPEAT strip_tac));
a(bc_thm_tac int_ℝ_minus_thm THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(rewrite_tac[]);
a(LEMMA_T⌜
	χ {y|(x, y) ∈ A ∩ B} =
	λv⦁χ {y|(x, y) ∈ A} v +
		(λz⦁χ {y|(x, y) ∈ B} z +
		(λu⦁~(χ {y|(x, y) ∈ A ∪ B} u)) z) v⌝
	pure_rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[] THEN PC_T1 "sets_ext1" rewrite_tac[χ_def]
	THEN REPEAT strip_tac);
a(MAP_EVERY cases_tac[⌜(x, x') ∈ A⌝, ⌜(x, x') ∈ B⌝]
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(REPEAT(bc_thm_tac int_ℝ_plus_thm THEN REPEAT strip_tac
	THEN1 asm_rewrite_tac[]));
a(bc_thm_tac int_ℝ_minus_thm THEN REPEAT strip_tac);
a(asm_rewrite_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_rectangle_thm⦎ = save_thm ( "area_rectangle_thm", (
set_goal([], ⌜∀w h⦁ ℕℝ 0 ≤ h ∧ ℕℝ 0 ≤ w
⇒	{(x, y) |
		x ∈ ClosedInterval (ℕℝ 0) w
	∧	y ∈ ClosedInterval (ℕℝ 0) h}
	Area w * h⌝);
a(rewrite_tac[area_def] THEN REPEAT strip_tac);
a(∃_tac⌜λx:ℝ⦁χ (ClosedInterval (ℕℝ 0) w) x * h⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(bc_thm_tac int_ℝ_const_times_thm);
a(LEMMA_T ⌜w = w - ℕℝ 0⌝ (fn th => conv_tac(RIGHT_C(pure_once_rewrite_conv[th])))
	THEN1 rewrite_tac[]);
a(bc_thm_tac int_ℝ_χ_interval_thm THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a(cases_tac⌜x ∈ ClosedInterval (ℕℝ 0) w⌝
	THEN asm_rewrite_tac[
	pc_rule1 "sets_ext1" prove_rule[]
	⌜{y|F} = {} ∧ ∀a⦁{v | v ∈ a} = a⌝]);
(* *** Goal "2.1" *** *)
a(TOP_ASM_T (fn th => conv_tac(RIGHT_C(rewrite_conv[th, χ_def]))));
a(LEMMA_T ⌜h = h - ℕℝ 0⌝ (fn th => conv_tac(RIGHT_C(pure_once_rewrite_conv[th])))
	THEN1 rewrite_tac[]);
a(bc_thm_tac int_ℝ_χ_interval_thm THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(asm_rewrite_tac[χ_def]);
a(LEMMA_T⌜χ{} = λx:ℝ⦁ℕℝ 0⌝
	(fn th => rewrite_tac[th, int_ℝ_0_thm]));
a(rewrite_tac[χ_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_circle_lemma1⦎ = save_thm ( "area_circle_lemma1", (
set_goal([], ⌜∀x⦁Abs x < ℕℝ 1 ⇒
	((λx⦁x * Sqrt (ℕℝ 1 - x ^ 2) + ArcSin x) Deriv ℕℝ 2 * Sqrt (ℕℝ 1 - x ^ 2)) x
⌝);
a(REPEAT strip_tac THEN lemma_tac⌜Abs x ≤ ℕℝ 1⌝
	THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(bc_thm_tac deriv_local_thm);
a(MAP_EVERY ∃_tac[⌜(λx⦁x * Cos(ArcSin x) + ArcSin x)⌝, ⌜ℕℝ 1⌝, ⌜~(ℕℝ 1)⌝]);
a(GET_NTH_ASM_T 2 (rewrite_thm_tac o rewrite_rule[open_interval_def, ℝ_abs_≤_less_interval_thm]));
a(REPEAT strip_tac
	THEN1 ALL_FC_T rewrite_tac[rewrite_rule[ℝ_≤_def, closed_interval_def, ℝ_abs_≤_less_interval_thm]cos_arc_sin_thm]);
a(DERIV_T (arc_sin_deriv_thm::trans_deriv_thms) ante_tac);
a(ALL_FC_T asm_rewrite_tac[sin_arc_sin_thm, cos_arc_sin_thm]);
a(rewrite_tac[ℝ_ℕ_exp_square_thm,
	ℝ_plus_assoc_thm,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀y⦁x * ~x * y + y = (ℕℝ 1 + ~ (x*x)) * y⌝]);
a(cases_tac⌜ℕℝ 0 < ℕℝ 1 + ~ (x * x)⌝);
(* *** Goal "1" *** *)
a(ALL_FC_T rewrite_tac[id_over_sqrt_thm]);
a(rewrite_tac[
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀y:ℝ⦁y + y = ℕℝ 2 * y⌝]);
(* *** Goal "2" *** *)
a(i_contr_tac THEN POP_ASM_T ante_tac THEN
	POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a(rewrite_tac[
	ℝ_abs_≤_less_interval_thm,
	open_interval_def,
	pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀y:ℝ⦁ℕℝ 1 + ~(y * y) = (ℕℝ 1 + y) * (ℕℝ 1 + ~y)⌝]);
a(REPEAT strip_tac THEN bc_thm_tac ℝ_0_less_0_less_times_thm);
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_circle_lemma2⦎ = save_thm ( "area_circle_lemma2", (
set_goal([], ⌜∀x⦁Abs x ≤ ℕℝ 1 ⇒ ℕℝ 0 ≤ ℕℝ 1 - x^2
⌝);
a(rewrite_tac[
	ℝ_ℕ_exp_square_thm,
	ℝ_abs_≤_less_interval_thm,
	closed_interval_def] THEN REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 1 + ~ (x * x) = (ℕℝ 1 + x) * (ℕℝ 1 + ~x)
	∧ ℕℝ 0 ≤ ℕℝ 1 + x ∧ ℕℝ 0 ≤ ℕℝ 1 + ~x⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(asm_rewrite_tac[] THEN LIST_DROP_NTH_ASM_T[3, 4, 5] discard_tac);
a(all_fc_tac[ℝ_0_≤_0_≤_times_thm]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_circle_lemma3⦎ = save_thm ( "area_circle_lemma3", (
set_goal([], ⌜∀x⦁Abs x ≤ ℕℝ 1 ⇒
	(λx⦁x * Sqrt (ℕℝ 1 - x ^ 2) + ArcSin x) Cts x
⌝);
a(REPEAT strip_tac);
a(REPEAT(simple_cts_tac THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a(ho_bc_thm_tac(∀_elim⌜Sqrt⌝comp_cts_thm));
a(rewrite_tac[ℝ_ℕ_exp_square_thm]);
a(strip_tac THEN REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(bc_thm_tac sqrt_cts_thm);
a(bc_thm_tac(rewrite_rule[ℝ_ℕ_exp_square_thm] area_circle_lemma2)
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a(bc_thm_tac arc_sin_cts_thm THEN strip_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_circle_lemma4⦎ = save_thm ( "area_circle_lemma4", (
set_goal([], ⌜∀r x y⦁ Abs x ≤ r
⇒	(Sqrt(x^2 +y^2) ≤ r ⇔ Abs y ≤ Sqrt(r^2 - x^2))⌝);
a(REPEAT ∀_tac THEN ⇒_tac THEN rewrite_tac[]);
a(lemma_tac⌜ℕℝ 0 ≤ Abs x ∧ ℕℝ 0 ≤ Abs y ∧ ℕℝ 0 ≤ x^2 ∧ ℕℝ 0 ≤ y^2⌝
	THEN1 rewrite_tac[ℝ_0_≤_abs_thm, 
		ℝ_0_≤_square_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ r⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T1 fc_⇔_canon (fn ths =>
	GET_NTH_ASM_T 6
	(fn th => strip_asm_tac(rewrite_rule
	(ℝ_abs_squared_thm::ths)th)))
	[square_mono_≤_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ r^2 + ~(x^2) ∧ ℕℝ 0 ≤ x^2 + y^2⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(lemma_tac⌜ℕℝ 0 ≤ Sqrt(r^2 + ~(x^2)) ∧ ℕℝ 0 ≤ Sqrt(x^2 + y^2)⌝
	THEN1 ALL_FC_T rewrite_tac[sqrt_def]);
a(ALL_FC_T1 fc_⇔_canon rewrite_tac[square_mono_≤_thm,
	sqrt_def]);
a(rewrite_tac[ℝ_abs_squared_thm]
	THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_circle_int_thm⦎ = save_thm ( "area_circle_int_thm", (
set_goal([], ⌜
	((λx⦁ℕℝ 2 * Sqrt (ℕℝ 1 - x ^ 2)) Int π)
	(ClosedInterval (~(ℕℝ 1)) (ℕℝ 1))
⌝);
a(ante_tac(list_∀_elim[⌜~(ℕℝ 1)⌝, ⌜ℕℝ 1⌝,
	⌜λ x⦁ x * Sqrt (ℕℝ 1 - x ^ 2) + ArcSin x⌝,
	⌜λx⦁ℕℝ 2 * Sqrt (ℕℝ 1 - x ^ 2)⌝]
	int_deriv_thm));
a(rewrite_tac[
	rewrite_rule[ℝ_abs_≤_less_interval_thm,
		open_interval_def] area_circle_lemma1,
	arc_sin_1_minus_1_thm,
	sqrt_0_1_thm]);
a(LEMMA_T⌜Abs(~(ℕℝ 1)) ≤ ℕℝ 1⌝ asm_tac
	THEN1 rewrite_tac[]);
a(LEMMA_T⌜Abs(ℕℝ 1) ≤ ℕℝ 1⌝ asm_tac
	THEN1 rewrite_tac[]);
a(ALL_FC_T rewrite_tac[rewrite_rule[] area_circle_lemma3]);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv));
a(taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_unit_circle_thm⦎ = save_thm ( "area_unit_circle_thm", (
set_goal([], ⌜{(x, y) | Sqrt(x^2 + y^2) ≤ ℕℝ 1} Area π⌝);
a(rewrite_tac[area_def] THEN REPEAT strip_tac);
a(∃_tac⌜λx⦁(if Abs x ≤ ℕℝ 1 then ℕℝ 1 else ℕℝ 0) * ℕℝ 2 * Sqrt(ℕℝ 1 - x^2)⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(ante_tac(rewrite_rule[int_def] area_circle_int_thm));
a(LEMMA_T ⌜(λ x⦁ χ (ClosedInterval (~ (ℕℝ 1)) (ℕℝ 1)) x * ℕℝ 2 * Sqrt (ℕℝ 1 + ~ (x ^ 2))) =
	(λ x⦁ (if Abs x ≤ ℕℝ 1 then ℕℝ 1 else ℕℝ 0) * ℕℝ 2 * Sqrt (ℕℝ 1 + ~ (x ^ 2)))⌝ rewrite_thm_tac);
a(rewrite_tac[closed_interval_def, χ_def,
	ℝ_abs_≤_less_interval_thm]);
(* *** Goal "2" *** *)
a(cases_tac⌜¬Abs x ≤ ℕℝ 1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a(LEMMA_T⌜χ{y|Sqrt (x ^ 2 + y ^ 2) ≤ ℕℝ 1} = (λx⦁ℕℝ 0)⌝ (fn th => rewrite_tac[th, int_ℝ_0_thm]));
a(rewrite_tac[χ_def] THEN REPEAT strip_tac);
a(LEMMA_T⌜¬Sqrt (x ^ 2 + x' ^ 2) ≤ ℕℝ 1⌝ rewrite_thm_tac);
a(cases_tac⌜x = ℕℝ 0⌝
	THEN1 (all_var_elim_asm_tac1 THEN all_asm_ante_tac THEN rewrite_tac[]));
a(strip_asm_tac(∀_elim⌜x⌝ ℝ_0_≤_square_thm));
a(strip_asm_tac(∀_elim⌜x'⌝ ℝ_0_≤_square_thm));
a(cases_tac⌜x' ^ 2 = ℕℝ 0⌝ THEN1
	asm_rewrite_tac[sqrt_square_thm]);
a(LEMMA_T⌜Sqrt (x ^ 2) < Sqrt (x ^ 2 + x' ^ 2)⌝ ante_tac
	THEN1 bc_thm_tac sqrt_mono_thm
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(rewrite_tac[sqrt_square_thm] THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2.2" *** *)
a(LEMMA_T⌜{y|Sqrt (x ^ 2 + y ^ 2) ≤ ℕℝ 1} = 
	ClosedInterval
	(~(Sqrt(ℕℝ 1 + ~ (x ^ 2)))) (Sqrt(ℕℝ 1 + ~ (x ^ 2)))⌝rewrite_thm_tac);
(* *** Goal "2.2.1" *** *)
a(PC_T1 "sets_ext" rewrite_tac[conv_rule(ONCE_MAP_C eq_sym_conv)
	ℝ_abs_≤_less_interval_thm] THEN ∀_tac);
a(FC_T1 fc_⇔_canon rewrite_tac[
	rewrite_rule[](∀_elim⌜ℕℝ 1⌝ area_circle_lemma4)]);
(* *** Goal "2.2.2" *** *)
a(all_fc_tac[rewrite_rule[]area_circle_lemma2]);
a(lemma_tac⌜ℕℝ 0 ≤ Sqrt (ℕℝ 1 + ~ (x ^ 2))⌝
	THEN1 all_fc_tac[sqrt_def]);
a(pure_rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x⦁ℕℝ 2 * x = x - ~x⌝]);
a(bc_thm_tac(int_ℝ_χ_interval_thm));
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏circle_dilate_thm⦎ = save_thm ( "circle_dilate_thm", (
set_goal([], ⌜∀r⦁ℕℝ 0 < r
⇒	{(x, y)|Sqrt (x ^ 2 + y ^ 2) ≤ r}
=	{(x, y)|Sqrt ((r ⋏-⋏1 * x) ^ 2 + (r ⋏-⋏1 * y) ^ 2) ≤ ℕℝ 1}⌝);
a(REPEAT strip_tac);
a(PC_T1"sets_ext1" rewrite_tac[] THEN REPEAT ∀_tac);
a(LEMMA_T⌜∀x y z: ℝ⦁ (x*y) ^ 2 = x ^ 2 * y ^ 2 ∧
	x*y + x*z = x*(y + z)⌝
	rewrite_thm_tac
	THEN1 (rewrite_tac[ℝ_ℕ_exp_square_thm]
		THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
a(all_fc_tac[ℝ_0_less_0_less_recip_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ x1^2 ∧ ℕℝ 0 ≤ x2^2 ∧ ℕℝ 0 ≤ (r ⋏-⋏1)^2⌝
	THEN1 rewrite_tac[ℝ_0_≤_square_thm]);
a(lemma_tac⌜ℕℝ 0 ≤ x1^2 + x2^2⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[sqrt_times_thm]);
a(rewrite_tac[sqrt_square_thm, ℝ_abs_def]);
a(LEMMA_T ⌜ℕℝ 0 ≤ r ⋏-⋏1⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[ℝ_≤_def]);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀x y : ℝ ⦁x ≤ y ⇔ ¬y < x⌝,
	prove_rule[]
	⌜∀p q⦁(¬p ⇔ ¬q) ⇔ (q ⇔ p)⌝]);
a(strip_asm_tac(∀_elim⌜r⌝ℝ_times_mono_⇔_thm));
a(POP_ASM_T(fn th => (conv_tac(LEFT_C( once_rewrite_conv[th])))));
a(rewrite_tac[ℝ_times_assoc_thm1]);
a(lemma_tac⌜¬r = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(ALL_FC_T rewrite_tac[ℝ_recip_clauses]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏area_circle_thm⦎ = save_thm ( "area_circle_thm", (
set_goal([], ⌜∀r⦁
	ℕℝ 0 < r
⇒	{(x, y) | Sqrt(x^2 + y^2) ≤ r} Area π * r ^ 2⌝);
a(REPEAT strip_tac);
a(lemma_tac⌜¬r = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(strip_asm_tac area_unit_circle_thm);
a(ALL_FC_T (MAP_EVERY ante_tac) [area_dilate_thm1]);
a(rewrite_tac[]);
a(all_fc_tac[circle_dilate_thm]);
a(POP_ASM_T rewrite_thm_tac);
a(conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN taut_tac);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏buffon_needle_lemma⦎ = save_thm ( "buffon_needle_lemma", (
set_goal([], ⌜
	let	S = {(θ, d) | θ ∈ ClosedInterval (ℕℝ 0) π ∧ d ∈ ClosedInterval (ℕℝ 0) (ℕℝ 1)}
	in let	x_axis = {(x, y) | y = ℕℝ 0}
	in let	needle(θ, d) =
		{(x, y) | ∃t⦁ t ∈ ClosedInterval (ℕℝ 0) (ℕℝ 1)
			∧ x = t * Cos θ ∧ y = d - t * Sin θ}
	in let	X = {(θ, d) | (θ, d) ∈ S ∧ ¬needle(θ, d) ∩ x_axis = {}}
	in	X Area ℕℝ 2
⌝);
a(rewrite_tac[let_def, area_def]);
a(∃_tac⌜λx:ℝ⦁ χ(ClosedInterval (ℕℝ 0) π) x * Sin x⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(LEMMA_T ⌜(Sin Int (λx⦁~(Cos x)) π - (λx⦁~(Cos x)) (ℕℝ 0)) (ClosedInterval (ℕℝ 0) π)⌝
	(accept_tac o rewrite_rule[
		sin_cos_π_thm, cos_def, int_def]));
a(bc_thm_tac int_deriv_thm1);
a(rewrite_tac[π_def] THEN REPEAT strip_tac);
a(TRANS_DERIV_T ante_tac);
a(conv_tac(ONCE_MAP_C ℝ_anf_conv) THEN taut_tac);
(* *** Goal "2" *** *)
a(cases_tac⌜¬x' ∈ ClosedInterval(ℕℝ 0) π⌝
	THEN asm_rewrite_tac[χ_def]);
(* *** Goal "2.1" *** *)
a(asm_rewrite_tac[
	pc_rule1"sets_ext" prove_rule[] ⌜{z|F} = {}⌝]);
a(LEMMA_T⌜χ({} : ℝ SET) = λx⦁ℕℝ 0⌝ (fn th => rewrite_tac[th, int_ℝ_0_thm]));
a(rewrite_tac[χ_def]);
(* *** Goal "2.2" *** *)
a(LEMMA_T⌜∀X Y⦁ Y = X ∧ χ X Int⋎R Sin x' ⇒ χ Y Int⋎R Sin x'⌝ bc_thm_tac
	THEN1 (REPEAT strip_tac THEN asm_rewrite_tac[]));
a(∃_tac⌜ClosedInterval(ℕℝ 0) (Sin x')⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(all_asm_ante_tac
	THEN PC_T1 "sets_ext1" rewrite_tac[closed_interval_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.2.1.1" *** *)
a(all_var_elim_asm_tac1 THEN POP_ASM_T ante_tac);
a(rewrite_tac[pc_rule1 "ℝ_lin_arith" prove_rule[]
	⌜∀y⦁x + ~y = ℕℝ 0 ⇔ x = y⌝]);
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(cases_tac⌜x' = ℕℝ 0⌝
	THEN1 asm_rewrite_tac[sin_def]);
a(cases_tac⌜x' = π⌝
	THEN1 asm_rewrite_tac[sin_cos_π_thm]);
a(lemma_tac⌜x' ∈ OpenInterval (ℕℝ 0) π⌝
	THEN1 (rewrite_tac[open_interval_def] 
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[sin_0_π_0_less_thm]);
a(once_rewrite_tac[ℝ_times_comm_thm]);
a(bc_thm_tac(rewrite_rule[](list_∀_elim
	[⌜Sin x'⌝, ⌜t⌝, ⌜ℕℝ 1⌝]ℝ_≤_times_mono_thm)));
a(asm_rewrite_tac[ℝ_≤_def]);
(* *** Goal "2.2.1.2" *** *)
a(strip_asm_tac(
	rewrite_rule[ℝ_abs_≤_less_interval_thm, closed_interval_def]
(∀_elim⌜x'⌝ abs_sin_abs_cos_≤_1_thm))
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(cases_tac⌜x = ℕℝ 0⌝ THEN1 all_var_elim_asm_tac1);
a(∃_tac⌜ℕℝ 0⌝ THEN REPEAT strip_tac);
a(∃_tac⌜ℕℝ 0⌝ THEN REPEAT strip_tac);
a(∃_tac⌜ℕℝ 0⌝ THEN rewrite_tac[]);
(* *** Goal "2.2.1.3.2" *** *)
a(cases_tac⌜x = Sin x'⌝ THEN1 all_var_elim_asm_tac1);
a(∃_tac⌜Cos x'⌝ THEN REPEAT strip_tac);
a(∃_tac⌜ℕℝ 0⌝ THEN REPEAT strip_tac);
a(∃_tac⌜ℕℝ 1⌝ THEN rewrite_tac[]);
(* *** Goal "2.2.1.3.2.2" *** *)
a(DROP_NTH_ASM_T 3 ante_tac);
a(cases_tac⌜x' = ℕℝ 0⌝ THEN1 
	(all_var_elim_asm_tac1 THEN rewrite_tac[sin_def]
		THEN strip_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(cases_tac⌜x' = π⌝ THEN1 
	(all_var_elim_asm_tac1 THEN rewrite_tac[sin_cos_π_thm]
		THEN strip_tac
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(REPEAT strip_tac);
a(lemma_tac⌜ℕℝ 0 < x' ∧ x' < π ∧ ℕℝ 0 < x ∧ x < Sin x'⌝
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LIST_DROP_NTH_ASM_T (interval 5 12) discard_tac);
(* *** Goal "2.2.1.3.2.2" *** *)
a(lemma_tac⌜∀z⦁ (λz⦁x + ~(z * Sin x')) Cts z⌝
	THEN REPEAT strip_tac
	THEN1 REPEAT (simple_cts_tac THEN REPEAT strip_tac));
a(ante_tac(list_∀_elim
	[⌜(λz⦁x + ~(z * Sin x'))⌝, ⌜ℕℝ 0⌝, ⌜ℕℝ 1⌝]intermediate_value_thm));
a(asm_rewrite_tac[]);
a(STRIP_T (ante_tac o ∀_elim⌜ℕℝ 0⌝));
a(LEMMA_T⌜x + ~ (Sin x') < ℕℝ 0⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(REPEAT strip_tac);
a(∃_tac⌜x'' * Cos x'⌝ THEN REPEAT strip_tac);
a(∃_tac⌜ℕℝ 0⌝ THEN REPEAT strip_tac);
a(∃_tac⌜x''⌝ THEN asm_rewrite_tac[ℝ_≤_def]);
(* *** Goal "2.2.2" *** *)
a(conv_tac(RIGHT_C(pure_once_rewrite_conv[
	prove_rule[]⌜Sin x' = Sin x' - ℕℝ 0⌝])));
a(bc_thm_tac int_ℝ_χ_interval_thm);
a(cases_tac⌜x' = ℕℝ 0⌝ THEN1 asm_rewrite_tac[sin_def]);
a(cases_tac⌜x' = π⌝ THEN1 asm_rewrite_tac[sin_cos_π_thm]);
a(DROP_NTH_ASM_T 3 (strip_asm_tac o rewrite_rule[closed_interval_def]));
a(lemma_tac⌜x' ∈ OpenInterval (ℕℝ 0) π⌝
	THEN1 (rewrite_tac[open_interval_def] 
		THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a(all_fc_tac[sin_0_π_0_less_thm]);
a(asm_rewrite_tac[ℝ_≤_def]);
pop_thm()
));

=TEX
%%%%
%%%%
=SML

val ⦏buffon_needle_thm⦎ = save_thm ( "buffon_needle_thm", (
set_goal([], ⌜
	let	S = {(θ, d) | θ ∈ ClosedInterval (ℕℝ 0) π ∧ d ∈ ClosedInterval (ℕℝ 0) (ℕℝ 1)}
	in let	x_axis = {(x, y) | y = ℕℝ 0}
	in let	needle(θ, d) =
		{(x, y) | ∃t⦁ t ∈ ClosedInterval (ℕℝ 0) (ℕℝ 1)
			∧ x = t * Cos θ ∧ y = d - t * Sin θ}
	in let	X = {(θ, d) | (θ, d) ∈ S ∧ ¬needle(θ, d) ∩ x_axis = {}}
	in	X ⊆ S
	∧	∃x s⦁	¬s = ℕℝ 0
		∧ 	X Area x
		∧	S Area s
		∧	x / s = ℕℝ 2 / π 
⌝);
a(rewrite_tac[let_def] THEN REPEAT strip_tac
	THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜ℕℝ 0 < π⌝ THEN1 rewrite_tac[π_def]);
a(lemma_tac⌜ℕℝ 0 ≤ π ∧ ¬π = ℕℝ 0⌝ THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a(LEMMA_T⌜ℕℝ 0 ≤ ℕℝ 1⌝ asm_tac THEN1 rewrite_tac[]);
a(LEMMA_T⌜{(x, y)|x ∈ ClosedInterval (ℕℝ 0) π ∧ y ∈ ClosedInterval (ℕℝ 0) (ℕℝ 1)}
             Area π * ℕℝ 1⌝ ante_tac
	THEN1 all_fc_tac[area_rectangle_thm]);
a(rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜ℕℝ 2⌝ THEN ∃_tac⌜π⌝ THEN asm_rewrite_tac[]);
a(accept_tac(rewrite_rule[let_def] buffon_needle_lemma));
pop_thm()
));

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
output_theory{out_file="wrk066.th.doc", theory="-"};
=TEX
The intention is that theorems should always have an outer universal quantifier if necessary rather than free variables
and that all variables bound by logical quantifiers should
actually be used.
The following code reports on theorems that fail to comply.
=SML
fun ⦏unused_qvs⦎ (tm : TERM) : TERM list = (
	let	fun drop_fst (t :: ts) v = (
			if	t =$ v
			then	ts
			else	t :: drop_fst ts v
		) | drop_fst [] _ = [];
		fun dest_quant t = (
			let	val (vs, b) = dest_∀ t
				handle Fail _ => dest_∃ t
				handle Fail _ => dest_∃⋎1 t;
			in	(frees vs, b)
			end
		);
		fun aux (acc, tm) = (
			(dest_var tm; drop_fst acc tm)
		handle Fail _ => 
			(dest_const tm; acc)
		handle Fail _ =>
			(aux (dest_quant tm))
		handle Fail _ =>
			(aux (acc, snd(dest_simple_λ tm)))
		handle Fail _ =>
			let 	val (f, x) = dest_app tm;
			in	aux (aux(acc, f), x)
			end
		);
	in	aux ([], tm)
	end
);
fun ⦏thm_unused_qvs⦎ (thm : THM) : TERM list = (
	let	val tuple = fold mk_pair (asms thm) (concl thm);
	in	unused_qvs tuple
	end
);
fun check_thms () = (
	let	val thms = get_thms "-";
		val fv_bad_thms = thms drop (is_nil o thm_frees o snd);
		val bv_bad_thms = thms drop (is_nil o thm_unused_qvs o snd);
		fun aux (ns, _) = (
			output(ExtendedIO.std_err,
				translate_for_output (hd ns));
			output(ExtendedIO.std_err, "\n")
		);
	in	(case fv_bad_thms of
			[] => ()
		|	_ => (
			output(ExtendedIO.std_err,
		"**** The following theorems have one or more free variables:\n");
			app aux fv_bad_thms
		));
		(case bv_bad_thms of
			[] => ()
		|	_ => (
			output(ExtendedIO.std_err,
		"**** The following theorems have one or more unused quantified variables:\n");
			app aux bv_bad_thms
		));
		(case (fv_bad_thms, bv_bad_thms) of
			([], []) => (
			output(ExtendedIO.std_err,
		"**** Theorem quality control checks all passed\n")
		) |	_ => ())
	end
);
val _ = check_thms();
=TEX
\end{document}
=IGN

