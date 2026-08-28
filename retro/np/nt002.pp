=IGN
nt002.pp

Greek Letters
	Γ Δ Θ Λ Ξ Π Σ Υ Φ Ψ Ω
	α β γ δ ε ζ η θ ι κ λ μ ν ξ π ρ σ τ υ φ χ ψ ω
Logic: 	∧ ∨ ¬ ∀ ∃ ⦁ × ≤ ≠ ≥ ∈ ∉ ⇔ ⇒
Set symbols: 𝔹 ℂ 𝔽 ℕ ℙ ℚ ℝ 𝕊 𝕌 ℤ ⊆ ∅ ⊂ ∩ ⋂ ∪ ⋃ ⊖
Arrows: → ⤖ ⤕ ⇻ ↔ ⤀ ⇸ ↣ ↦ ↠ ⤔
Formal Text Brackets: ⌜ ⌝ ⓣ ⓜ ⓩ Ⓢ ■ ┌ └ ╒ ├
Padding symbols	│ ─ ═  Index Brackets ⦏ ⦎
Bracketing symbols: ⟨ ⟩ ⟦ ⟧ ⦇ ⦈
Subscription and Superscription: ⋎ ⋏ ↗ ↘ ↕ Underlining: ⨽ ⨼
Relation, Sequence and Bag Symbols:  ⩥ ▷ ⩤ ◁ ⁀ ↾ ↿ ⊕ ⊎ ⨾ ∘
Miscellaneous: ⊢ ⦂ ≜ ⊥ ⊖

set_flag("pp_show_HOL_types", true);

=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}

%\def\ExpName{\mbox{{\sf exp}
%\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Recursion and WellOrderings}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
I put a toe in the water here on reworking certain topics prerequisite to
support for inductive data types (as I imagine it)
for use in the first instance in the metatheory of HOL.
However, after beginning I decided that it would be more helpful in the first instance
to keep with the existing treatement of well-orderings and the recursion theorem,
and go straight to investigation of inductive datatypes, which I will do in nt003.
There is here at the moment just the constructive definition of well-foundedness
and the very first steps in proof of a  recursion theorem,
which will remain cut off for the time being.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2025/06/10

Last Change 2025/07/14

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}

\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
{\parskip=0pt\tableofcontents}
%\newpage
%\subsection{Document cross references}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage

\section{INTRODUCTION}

In the first instance this document will hang on `misc3',
later the dependencies will be pruned, with a view to establishing
the simplest basis for the metatheory of HOL and its use in defining
a reflexive logical kernel.

=SML
open_theory "misc3";
force_new_theory "⦏nt002⦎";
force_new_pc "⦏'nt002⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'nt002";
set_merge_pcs ["misc11", "'GSU", "'misc3","'nt002"];
=TEX

\section{The Recursion Theorem}

=SML
declare_infix(230, "⦏<<⦎");
declare_infix(230, "⦏~~⦎");
=TEX

ⓈHOLCONST
│ ⦏hereditary⦎: ('a → 'a → BOOL) → ('a → BOOL) → BOOL
├─────────
│ ∀$<< p⦁ hereditary $<< p ⇔ ∀x⦁ (∀y⦁ y << x ⇒ p y) ⇒ p x
■

ⓈHOLCONST
│ ⦏inductive⦎: ('a → 'a → BOOL) → 'a → BOOL
├─────────
│ ∀$<< x⦁ inductive $<< x ⇔ ∀p⦁ hereditary $<< p ⇒ p x
■

ⓈHOLCONST
│ ⦏Well_founded⦎: ('a → 'a → BOOL) → BOOL
├─────────
│ ∀r⦁ Well_founded r ⇔ ∀x⦁ inductive r x
■

ⓈHOLCONST
│ $⦏~~⦎: ('a → 'b) → ('a → 'b) → ('a → 'a → BOOL) → 'a → BOOL
├─────────
│ ∀f g $<< x⦁ (f ~~ g) x ⇔ (∀y⦁ y << x ⇒ f y = g y) ∧ f x = g x 
■

ⓈHOLCONST
│ $⦏pfixp⦎: (('a → 'b) → ('a → 'b)) → ('a → 'a → BOOL) → ('a → 'b) → 'a  → BOOL
├─────────
│ ∀G $<< f x⦁ ((G f) ~~ f) x  
■

ⓈHOLCONST
│ $⦏upfixp⦎: (('a → 'b) → ('a → 'b)) → ('a → 'a → BOOL) → ('a → 'b) → 'a  → BOOL
├─────────
│ ∀G $<< f x = pfixp G $<< f x 
■

=SML
set_goal([], ⌜∀Fn r$<<⦁ Well_founded $<< ∧ (∀x f g⦁ (∀y⦁ y << x ⇒ f y = g y) ⇒ Fn f x = Fn g x)
	      ⇒ ∃⋎1 h⦁ h = Fn h⌝);
a (rewrite_tac [get_spec ⌜Well_founded⌝,get_spec ⌜inductive⌝]);
a (REPEAT strip_tac);
a (lemma_tac ⌜heriditary $<< (λx⦁ ∃⋎1 y⦁ ∃f⦁
  		      (∀z⦁ z << x ⇒ f z = Fn f z)
		    ∧ Fn f x = y
  		    ∧ (∀g⦁ (∀z⦁ z << x ⇒ g z = Fn g z) ⇒ Fn g z = y))
		    ⌝);
a (lemma_tac ⌜∀x⦁ ∃⋎1 y⦁ ∃f⦁
  		      Fn f x = y
  		    ∧ (∀z⦁ z << x ⇒ f z = Fn f z)
		    ∧ (∀g⦁ (∀z⦁ z << x ⇒ g z = f z) ⇒ Fn g z = y)
		    ⌝);
set_labelled_goal "2";
a (asm_fc_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜λx⦁ ∃⋎1 y⦁ ∃f⦁
  		      Fn f x = y
  		    ∧ (∀z⦁ z << x ⇒ f z = Fn f z)
		    ∧ (∀g⦁ (∀z⦁ z << x ⇒ g z = f z) ⇒ Fn g z = y)
		    ⌝);
(* *** Goal "1.1" *** *)
		    
   
a (swap_nth_asm_concl_tac 1 THEN rewrite_tac[]);

stop;
=TEX

\ignore{
\section{HOL TYPES AND TERM}

We use the urelments in GSU as names of type and term variables and constants.
The method here is to define the constructors as operations over sets, and to take the smallest set which is closed under the constructions.

\subsection{Types}

 ⓈHOLCONST
│ ⦏Mk_Tvar⦎ : 'a GSU → 'a GSU
 ├───────────
│ ∀n⦁ MkTvar n = Nat⋎u 0 ↦⋎u n
 ■
 
 ⓈHOLCONST
│ ⦏Mk_Tcon⦎ : 'a GSU → 'a GSU LIST → 'a GSU
 ├───────────
│ ∀n l⦁ MkTcon n l = Nat⋎u 1 ↦⋎u SeqCons⋎u n (SeqDisp⋎u l)
 ■

=GFT
=TEX


=IGN
set_flag("subgoal_package_quiet", true);


set_goal([], ⌜∀f s x⦁ x ∈⋎u s ⇒ f x ∈ FunImage⋎u f s⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜FunImage⋎u⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val funimage⋎u_fc_lemma = save_pop_thm "funimage⋎u_fc_lemma";

set_merge_pcs ["misc3", "'nt002"];
=TEX
}%ignore


=SML
add_pc_thms "'nt002" [];
commit_pc "'nt002";

force_new_pc "⦏nt002⦎";
merge_pcs ["misc3", "'nt002"] "nt002";
commit_pc "nt002";

set_flag("subgoal_package_quiet", false);
=TEX




{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{misc3.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
