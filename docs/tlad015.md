# SPaDE Universality and Reflexion in Practice

## Introduction

This document brings together as full as possible account of the mechanisms envisaged for SPaDE supporting Recursive Self Improvement by formalised SPaDE HOL metatheory, and the aspects of SPaDE which render the universality of the HOL institution applicable in practice.

This early version is a lightweight sketch intended to give a structure and indicate which aspects of SPaDE should be incorporated into the account.

The major sections are as follows:

- [SPaDE and the LCF Paradigm](#spade-and-the-lcf-paradigm) - key departures from the LCF paradigm
- [SPaDE HOL Metatheory](#spade-hol-metatheory) - the formal specification of SPaDE HOL in itself
- [Recursive Self Improvement](#recursive-self-improvement) - the verification and application of derived rules
- [Universality By Embedding](#universality-by-embedding) - how SPaDE can represent other logical systems using deep embeddings in HOL
- [Onboarding](#onboarding) - the importation of or access to diverse knowledge sources and formalized theories
- [Strategic Aim](#strategic-aim)

## SPaDE and the LCF Paradigm

### The Pure LCF Paradigm

The pure LCF paradigm is characterized by a small trusted kernel that ensures the correctness of all derived theorems. In this paradigm, theorems are constructed using a set of primitive inference rules, and all higher-level proof procedures are built on top of this kernel. This approach guarantees that any theorem produced by the system is valid, subject to the correct execution of the kernel code.
That rests upon the correctness of the kernel code, of the compiler for the kernel, and the underlying hardware on which the system runs.

The system is written in a functional programming language known as the metalanguage which is distinct from the object logic being formalized, and suffices for the implementation of deduction in the object language but not for reasoning about the object language (or anything else).

Advantages of the pure LCF paradigm include:
- Strong correctness guarantees due to the small trusted kernel.
- Flexibility in defining new proof strategies without compromising soundness.

### SPaDE's Departures from the LCF Paradigm

SPaDE though coming from the LCF tradition, is a fundamental rethinking with the aim of closely integr

temporary list:

- multiple authorities in trust hierarchy signing theorems

- identical object and meta-language

- efficient evaluation of expressions to yield theorems giving an efficient meld of computation and deduction

- reflexive metatheory enabling functions defined over terms using the same term representation (use and mention distinguished by context)

- use of tactics replaced by execution of proven derived rules

The specific technical features supporting these are:
- A trust management system allowing multiple authorities to sign theorems.

## SPaDE HOL Metatheory

The support for Metatheory in SPaDE HOL has two distinct primary applications:

- RSI (Reflexive Self Improvement)
    This application involved enhancing SPaDE reasoning about or computation using HOL by reasoning about the syntax, i.e. the structure of terms and the rules of deduction to yield more powerful and efficient inference rules.
- Semantic Embedding
    This is for onboarding knowledge from sources which use languages other than HOL, by providing a semantic embedding of those languages into the SPaDE HOL framework. The aim here is to enable terms in HOL to express the same declarative content as those of the embedded languages, using abstract structures which correspond closely to the abstract syntax of the embedded language, and semantic mappings which faithfully capture the intended meanings of those expressions.
    Once the expressions of the target are given their correct meaning, reasoning about them can be supported and rendered efficient by the same RSI mechanisms as are exploited in HOL.

    The genericism thus obtained is not a purely syntactic matter, and all reasoning is ultimately taking place in HOL using primitive or proven derived rules.

- HOL Terms are represented by T-expressions, literal constants are T-expressions, but there is a crucial difference between a T-expression term representation which is *used* in a term (e.g. as a function or argument in an application) and a T-expression which is included as a literal constant, which is understood as a *mention* of the term rather than a use.
Use of a term and mention of the term refer to exactly the same representation but are distinguished by the context in which they appear, enabling reasoning about soundness of deductions to avoid translation between use and mention.
- Efficient evaluation mechanisms for expressions which yields theorems directly, integrating computation with deduction. This can be done for multiple embedded languages including those implemented by special hardware such as GPUs or FPGAs.
- A reflexive metatheory that allows functions to be defined over terms using the same term representation.
- A rule-based execution model where tactics are replaced by the application of proven derived rules.

## Onboarding

- T-expressions provide a generic representation for abstract syntax.  For reflexion (proving derived rules) this enables reasoning about the deductive system.  For onboarding, it supports deep semantic embeddings, and hence language specific semantic turnstiles which assert truth of expressions within the embedded language.  Establishing those truths initially involves reasoning in HOL about the semantics, but the use of the reflexion mechanisms then allows the inference rules to be proven and applied efficiently without repeated meta-level reasoning, as well as derived rules for the embedded languages.

Access to Diverse Repositories

Any form of declarative knowledge can be accessed by variants of the knowledge repository system which interpret the language or data appropriately, subject to stability (versioned sources or access to snapshots only).

## Strategic Aim

An underlying thesis is that all declarative knowledge can be formalised, and represented in SPaDE.

A second important thesis is that *foundations* are important, both for ensuring logical integrity and for enabling efficient representation and exploitation of delarative knowledge.

The aim is to enable that to be done, and to promote the long term curation of a diasporic repository of formalised declarative knowledge.
This would continually grow and be subject to structural optimisation, as well as the building of focal intelligence heuristics for each logical context in the repository.
This is indended in the early stages to be a formal modelling service for use by LLMs, but its continuous and carefully created growth is intended to support an approach to AI which learns continuously, does not ingest uncurated knowledge blindly, and can reason reliably about the knowledge it has acquired.
