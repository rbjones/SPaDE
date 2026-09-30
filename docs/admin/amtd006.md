# Task: a generic theory of abstract syntax

## Purpose

The first specification written for SPaDE is a generic theory of abstract syntax. It is used for the HOL terms in the specification of HOL. Later it is used when onboarding knowledge or data expressed in some other language, such as Lean: the semantics of that notation are rendered in HOL, and the syntax is this generic one.

`spc001.pp`–`spc005.pp` are reference for that work. None of them survives intact. The deductive system remains the same. The way it is expressed is more constructive, explicit, and executable (in particular the representation of inference rules as relations is to be replaced by functions, the partial nature is captured by returning "T" whenever the inference would otherwise fail). The inference rules are written so that SPaDE can prove a derived rule sound and then run it. Those derived rules are the earliest reflective self-improvement.

## What a specification does when it creates a theory

Every formal specification in HOL begins the theory it is creating with `force_delete_theory`. That operation does not fail when the theory is absent. `new_theory` then succeeds whether or not a previous check left the theory in the database. With the dependencies maintained, a change to one specification causes the makefile to re-check that specification and the specifications that depend on it.

The new theory does not take the name of an `spc` theory, and it does not take the name of the document. The name is an intelligible name for the theory.

A document derived from a ProofPower source, or from [krdd004.md](../../kr/krdd004.md), acknowledges that source. ProofPower checks well-formedness. Correctness is a further, more intelligent check.

## First stage

The generic abstract syntax starts from the packing and unpacking of null-terminated byte sequences in [Encoding and Decoding NTBS and Related Data Types](../../kr/krdd004.md#encoding-and-decoding-ntbs-and-related-data-types). That account replaces the coding method in `spc001` in a way that is less sensitive to features of the language.

A constructor of the language takes strings as arguments. Each string is converted to an NTBS. Those NTBS are concatenated. A code is added (as an NTBS) at the front to identify the construction and then the NTBS sequence is concatenated to yield a byte (char) sequence (STRING) which is the representation of the constructed phrase (TYPE, TERM or larger structure in the SPaDE repository). That code may be the name of the constructor (e.g. "Mk_app").

The result is a SPaDE specification in markdown, with the HOL in `hol` fences, stripped to `.sml` by `docs/tlci001.mkf`. It is part of SPaDE. The `spc` documents and `retro/` remain reference and bootstrap.

## Later, and not this stage

The specification of HOL is built on this abstract syntax. Architectural material in `kr/` is input. The likely outcome is a new specification in `docs/` which supersedes it. Specifications in `kr/` written for HOL4 are not the form of the new architectural HOL.

Subsequent task description will address various other ways in which SPaDE will differ from ProofPower, in advancing to a  full specification of the SPaDE repository, and the primitive HOL inference rules.

---

Document ID: amtd006
Author: Grok Build (Grok 4.7)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
