# Task Description: Prepare the SPaDEroot Theory

## Introduction

The task is to write ProofPower HOL specifications to define the SPaDEroot theory.

The details of why we need this theory, the role it will play and the content of the theory are provided in a first draft of the specification document [The SPaDEroot Theory](tlcd002.md).

This theory is an exception to the general pattern of giving the same name to a theory as the document that specifies it.

The definition of the task is effectively split between the text in the draft specification and the standard procedure for creating a new theory in ProofPower HOL (ampd )

## ATTIK


For that reason, the first five tasks correspond to the five ProofPower documents in the spc001.pp–spc005.pp sequence, which will be recast as a series of specifications specific to SPaDE written in ProofPower HOL (SML) embedded in github markdown.

It is envisaged that the one formal specification document commissioned by this task description will be produced in stages, since these are the first formal specifications to be assigned to autonomous agents in the SPaDE development and it is not yet clear what agents will have the necessary skills, or what needs to be supplied to the agent to facilitate the work.
It is also likely that the full detail in this task description will also appear in stages as the specification evolves.

## Stages

Initially it is proposed that the work be conducted in the following stages:

- Overview and Background
- The Theory of T-expressions
- The Representation of Abstract Syntax in T-expressions
- The Structure of Types and Terms
- Logical Contexts
- The Structure of SPaDE repositories

Each stage will be prescribed in a separate section below, but the commissioning of work need not wait on the completion of all the sections.
It is likely that the first two sections will be commissioned before the detailed requirements for the later sections are fully specified.

The first stage in the production of this specification is the formulation of a generic theory of abstract syntax. It is used for the HOL terms in the specification of HOL. Later it is used when onboarding knowledge or data expressed in some other language, such as Lean: the semantics of that notation are rendered in HOL, and the syntax is this generic one.

`spc001.pp`–`spc005.pp` are reference for that work. None of them survives intact. The deductive system remains the same. The way it is expressed is more constructive, explicit, and executable (in particular the representation of inference rules as relations is to be replaced by functions, the partial nature is captured by returning "T" whenever the inference would otherwise fail). The inference rules are written so that SPaDE can prove a derived rule sound and then run it. Those derived rules are the earliest reflective self-improvement.

## What a specification does when it creates a theory

Every formal specification in HOL begins the theory it is creating with `force_delete_theory`. That operation does not fail when the theory is absent. `new_theory` then succeeds whether or not a previous check left the theory in the database. With the dependencies maintained, a change to one specification causes the makefile to re-check that specification and the specifications that depend on it.

The new theory does not take the name of an `spc` theory, and it does not take the name of the document. The name is an intelligible name for the theory.

A document derived from a ProofPower source, or from [krdd004.md](../../kr/krdd004.md), acknowledges that source. ProofPower checks well-formedness. Correctness is a further, more intelligent check.

## First stage

The generic abstract syntax starts from the packing and unpacking of null-terminated byte sequences in [Encoding and Decoding NTBS and Related Data Types](../../kr/krdd004.md#encoding-and-decoding-ntbs-and-related-data-types). That account replaces the coding method in `spc001` in a way that is less sensitive to features of the language.

A constructor of the language takes strings as arguments. Each string is converted to an NTBS. Those NTBS are concatenated. A code is added (as an NTBS) at the front to identify the construction and then the NTBS sequence is concatenated to yield a byte (char) sequence (STRING) which is the representation of the constructed phrase (TYPE, TERM or larger structure in the SPaDE repository). That code may be the name of the constructor (e.g. "Mk_app").

The result is a SPaDE specification in markdown, with the HOL in `hol` fences, stripped to `.sml` by `docs/tlci001.mkf`. It is part of SPaDE. The `spc` documents and `retro/` remain reference and bootstrap.

## Task execution

This task is undertaken on branch `am`, in its `SPaDE-am` worktree. A local worker receives that worktree alone, mounted for the task as specified in [ampd010.md](ampd010.md). It may read the sources named in the architect role card and change only the formal target and its directly related build entries.

The worker must run the stated document-generation and ProofPower validation commands before proposing completion. Those commands are to be made reproducible in this worktree before the task is assigned autonomously; the existing document makefile strips `hol` fences but is not yet a ProofPower runner for a new architectural script. The worker does not merge its result.

## Later, and not this stage

The specification of HOL is built on this abstract syntax. Architectural material in `kr/` is input. The likely outcome is a new specification in `docs/` which supersedes it. Specifications in `kr/` written for HOL4 are not the form of the new architectural HOL.

Subsequent task description will address various other ways in which SPaDE will differ from ProofPower, in advancing to a  full specification of the SPaDE repository, and the primitive HOL inference rules.

---

Document ID: tltd002
Author: Grok Build (Grok 4.7) and Roger Jones
Status: In progress
Chat log: [amcl003.md](amcl003.md)
