# Deductive Knowledge Subsystem Meta-Task

## Introduction

This meta-task covers the deductive knowledge subsystem within the SPaDE project.

Its primary role is to implement the primitive inference rules of the SPaDE HOL logical institution.
This is similar to the deductive system for ProofPower HOL documented in spc001-5.
However, the structure of SPaDE theorems is complicated by the very different way in which SPaDE ensures integrity of proof, involving a heirarchy of trust and the use of digital signatures to place theorems within that heirarchy.

The deductive kernel will provide support for efficient evaluation of functions in HOL and possibly other languages, and will implement a reflexive rule which admits functions proven to be logically sound as inference rules.

It is also responsible for establishing structural paradigm for proofs which is amenable to the kinds of capabilities to be implemented in the deductive intelligence subsystem (alpha-zero stlye RL optimised MCTS).