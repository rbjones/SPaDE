# The SPaDE Deductive Kernel

## Introduction

This is a first sketch of the deductive kernel for SPaDE.
The deductive kernel is so called because its role is broadly similar to that of the kernel of an interactive theorem prover, contributing to the integrity of the deductive system, though the approach to that end is quite different.

The following kinds of functionality are assigned by the architecture to this component of SPaDE.

- [The Calculus of Authority Levels](#the-calculus-of-authority-levels)
- [The Structure of Theorems in SPaDE](#the-structure-of-theorems-in-spade).
- [Implementation of primitive inference rules](#implementation-of-primitive-inference-rules).
- [Support for the hierarchy of authorities for endorsing theorems](#support-for-the-hierarchy-of-authorities-for-endorsing-theorems).

## The Calculus of Authority Levels

Rather than adopting the classic LCF architecture in which authority to create theorems rests exclusively with the logical kernel, and is reserved by the kernel to sentences which have been rigorously derived from axioms via primitive inference rules, SPaDE allows multiple authorities to endorse theorems, and gives to users a view of the repository filtered by the level of authority they choose to trust.

Since the derivation of a theorem may depend on contributions from multiple authorities, or a theorem may have been independently endorsed by several authorities, the level of authority associated with a theorem will in general be an expression former from the authority levels which have contributed to its derivation.

When a theorem is deduced from one or more premises, the resulting level of authority will be the conjunction of the contributing levels.
When a theorem is independently endorsed by multiple authorities, the resulting level of authority will be the disjunction of the contributing levels.

The complexity which would otherwise arise is mitigated by the use of endorsements, in which one authority asserts trust for another.
This means that a set of authorities can be accepted by defining a single authority which endorses all the authorities to be trusted and citing that authority level.
This creates from an otherwise flat array of authorities, a hierarchy in which trust can be managed more efficiently.

Semantically, when a theorem is certified by an authority qualified by an authority level, the assertion is that the theorem is alleged to be true provided that the qualifying authority level has been hitherto infallible.
The "hitherto" is essential to avoid circularity in the semantics, but does not depend on date stamping but depends upon the use of sequence number on theorems such that the sequence number allocated to any theorem is a strict supremum of the sequence numbers of theorems upon which the derivation depends.

## The Structure of Theorems in SPaDE

In SPaDE a theorem is a term which has been authenticated as true in a particular logical context by an authority which has digitally signed it.

The content of the package signed is as follows:

- The theorem itself, a boolean-valued term in SPaDE HOL.
- The logical context in which the term is derivable, as:
  - the location of the local repository defining that context
  - path in that repo of the context, and
  - the checksum of the context.
- An expression giving the level of authority relied upon in deriving the theorem.

## Implementation of Primitive Inference Rules

In an LCF system, the kernel implements an abstract data type of theorems monopolising the ways in which values of that type can be created and ensuring that any computation of a valur of type theorem perfectly shadows (without exhibiting or preserving) a formal proof in the underlying logic.
This makes it safe for users to program advanced theorem proving algorithms without any risk of compromising the integrity of proof checking.

In SPaDE the kernel supports primitive inference rules and more complex derived inference rules in a different way, making use of digital signatures to allow a user to select a level of authentication appropriate to his application, and to make use an open ended variety of software and/or hardware support in the application of deductive methods.

## Support for the Hierarchy of Authorities for Endorsing Theorems

SPaDE enables the use of any authority to undertake and endorse deductive reasoning, requiring such an authority to digitally sign the theorems it endorses and enabling users to select, using a heirarchy of authorities, the level of authentication they require for the theorems they use in their applications.

These same mechanisms also enable real-world interaction, effecting actions in the world and obtaining assurance of their completion in a way intended to dovetail with the use of smart contracts on blockchains, maximising the assurance that real world contracts will achieve their intended effects.

## The Subsumption of Computation within Deduction

It is normal even in the most rigorous mathematical deductive proofs, to incorporate calculations where needed without any detailed reduction to primitive rules.
In default of any provision for using the available computational machinery for such routine calculations, formal proofs are substantially less efficient than mere calculation.

Insofar as the rigour of reduction of computation to foundational levels may be intended to improve confidence the the derivations to which it contributes, it is doubtful that any improvement in confidence is warranted by the costs involved.
In any case, the normal LCF paradigm depends upon the correctness of the compilers used to compile the kernel, and the hardware on which it runs, for the overall soundness of the system.

Compilers can be verified, and flawed results due to hardware malfunctions are almost unknown, it is more likely to result in complete failure of the the system with no false conclusions.

It is the intention of the SPaDE architecture that efficient computation be fully embraced, so that normal work can efficiently be conducted within a comprehensive deductive framework.
The mechanisms for this are largely independent of kernel support, I describe here the features of the SPaDE deductive kernel which may be involved, and how the desired effects are obtained.

This is addressed in the following ways:

- [Provision for efficient evaluation of HOL expressions](#provision-for-efficient-evaluation-of-hol-expressions)
- [Provision for meta-theoretic reflection](#provision-for-meta-theoretic-reflection)

### Provision for Efficient Evaluation of HOL Expressions

The first part of this is the provisions in the kernel for efficient evaluation of HOL expressions.
The details of this are given in the subsequent sections.

### Provision for Meta-Theoretic Reflection

The second part is the axiom of meta-theoretic reflection (not necessarily under that name).
This asserts that if I have function over HOL terms which is logically sound, i.e. which maps terms to terms which are logically derivable from them (in any context), then the result of applying that function to the term is also a theorem.
That is to say, that on proving that a function is a derived inference rule of the logic, then it can be used in proofs without reference to its internal computational details.

A first element of this is the incorporation of the reflexive axiom in the logical system.
This asserts that any term is logically derivable from itself, providing a foundation for reasoning about the results of computations within the deductive framework.
Furthermore, the computation involved in performing that derived inference can be efficiently conducted using the provisions for efficient evaluation of HOL expressions.

### Provision for Abstract Machine Evaluation

The first motivation for this is to enable the use of whatever hardware may be made available for efficient computation within the deductive framework.
This involves defining an abstract machine model in the SPaDE repository using a function which is defined to capture precisely the function computed by that hardware on any `program' submitted to it.

The abstract machine defined could be the machine code of the underlying hardware, or it could be a higher-level intermediate representation that is more convenient for reasoning within the deductive framework.
In either case, a proof agent is created which is designated to handle expressions in that notation, and which will either execute them on the designated hardware, or preprocess (compile) them into a form suitable for execution on the hardware, and will return a result as a theorem which asserts the value resulting from that particular computation.
This agent has its own signature, and by this means users of SPaDE (or their agents) can decide whether to trust this particular abstract machine and its associated hardware.

The role of the deductive kernel in this process is merely to provide support for the calculus of authority which permits arbitrary agents to be trusted (at the users discretion)based on their signatures and the theorems they produce, without needing to verify the internal workings of the abstract machine or the underlying hardware.

## The Efficient Evaluation of HOL Expressions

The details of how this is to work have not been considered in any detail, but I would envisage it happening at either or both two levels.

## Support for an Evaluative Proof Paradigm

The logical system is defined inductively as the closure of a set of axioms under a set of primitive inference rules.
The naive way of establishing that a term is a theorem is to show how it can be derived from the axioms using the primitive inference rules by beginning with axioms and applying rules until the desired term is obtained.

This proof method was known in antiquity and was called synthetic proof.
It was contrasted with analytic proof, in which the proof proceeds from the desired conclusion backwards, seeking premises from which the result or intermediate theorems can be derived until the premises required are all axioms.

In modern times, these are described, perhaps more perspicuously, as forward and backward proof search, corresponding to synthetic and analytic proof respectively.

Backward proof is generally easier for humans seeking proofs, but it also provides a more efficient proof search method for automated systems (than naively reasoning forward from the axioms hoping to find your result, the British Museum Algorithm!).
More important that that rather modest claim, in the context of *deductive engineering* we natually begin with some conception of what we want to engineer and work backwards to establish an architecture and the resulting requirements on the components, and so on.
(for further discussion of this line of thought see [Deductive Engineering](./tlad007.md))

This advocacy of backward reasoning is to note that backward reasoning can be effectively realised in an evaluative proof paradigm.
What I mean by that is, proof by rewriting the goal until it is shown to have the value "T" (true).
This conceptually backward proof method can be accomplished entirely by rewriting (which is a forward operation) by starting with the tautology "G=G" where G is the desired goal, and progressive

