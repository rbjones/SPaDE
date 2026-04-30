# Deduction in SPaDE

The SPaDE project involves and depends upon new ideas in relation to deduction.
Talking about those ideas demands some new terminology, and it is the purpose of this document to introduce that terminology and to explain the ideas behind it.

It is in effect an part of the [SPaDE glossary](./tlad001.md) covering the following expressions:

- [deduction](#deduction)
- [declarative language](#declarative-language)
- [formal deduction](#formal-deduction)
- [deductive paradigm](#deductive-paradigm)
- [deductive engineering](#deductive-engineering)
- [deductive intelligence](#deductive-intelligence)
- [reflexion and singularity](#reflexion-and-singularity)

## Deduction

Deduction is a kind of reasoning in which, from a group of premises one or more conclusions may be inferred.
Such inferences are considered deductive if the methods used to obtain the conclusions are such that, if the premises are true, then so will be the conclusions.
Implicit in that account is that deduction operates upon things which carry truth values, which may or may not be true.
In making that precondition clear, the concept of declarative language is invoked.

## Declarative Language

Declarative language is that kind of language in which information or knowledge may be expressed by asserting expressions (generally known as sentences) which carry truth values, and express relationships in some subject matter between entities referred to be other kinds of expression in the language.
In order to be a properly declarative language, the expressions in the language must be given meaning, either as designating things within the subject domain or as expressing relationships between such things.
The designations are determined by the semantics of the language (which defines the meanings) in terms of the state of the domain of discourse so that the truth value of the sentences will depend on the state of the domain.
Each sentence will therefore be true in some subset (usually proper) of the possible states of the domain, and its assertion as true will in that way convey information about how the world is; that the world is such as to render the sentence true under the semantics of the language.

## Entailment

Entailment is a relationship between sentences in a declarative language, such that one sentence (the conclusion) is entailed by another sentence or group of sentences (the premises) if the subset of possible states of the domain in which the conclusion is true is a superset of the subset of possible states in which the premises are true.
In that case, the truth of the conclusion is guaranteed by the truth of the premises, and the conclusion is said to be entailed by the premises.

The notion of "possible state" above should not be understood as a reference to some notion of logical possibiity, since that might cause circularity in accounts of logical necessity.
It is rather, accepting that languages are conventions for communication, and that a semantics for some language is part of the definition of the conventional meaning of that language, and the description of the subject matter, including the possible states of that subject matter, is a part of defining those conventions.

## Formal Deduction

Formal deduction is a reliable method for determining broad logical or analytic truth in formal declarative languages.
It is usually defined for any particular language as the closure of a decidable set of axioms and definitions under a decidable set of inference rules.
This yields a semi-decidable subset of the truths in the language.
Truth in foundational institutions is not semi-decidable, so formal deduction is not complete, but it is rare for this to impact practical applications.

A formal proof of a theorem is a record of a sequence of inferences which derive that theorem from the axioms and definitions, and the correctness of such proofs can be reliably checked by straightforward algorithms.
One popular approach to implenting interactive theorem proving tools is known as the "LCF paradigm", since it was first undertaken for Dana Scott's Logic for Computable Functions (LCF) by a team at Edinburgh University in the 1970s.
The approach to formal deduction in SPaDE diverges substantially from that in the LCF paradigm, but can be related to some of the modern extensions to it which admit decision procedures and/or reflexion principles, and will be described partly in contrast with the simplistic account of formal proof and its treatment in derivatives of the LCF paradigm.

## Deductive Paradigm

The term "deductive paradigm" is used in SPaDE to refer to a radical broadening in the scope of application of formal declarative knowledge and deductive reasoning which SPaDE seeks to articulate and support, both in philosophical and engineering terms.
This is though of and spoken of in SPaDE as subsuming the more familiar "computation paradigm" in which information processing is conceived as the processing of data by computing machines into a semantic context in which the meaning of the data is explicit, and hence the data read as propositions, and the effects of algorithms are then understood as performing inferences.

An important aspect of the support in SPaDE intended for the deductive paradigm is the facility to apply directly in proofs any algorithm which has been proven to deliver theorems which could have been derived using the primitive inference rules.
One effect of the features anticipated in SPaDE's support for the deductive paradigmis that the difference in computational resource required to prove that a program computes a particular result, but comparison with simply running the program and observing the result, can be eliminated, and it is this feature which encourages the claim that the deductive paradigm subsumes the computation paradigm (though qualifications are appropriate).

## Deductive Engineering

Though the deductive paradigm is more broadly scoped, embracing any context in which deductive reasoning may be of value or interest, SPaDE prioritises its application to engineering, and the application of deductive methods to the automation of engineering design is referred to in SPaDE as "deductive engineering".

The first areas of focus in deductive engineering will be software development, more specifically theorem proving software, replacing the usual heirarchy of tactics and other higher order proof methods (in LCF systems) with verified derived inference rules which are then trusted to derive results without reduction to primitive rules.

As the application domains broaden one approach to be explored is the capture of systematic design rules as derived inference rules.
Because of the need in deductive engineering to have requirements formally specified so that it can be known what an engineering artefact *does* methods for coevolution of requirements and design will be explored.

## Deductive Intelligence

Deductive intelligence is the application in SPaDE of focal methods to deduction in arbitrary logical contexts in the SPaDE knowledge repository.
In the first instance the focal methods will be derived from those in the alpha-zero system, the use of re-inforcement learning with deep neural nets for heuristics in MCTS (Monte Carlo Tree Search) for theorem proving.

Each logical context in a SPaDE repository is a distinct perfect information space within which focal intelligence can be applied to deduction.
There will therefore be potentially a separate focal specialist for each logical context.
Since the logical contexts form a hierarchy, subproblems in one context which fall wholly within the vocabulary of a smaller context can be subcontracted to the more narrowly focussed specialist associated with that smaller context.

## Reflexion and Singularity

The development of SPaDE will not only aim to provide more effective application of deductive methods by the use of focal methods, but will also look at multiple levels (in progression) for singular foci, i.e. to those features which enable the design of more advanced deductive methods, the kind of self re-invention of intelligence which gives rise to a *singularity*.

This requires that SPaDE be able to reason about its own deductive methods and capabilites, a kind of reflexion demanding in this context a *metatheory-first* development strategy for the core SPaDE knowledge repository.

The SPaDE kernel will be designed with features intended to support the application of metatheoretic reasoning on an incremental basis rather than relying on (but not excluding) more radical redesign of SPaDE.
More details of this may be found in the architecural documentation for the SPaDE kernel.

It is intended that all aspects of SPaDE, the structure of the SPaDE knowledge repository, the deductive methods, and the focal methods, will be under continuous evaluation by SPaDE itself, enabling a form of self-improvement and adaptation over time and as a prophylactic agains structural decay.
