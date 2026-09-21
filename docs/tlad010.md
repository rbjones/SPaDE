# The First Singular Focus

## Introduction

In thinking about the development trajectory and trying to identify the first "singular focus" I see multiple ways in which the system will be engaged in self-improvement but which fall short of the system redesigning itself as a whole.

This causes me to pull apart the idea of focus, of Recursive Self-Improvement (RSI) and singularity.

Before getting into that I note, that focal reasoning, by itself is not going to deliver the progression of self-improvement necessary for a singularity.
Focal reasoning depends on a theory defining a definite problem space, and is applied only when a definite problem in that space has been identified.
The direction has to be set either by a human or a non-focal AI (at this stage likely an LLM).


## Preliminary Notes

I think there are three major elements of "self-improvement" from which the first singularity might be composed.

One is the learning-by exploration in the alpha-zero methods which will be the first versions of the di subsystem.

The second is the use of the reflection principle made available by features of the deductive kernel which allow syntactic functions proven to be logically sound to be executed as derived rules.
Derived rules established by meta-theoretic reflection will replace the tactics in prior LCF systems, they are essentially tactics which are proven sound and can therefore be executed without being reduced to primitive inference steps. This first level of reflexive self improvement is HOL centric, since it hangs around the formal specification of the system in HOL, and involves derived rules specified as HOL functions (and a kernel facility allowing efficient execution of HOL functions), whereas a first implementation of SPaDE will be in python. To advance to a full capability for self-improvement would require the entire system to be written in a langauge for which we have a complete HOL metatheory, and I'm not convinced we need to go there.

Note that the correspondence between the epistemological stack and the focal tower was never intended to be one-one, I always expected there to be many singular foci of each epistemological status.

I think the first target for planning should be the limited kinds of self improvement which we get from meta-theoretic reflection yielding new derived inference rules which are efficiently executed.
This suffices for a general deductive engineering paradigm in which design methods are implemented using algorithms which have been proven to yield correct designs (used in backward proofs like tactics, by matching system requirements to subsystem structure and component requirements and hence iteratively decomposing the problem.

## Introduction

The SPaDE development strategy prioritises singular foci to maximise pace of development.
This document explains the current conception of what that first singular focus is, and how it can be progressed.

A focus in SPaDE is a perfect information space delivering some desired capability, it is singular if the capability is self-advancing, as in the hypothetical singularity occurring when an AI is able to design a more advanced AI.
Singular foci are reflexive, they involve the system understanding itself sufficiently to make improvements.
This is called Recursive Self-Improvement (RSI).

In SPaDE we see this phenomenon as occurring at multiple levels, involving progressively broader capabilities, or the achievement of a capability in progressively broader contexts (e.g. in distant star systems, rather than just on Earth).
These progressively advancing singular systems are what we call the focal tower, and the development of SPaDE is intended to progress through these different levels, leveraging singular capabilities to advance to the next level as rapidly as possible.

Getting this process off the ground is a bootstrap problem, how do we get to the point at which SPaDE deductive intelligence can work continuously exploring and gaining proficiency in the capabilities characterising the first singular focus?

## Reflection in SPaDE

Reflection is an established method for facilitating efficiency in formal reasoning.
The idea is that a logical system can reason about itself and prove derived rules of inference which are more efficient than repeated application of the primitive inference rules.
If the system is augmented by a primitive rule which allows any such proven derived rule to be used instead of reducing the inference to the primitive rules, then the system can effectively improve its reasoning efficiency through reflection.

Two essential augmentations of typical formal foundation systems are required.
The first is to enable the execution of algorithms expressed in the formal notation of the logical system, yielding a theorem stating the result of the computation.
The second is an inference rule which allows th

## The Focus

At the foundational core of SPaDE is a formal deductive system.
This consists of an abstract language with well defined syntax and semantics under which certain syntactic objects may be designated *truths*, and a recursively enumerable set of such truths defined as the closure of a (decidable)set of axiomatic truths under rules of inference which are computable truth preserving functions.
That core deductive system fixes the meanings of theis then elaborated by *conservative extension* 

SPaDE loosely descends from a tradition among interactive theorem provers which follow an architecture known as the LCF paradigm.
That architecture allows the user to program derived inference rules starting from those which define the deductive system, and to use these derived rules in proving theorems in the system.
In doing this other kinds of deduction related functions may be employed, such as tactics and tacticals, which effectively facilitate the construction of derived rules.
This kind of programming is rendered safe by the requirement that these user programmed features must ultimately achieve their effects only by successive calls to the primitive inference rules.
This means that though this kind of programming does allow reasoning capabilities to be advanced, it does not allow them to be made more efficient.

In this context reflection is logically metha-theoretic, and enables the creation of new sound inference functions.
To enable this kind of reflection, the syntax of the core logical system (HOL) admits as primitive, literal constants which are exactly the same as the terms of the logic (but are treated as mention rather than use, as in the distinction between text and quoted text).
This facilitates the construction of a meta-theory in which the
