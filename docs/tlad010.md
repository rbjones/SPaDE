# The First Singular Focus

## Introduction

The SPaDE development strategy prioritises singular foci to maximise pace of development.
This document explains the current conception of what that first singular focus is, and how it can be progressed.

A focus in SPaDE is a perfect information space delivering some desired capability, it is singular if the capability is self-advancing, as in the hypothetical singularity occurring when an AI is able to design a more advanced AI.
Singular foci are reflexive, they involve the system understanding itself sufficiently to make improvements.

In SPaDE we see this phenomenon as occurring at multiple levels, involving progressively broader capabilities, or the achievement of a capability in progressively broader contexts.
These progressively advancing singular systems are what we call the focal tower, and the development of SPaDE is intended to progress through these different levels, leveraging singular capabilities to advance to the next level as rapidly as possible.

Getting this process off the ground is a bootstrap problem, how do we get to the point at which SPaDE deductive intelligence can work continuously exploring and gaining proficiency in the capabilities characterising the first singular focus?

## The Focus

At the foundational core of SPaDE is a formal deductive system.
This consists of an abstract language with well defined syntax and semantics under which certain syntactic objects may be designated *truths*, and a recursively enumerable set of such truths defined as the closure of a set of truths under rules of inference which are computable truth preserving functions.

SPaDE loosely descends from a tradition among interactive theorem provers which follow an architecture known as the LCF paradigm.
That architecture allows the user to program derived inference rules starting from those which define the deductive system, and to use these derived rules in proving theorems in the system.
In doing this other kinds of deduction related functions may be employed, such as tactics and tacticals, which effectively facilitate the construction of derived rules.
This kind of programming is rendered safe by the requirement that these user programmed features must ultimately achieve their effects only be successive calls to the primitive inference rules.
This means that though this kind of programming does allow reasoning capabilities to be advanced, it does not allow them to be made more efficient.

In this context reflection is logically metha-theoretic, and enables the creation of new sound inference functions.
To enable this kind of reflection, the syntax of the core logical system (HOL) admits as primitive, literal constants which are exactly the same as the terms of the logic (but are treated as mention rather than use, as in the distinction between text and quoted text).
This facilitates the construction of a meta-theory in which the
