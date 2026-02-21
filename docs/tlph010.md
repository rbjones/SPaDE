# Universal Foundational Institutions

The thesis, that Higher Order Logic suitably construed is universal for the representation of declarative knowledge, is meaningless without an account of the terminology involved.
The purpose of this document is to provide that account.

## Some Context

The status quo terminologically is confused by the number of academic disciplines concerned with language and logic, which chose terminology conducive to theoretical development within those disciplines, but not closely aligned with the purposes of this work, or even with the motivations of the pioneers of modern logic.

It may be worth touching upon some of the seminal work concerned with the emergence of modern logic.
The main factor in the development of logic in the 19th century was the engagement of mathematics with logic, which seems to have had two principal stimuli.
One was probably just that mathematics became less exclusively focussed on number and geometry, and more open to diverse forms of mathematical structure.
From this point of view, the algebraic treatment of proposition logic by Boole and De Morgan was a natural development.

The second stimulus was the perceived need for a return to rigor in mathematical analysis, which under the impetus of its applications in science and engineering had mushroomed despite a lack of clarity about its fundamental concepts, notably the real number system and the concept of function, both of which were ontologically novel and opaque.
This thread was pursued most effectively by Cauchy, Weierstrass, Dedekind and Cantor, leading to the arithmetisation of analysis and the formal definition of real numbers in terms of Dedekind cuts or Cauchy sequences of rationals.

A third notable stimulus was philosophical.
In the eighteenth century a divergence appeared between David Hume, and the central place in this philosophy of his division of knowledge into "relations of ideas" and "matters of fact", and Immanuel Kant, who argued that synthetic a priori knowledge was possible, and that mathematics was the prime example of such knowledge.
For Hume, mathematics belonged to the realm of "relations of ideas", and hence to logic, from which Kant demurred.

In a context in which mathematics had been progressing a profound foundational re-construction, Gottlob Frege set out to refute Kant by showing that mathematics could be reduced to logic.
The conception of *logic* which he tabled for that purpose was *Begriffsschrift*, concept notation.

## Foundational Institutions

*[This originally followed on from the writing before the section on Context, and some reconsideration will be necessary when the context is completed.]*

Ideally this might have been done by refinement of and existing conception of institutions, but I have found no conception of institution which meets the requirement.

This document therefore begins by articulating the purpose in hand, so that further consideration can then be given to how the technical details can be filled in.

## Purpose

The first informal idea which the notion of foundational institution is intended to capture is that some logical foundation systems are universal for the representation of declarative knowledge.
By that is meant, that they provide a language into which all other declarative languages can be semantically embedded.
A *semantic embedding* is a mapping from one language to another which preserves meaning.

To progress this idea, we will define the following concepts:

- declarative language
- logical foundation system
- foundational institution
- foundational embedding

### Declarative Language

A declarative language is one in which constraints on the possible state of some domain of discourse can be expressed, using sentences having truth values which are determined by the state of that domain, the assertion of which limit the possibilities to those satisfying the truth conditions.

In order to talk about whether mappings between declarative languages preserve meaning, we need to say something about the semantics of those languages.  For meaning to be fully preserved, we need to consider not only the truth conditions of sentences but also the value of expressions within the languages.  Semantics is not just assigning values to sentences, but also to the members of all other syntactic categories of the language.

We must therefore go into more detail about semantics, which begins with *abstract syntax*.

#### Abstract Syntax

The abstract syntax of a declarative language is a set of syntactic categories, and a collection of rules for forming objects in these categories from members of other syntactic categories.
